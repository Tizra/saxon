; Copyright © March 2009, Perry Trolard, Washington University in Saint Louis
; 
; The use and distribution terms for this software are covered by the MIT 
; Licence (http://opensource.org/licenses/mit-license.php), which can be found 
; in the file MIT.txt at the root of this distribution. Use of the software 
; counts as agreeing to be bound by the terms of this license. You must not 
; remove this notice from this software.

(ns saxon
  "Clojure Saxon wrapper"
  (:gen-class :prefix "")
  (:use [clojure.java.io  :only (file)]
        [clojure.string   :only (join upper-case lower-case)])
  (:import
    java.net.URL
    net.sf.saxon.lib.FeatureKeys
    (java.io File InputStream OutputStream Reader StringReader Writer)
    (javax.xml.transform.stream StreamSource)
    (javax.xml.transform Source)
    (net.sf.saxon.s9api Axis Destination Processor Serializer
                        Serializer$Property XPathCompiler XPathSelector
                        XdmDestination XdmValue XdmItem XdmNode XdmNodeKind
                        XdmAtomicValue XQueryCompiler XQueryEvaluator QName
                        ExtensionFunction SequenceType ItemType
                        OccurrenceIndicator)
    org.apache.xml.resolver.CatalogManager
    org.apache.xml.resolver.tools.CatalogResolver
    (net.sf.saxon.om NodeInfo)
    (net.sf.saxon.tree.util Navigator)))

;;
;; Utilities
;;
(def ^CatalogManager
     allocate-catalog-manager
  ;(memoize 
    (fn [arg]
        (cond
          (string? arg)
          (CatalogManager. arg)
          (:files arg)
          (doto (CatalogManager.)
            (.setCatalogFiles (:files arg)))
          (:catalog-properties arg)
          (CatalogManager. (:catalog-properties arg))
          (map? arg)
          (CatalogManager.)
          (instance? CatalogManager arg)
          arg
          :default (throw (Exception. (str "bad manager passed for catalog-resolver" arg))))));)

(defn ^CatalogManager 
      catalog-manager
  [options]
  (doto (allocate-catalog-manager options)
    (.setUseStaticCatalog (or (:use-static-catalog options) false))
    (.setAllowOasisXMLCatalogPI (or (:allow-oasis-xml-catalog-pi options) false))
    (.setVerbosity (or (:verbosity options) 0))
    (.setRelativeCatalogs (or (:relative-catalogs options) false))
    
    (.setUseStaticCatalog (or (:use-static-catalog options) false))))

(defn ^CatalogResolver
      catalog-resolver
  [arg]
  (if (nil? arg)
    (CatalogResolver.)
  (CatalogResolver. (catalog-manager arg))))




(defn- java-prop-name
  [prop]
  (-> (name prop) .toUpperCase (.replace "-" "_")))

(defn set-config-property!
  "Set a configuration property on a Saxon Processor object. Takes keyword
  representing a net.sf.saxon.FeatureKeys field and the value to be set, e.g.
    (set-config-property! :line-numbering true)
  Lets errors bubble up."
  [^Processor proc prop value]
  (case prop
    :catalog-options
    (-> proc
      .getUnderlyingConfiguration
      .getParseOptions
      (.setEntityResolver 
        (catalog-resolver value)))

    (let [prop  (java-prop-name prop)
         ^String field (.get (.getField FeatureKeys prop) nil)]
     (.setConfigurationProperty proc field value))))

(defn ^Processor 
  processor
  "Returns a Saxon Processor object, a thread-safe generator class for documents, 
  stylesheets, & XPaths."
  ([]
    (Processor. false))
  (^Processor [config]
    (let [proc  (processor)
          configurator (fn [[k v]]
                         (set-config-property! proc k v))]
      (doall (map configurator config))
      proc))
  ([k v & {:as config}]
    (processor (assoc config k v ))))
    
(defmulti set-xml-catalog! (fn [catalog is-tracing] (class catalog)))
  (defmethod set-xml-catalog! File
    [catalog is-tracing]
    (set-xml-catalog! (str catalog) is-tracing))
  (defmethod set-xml-catalog! String
    [catalog is-tracing]
    (. net.sf.saxon.trans.XmlCatalogResolver
       (setCatalog catalog (.getUnderlyingConfiguration proc) is-tracing)))


(defmulti ^Source xml-source class)
  (defmethod xml-source File
    [f]
    (StreamSource. ^File f))
  (defmethod xml-source InputStream
    [i]
    (StreamSource. ^InputStream i))
  (defmethod xml-source URL
    [u]
    (StreamSource. ^InputStream (.openStream ^URL u)))
  (defmethod xml-source Reader
    [r]
    (StreamSource. ^Reader r))
  (defmethod xml-source String
    [s]
    (StreamSource. (StringReader. ^String s)))
  (defmethod xml-source XdmNode
    [nd]
    (.asSource ^XdmNode nd))


;; Well, except this is public -- maybe doesn't need to be
(defn atomic?
  "Returns true if XdmItem or a subclass (XdmAtomicValue, XdmNode) is an atomic value."
  [^XdmItem val]
  (.isAtomicValue val))

(defn unwrap-xdm-items
  "Makes XdmItems Clojure-friendly. A Saxon XdmItem is either an atomic value 
  (number, string, URI) or a node. 
  
  This function returns a sequence of items, turning XdmAtomicValues 
  into their corresponding Java datatypes (Strings, the numeric types), leaving XdmNodes 
  as nodes."
  [sel]
  (map #(if (atomic? %) (.getValue #^XdmAtomicValue %) %) sel))

;;
;; Public functions
;;

(defn ^XdmNode
	compile-xml
  "Compiles XML into an XdmNode, the Saxon 
  currency for in-memory tree representation. Takes
  File, URL, InputStream, Reader, or String." 
  [^Processor proc x]
  (.. proc (newDocumentBuilder) 
                  (build (xml-source x))))

(defn compile-xslt
  "Compiles stylesheet (from anything convertible to javax.
  xml.transform.Source), returns function that applies it to 
  compiled doc or node."
  [^Processor proc f]
  (let    [cmplr  (.newXsltCompiler proc)
           exe    (.compile cmplr   (xml-source f))]

    (fn [initial ^Destination dest & params]
      (let  [transformer (.load exe)] ; created anew, is thread-safe
        (when params
          (let [prms  (first params)
                ks    (keys prms)]
            (doseq [k ks]
              (.setParameter transformer
                             (QName. ^String (name k))
                             (XdmAtomicValue. (k prms))))))
        (if (instance? XdmNode initial)
          (.setInitialContextNode transformer ^XdmNode initial)
          (.setInitialTemplate transformer (QName. ^String initial)))
        (doto transformer
          (.setDestination dest)
          (.transform))
        dest))))

(defn xdm-result
  [^XdmDestination result]
  (-> result .getXdmNode))

(defn compile-xpath
  "Compiles XPath expression (given as string), returns
  function that applies it to compiled doc or node. Takes 
  optional map of prefixes (as keywords) and namespace URIs."
  [^Processor proc ^String xpath & ns-map]
  (let  [cmplr  (doto (.newXPathCompiler proc) 
                    (#(doseq [[pre uri] (first ns-map)]
                        (.declareNamespace ^XPathCompiler % (name pre) uri))))
         exe    (.compile cmplr xpath)]

    (fn [^XdmNode xml] 
      (unwrap-xdm-items
        (doto (.load exe)
          (.setContextItem xml))))))

(defn compile-xquery
  "Compiles XQuery expression (given as string), returns
  function that applies it to compiled doc or node. Takes 
  optional map of prefixes (as keywords) and namespace URIs."
  [^Processor proc ^String xquery & ns-map]
  (let  [cmplr  (doto (.newXQueryCompiler proc) 
                    (#(doseq [[pre uri] (first ns-map)]
                        (.declareNamespace ^XQueryCompiler % (name pre) uri))))
         exe    (.compile cmplr xquery)]

    (fn [^XdmNode xml] 
      ; TODO add variable support
      ;(.setExternalVariable ^Qname name ^XdmValue val)
      (unwrap-xdm-items 
        (doto (.load exe)
          (.setContextItem xml))))))

;; memoize compile-query funcs, create top-level query func

  ;; redef, decorate-with are copyright (c) James Reeves. All rights reserved.
  ;; Taken from compojure.control; Compojure: http://github.com/weavejester/compojure
(defmacro redef
  "Redefine an existing value, keeping the metadata intact."
  {:private true}
  [name value]
  `(let [m# (meta #'~name)
         v# (def ~name ~value)]
     (alter-meta! v# merge m#)
     v#))

(defmacro decorate-with
  "Wrap multiple functions in a decorator."
  {:private true}
  [decorator & funcs]
  `(do ~@(for [f funcs]
          `(redef ~f (~decorator ~f)))))

(decorate-with memoize compile-xpath compile-xquery)

(defn query
  "Run query on node. Arity of two accepts (1) string or compiled query fn & (2) node;
  arity of three accepts (1) string query, (2) namespace map, & (3) node."
  ([^Processor proc q nd] ((if (fn? q) q (compile-xquery proc q)) nd))
  ([^Processor proc q nses nd] ((compile-xquery proc q nses) nd)))

(definline with-default-ns
  "Returns XQuery string with nmspce declared as default element namespace."
  [nmspce q] `(format "declare default element namespace '%s'; %s" ~nmspce ~q))


;; Serializing

(defn- write-value
  [^Processor proc ^XdmValue node ^Destination serializer]
  (.writeXdmValue proc node serializer))

(defn- set-props
  [^Serializer s props]
  (doseq [[prop value] props]
    (let [prop (Serializer$Property/valueOf (java-prop-name prop))]
      (.setOutputProperty s prop value))))

(defmulti serialize (fn [^Processor proc node dest & props] (class dest)))
  (defmethod serialize File
    [^Processor proc node ^File dest & props]
    (let [s (Serializer.)]
      (set-props s (first props))
      (write-value proc node (doto s (.setOutputFile dest)))
      dest))
  (defmethod serialize OutputStream
    [^Processor proc node ^OutputStream dest & props]
    (let [s (Serializer.)]
      (set-props s (first props))
      (write-value proc node (doto s (.setOutputStream dest)))
      dest))
  (defmethod serialize Writer
    [^Processor proc node ^Writer dest & props]
    (let [s (Serializer.)]
      (set-props s (first props))
      (write-value proc node (doto s (.setOutputWriter dest)))
      dest))

(defn serializer
  ([^Processor proc]
    (-> proc .newSerializer))
  ([^Processor proc ^Destination dest]
    (-> proc (.newSerializer dest))))
;; Node functions

(defn parent-node
  "Returns parent node of passed node."
  [^XdmNode nd]
  (.getParent nd))

(defn node-name
  "Returns the name of the node (as QName)."
  [^XdmNode nd]
  (.getNodeName nd))

(defn node-ns
  "Returns the namespace of the node or node name."
  [q]
  (if (= (class q) QName)
      (.getNamespaceURI ^QName q)
      (node-ns (node-name q))))

(def ^:private 
  node-kind-map
      {XdmNodeKind/DOCUMENT   :document
       XdmNodeKind/ELEMENT    :element
       XdmNodeKind/ATTRIBUTE  :attribute
       XdmNodeKind/TEXT       :text
       XdmNodeKind/COMMENT    :comment
       XdmNodeKind/NAMESPACE  :namespace
       XdmNodeKind/PROCESSING_INSTRUCTION :processing-instruction})

(defn node-kind
  "Returns keyword corresponding to node's kind."
  [^XdmNode nd]
  (node-kind-map (.getNodeKind nd)))

(defn node-path
  "Returns XPath to node."
  [^XdmNode nd]
  (Navigator/getPath (.getUnderlyingNode nd)))

(defn get-attr-value
  "Get the value of attribute `attr` of `el`. `el` must be an element."
  [^String attr ^XdmNode el]
  (.getAttributeValue el (QName. attr)))

;(def ^{:private true} 
;    axis-map
;        {:ancestor            Axis/ANCESTOR           
;         :ancestor-or-self    Axis/ANCESTOR_OR_SELF   
;         :attribute           Axis/ATTRIBUTE          
;         :child               Axis/CHILD              
;         :descendant          Axis/DESCENDANT         
;         :descendant-or-self  Axis/DESCENDANT_OR_SELF 
;         :following           Axis/FOLLOWING          
;         :following-sibling   Axis/FOLLOWING_SIBLING  
;         :parent              Axis/PARENT             
;         :preceding           Axis/PRECEDING          
;         :preceding-sibling   Axis/PRECEDING_SIBLING  
;         :self                Axis/SELF               
;         :namespace           Axis/NAMESPACE})
;
;(defn axis-seq
;   "Returns sequences of nodes on given axis."
;   ([^XdmNode nd axis]
;    (.axisIterator nd ^Axis (axis-map axis)))
;   ([^XdmNode nd axis name]
;    (.axisIterator nd ^Axis (axis-map axis) (QName. ^String name))))

; Node-kind predicates

(defn document?
  "Returns true if node is document."
  [^XdmNode nd]
  (.equals (.getNodeKind nd) XdmNodeKind/DOCUMENT))

(defn element?
  "Returns true if node is element."
  [^XdmNode nd]
  (.equals (.getNodeKind nd) XdmNodeKind/ELEMENT))

(defn attribute?
  "Returns true if node is attribute."
  [^XdmNode nd]
  (.equals (.getNodeKind nd) XdmNodeKind/ATTRIBUTE))

(defn text?
  "Returns true if node is text."
  [^XdmNode nd]
  (.equals (.getNodeKind nd) XdmNodeKind/TEXT))

(defn comment?
  "Returns true if node is comment."
  [^XdmNode nd]
  (.equals (.getNodeKind nd) XdmNodeKind/COMMENT))
  
(defn namespace?
  "Returns true if node is namespace."
  [^XdmNode nd]
  (.equals (.getNodeKind nd) XdmNodeKind/NAMESPACE))

(defn processing-instruction?
  "Returns true if node is processing instruction."
  [^XdmNode nd]
  (.equals (.getNodeKind nd) XdmNodeKind/PROCESSING_INSTRUCTION))

; Integrated extension functions

(defn- replace-str
  "A version of clojure.string/replace that takes the input string as the last
  argument so that this function can be composed."
  [match replacement s]
  (clojure.string/replace s match replacement))

(def ^:private constantize-keyword
  "Takes a :keyword-like-this and turns it into a Java-style
  CONSTANT_LIKE_THIS."
  (comp upper-case (partial replace-str #"-" "_") name))

(defn ^:private get-static-fields-as-keywords
  "Get a list of all static fields in a class as keywords. Example:

  => (get-static-fields-as-keywords Math)
  (:e :pi)"
  [cls]
  (map #((comp keyword (partial replace-str #"_" "-") lower-case :name)
         (bean %))
       (seq (:fields (bean cls)))))

(defn ^:private get-class-constant
  "Get the value of a public static field of a Java class. Takes a keyword
  and assumes that the field is a constant and therefore uses all caps. Example:

  => (get-class-constant Math :pi)
  3.141592653589793"
  [cls field]
  (eval (read-string
          (str (.getName cls) "/" (constantize-keyword field)))))

(defn make-sequence-type
  "A wrapper for Saxon's SequenceType.makeSequenceType() method. Takes
  arguments in the reverse order to the original method because it feel
  more pleasant to say `[:one :boolean]` than `[:boolean :one]`."
  [occurrence-indicator item-type]
  {:pre [(some #{occurrence-indicator}
               (get-static-fields-as-keywords OccurrenceIndicator))
         (some #{item-type}
               (get-static-fields-as-keywords ItemType))]}
  (SequenceType/makeSequenceType
    (get-class-constant ItemType item-type)
    (get-class-constant OccurrenceIndicator occurrence-indicator)))

(defmacro defextfn
  "Define a Saxon integrated extension function.

  For information on integrated extension functions, see:

  http://www.saxonica.com/documentation/index.html#!extensibility/integratedfunctions

  Arguments:

    fn-name     - The name of the function.
    fn-ns       - The namespace to add the function into.
    arg-types   - The argument types (OccurrenceIndicator & ItemType)
                  the function takes.
    result-type - The result type (OccurrenceIndicator & ItemType) of the
                  function.
    arguments   - A vector of the arguments the XPath function receives.
    body        - The body of the function.

  Example:

    (defextfn has-class
      \"http://github.com/eerohele\"
      [[:one :any-node] [:one :string]] ; Takes one node arg and one string arg.
      [:one :boolean]                   ; Returns one boolean value.
      [el class-name]                   ; The args to the XPath function.
      (XdmAtomicValue. (boolean (dita/has-class? (str class-name) el))))

    ; Example use of has-class? extension function :
    ; (has-class? 'map/topicref' el)"
  [fn-name fn-ns arg-types result-type arguments & body]
  `(defn ~fn-name []
     (reify ExtensionFunction
       (getName [this]
                (QName. ~fn-ns (str '~fn-name)))
       (getResultType [this]
                      (apply make-sequence-type ~result-type))
       (getArgumentTypes [this]
                         (into-array
                           (map (partial apply make-sequence-type) ~arg-types)))
       (call [this args#] (let [~arguments (unwrap-xdm-items args#)]
                           (do ~@body))))))
