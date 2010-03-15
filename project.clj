(defproject clojure-saxon "0.9.1-SNAPSHOT"
            :description "Clojure wrapper for the Saxon XSLT and XQuery processor."
            :main saxon
            :dependencies [[org.clojure/clojure "1.2.0-master-SNAPSHOT"]
                           [org.clojure/clojure-contrib "1.2.0-SNAPSHOT"]
                           [org.clojars.pjt/saxon9 "9.1.0.8"]
                           [org.clojars.pjt/saxon9-s9api "9.1.0.8"]]
            :dev-dependencies [[lein-clojars/lein-clojars "0.5.0-SNAPSHOT"]])
