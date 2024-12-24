(defproject latte-lists "0.1.0-SNAPSHOT"
  :description "Finite lists in LaTTe"
  :url "https://github.com/latte-central/latte-nats.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [latte-sets "1.0b10-SNAPSHOT"]
                 [latte-nats "0.7.0-SNAPSHOT"]]
  :repl-options {:init-ns latte-lists.core})
