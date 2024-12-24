
(ns latte-nats.main
  (:gen-class)
  (:require [latte.main :refer [latte-main]]))

(defn -main [& args]
  (latte-main args "latte-nats"
              '[latte-nats.core
                latte-nats.rec
                latte-nats.plus
                latte-nats.ord
                latte-nats.times]))

