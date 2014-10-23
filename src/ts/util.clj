(ns ts.util
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.core.logic.protocols :refer [walk ext-no-check]]))

;; [Interface]
(defn %put! [m ks v m*]
  #(when (not (nil? v))
     (unify % (assoc-in (-reify % m) (-reify % ks) v) m*)))

(defn %get! [m ks v]
  #(let [val (get-in (-reify % m) (-reify % ks))]
     (when (not (nil? val))
       (unify % val v))))
