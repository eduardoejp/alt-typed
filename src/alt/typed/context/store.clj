(ns alt.typed.context.store
  (:require [alt.typed.type :as &type])
  (:import (alt.typed.type ArgInfo
                           TypeVar)))

;; [Data]
(defrecord Cell [name type])

;; [Methods]
(defn store [store var-name type]
  (assert (and (symbol? var-name) (nil? (namespace var-name))))
  (assert (&type/type? type))
  (let [$node (inc (::id store))]
    [(-> store
         (assoc-in [::store $node] (Cell. var-name type))
         (assoc ::id $node))
     (TypeVar. $node var-name)]))

(defn retrieve [store ^TypeVar $var]
  (assert (contains? (::store store) (.-id $var)))
  (-> (::store store) ^Cell (get (.-id $var)) .-type))

(defn constrain [store ^TypeVar $var top]
  (assert (contains? (::store store) (.-id $var)))
  (assert (&type/type? top))
  (assoc-in store [::store (.-id $var) :type] top))

(defn redirect [store ^TypeVar $from ^TypeVar $to]
  (assert (and (contains? (::store store) (.-id $from))
               (contains? (::store store) (.-id $to))))
  (assoc-in store [::store (.-id $from)] (get-in store [::store (.-id $to)])))

(let [instancer (fn [[storage =vars] ^ArgInfo var-info]
                  (let [[storage =var] (store storage (.-name var-info) (.-type var-info))]
                    [storage (conj =vars =var)]))]
  (defn instance [store type-fn]
    (let [[store =vars] (reduce instancer [store []] (&type/params type-fn))]
      [store
       (&type/apply-fn type-fn =vars)])))

;; [Functions]
(defn install [obj]
  (merge obj {::id -1, ::store (hash-map)}))
