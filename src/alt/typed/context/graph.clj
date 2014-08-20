(ns alt.typed.context.graph
  (:refer-clojure :exclude [find pop])
  (:require (alt.typed [util :as &util]
                       [type :as &type]))
  (:import (alt.typed.type ArgInfo
                           ClassTypeCtor
                           TypeCtor
                           TypeVar)))

;; [Data]
(defrecord VarGraphCell [name type])

(defrecord TypeGraphCell [type])

;; [Methods]
(defn ann [self var-name type]
  (assert (namespace var-name) ["Can't annotate unqualified vars." {:var var-name}])
  (assert (not (contains? (::global self) var-name)) ["Can't annotate the same var twice." {:var var-name}])
  (assoc-in self [::global var-name] type))

(defn get-var [self id]
  (assert (contains? (::graph self) id))
  (-> (::graph self) ^VarGraphCell (get id) .-type))

(defn get-type [self id]
  (assert (contains? (::graph self) id))
  (let [node (get (::graph self) id)]
    (cond (instance? VarGraphCell node)
          (TypeVar. id (.-name node))

          (instance? TypeGraphCell node)
          (.-type node))))

(defn add-var [self var-name type]
  (assert (and (symbol? var-name) (nil? (namespace var-name))))
  (assert (&type/type? type))
  (let [$node (inc (::id self))]
    [(-> self
         (assoc-in [::graph $node] (VarGraphCell. var-name type))
         (assoc ::id $node))
     $node]))

(defn add-type [self type]
  (assert (&type/type? type))
  (let [$node (inc (::id self))]
    [(-> self
         (assoc-in [::graph $node] (TypeGraphCell. type))
         (assoc ::id $node))
     $node]))

(defn constrain [self id top]
  (assert (instance? VarGraphCell (get (::graph self) id)))
  (assert (&type/type? top))
  (assoc-in self [::graph id :type] top))

(defn find [self binding-name]
  (prn 'graph/find binding-name)
  (if (namespace binding-name)
    (get (::global self) binding-name)
    (some (&util/partial* get binding-name) (::local self))))

(defn push [self frame]
  (assert (not (some namespace (keys frame))) "The local environment is for local (unqualified) vars.")
  (update-in self [::local] conj frame))

(defn pop [self]
  (assert (not (empty? (::local self))) "Can't pop an empty stack!")
  (update-in self [::local] rest))

;; [Functions]
(defn id? [x]
  (instance? Long x))

(defn instance [graph type-fn]
  (let [[graph =vars] (reduce (fn [[graph =vars] ^ArgInfo var-info]
                                (let [[graph =var] (add-var graph (.-name var-info) (.-type var-info))]
                                  [graph (conj =vars =var)]))
                              [graph []]
                              (&type/params type-fn))]
    [graph
     (&type/apply-fn type-fn =vars)]))

(let [+defaults+ {::id -1, ::global (hash-map), ::local '(), ::graph (hash-map)}]
  (defn install [obj]
    (merge obj +defaults+)))
