(ns alt.typed.context.graph
  (:refer-clojure :exclude [find pop])
  (:require (alt.typed [util :as &util]
                       [type :as &type]))
  (:import (alt.typed.type ArgInfo
                           ClassTypeCtor
                           TypeCtor
                           TypeVar)))

;; [Protocols]
(defprotocol $TypeGraph
  (ann [graph var-name node-id])
  (find [graph binding-name])
  (get-var [graph id])
  (add-var [graph var-name type])
  (get-type [graph id])
  (add-type [graph type])
  (push [graph frame])
  (pop [graph])
  (constrain [graph id top])
  (instance [graph type-fn]))

;; [Functions]
(defn id? [x]
  (instance? Long x))

;; [Implementations]
(defrecord VarGraphCell [name type])

(defrecord TypeGraphCell [type])

(defrecord TypeGraph [_id _global _local _graph]
  $TypeGraph
  (ann [self var-name type]
    (assert (namespace var-name) ["Can't annotate unqualified vars." {:var var-name}])
    (assert (not (contains? _global var-name)) ["Can't annotate the same var twice." {:var var-name}])
    (assoc-in self [:_global var-name] type))
  
  (get-var [self id]
    (assert (contains? _graph id))
    (-> _graph ^VarGraphCell (get id) .-type))

  (get-type [self id]
    (assert (contains? _graph id))
    (let [node (get _graph id)]
      (cond (instance? VarGraphCell node)
            (TypeVar. id (.-name node))

            (instance? TypeGraphCell node)
            (.-type node))))
  
  (add-var [self var-name type]
    (assert (and (symbol? var-name) (nil? (namespace var-name))))
    (assert (&type/type? type))
    (let [$node (inc _id)]
      [(-> self
           (assoc-in [:_graph $node] (VarGraphCell. var-name type))
           (assoc :_id $node))
       $node]))

  (add-type [self type]
    (assert (&type/type? type))
    (let [$node (inc _id)]
      [(-> self
           (assoc-in [:_graph $node] (TypeGraphCell. type))
           (assoc :_id $node))
       $node]))
  
  (constrain [self id top]
    (assert (instance? VarGraphCell (get _graph id)))
    (assert (&type/type? top))
    (assoc-in self [:_graph id :type] top))
  
  (find [self binding-name]
    (prn 'graph/find binding-name)
    (if (namespace binding-name)
      (get _global binding-name)
      (some (&util/partial* get binding-name) _local)))
  
  (push [self frame]
    (assert (every? (comp not namespace) (keys frame)) "The local environment is for local (unqualified) vars.")
    (update-in self [:_local] conj frame))
  
  (pop [self]
    (assert (not (empty? _local)) "Can't pop an empty stack!")
    (update-in self [:_local] rest))
  
  (instance [graph type-fn]
    (let [[graph =vars] (reduce (fn [[graph =vars] ^ArgInfo var-info]
                                  (let [[graph =var] (add-var graph (.-name var-info) (.-type var-info))]
                                    [graph (conj =vars =var)]))
                                [graph []]
                                (&type/params type-fn))]
      [graph
       (&type/apply-fn type-fn =vars)]))
  )

;; [Constants]
(def +new-graph+
  (TypeGraph. -1 {} '() {}))
