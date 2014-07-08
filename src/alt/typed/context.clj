(ns alt.typed.context
  (:refer-clojure :exclude [import refer intern resolve create-ns])
  (:require (clojure [set :as set])
            (alt.typed.context [ns :as &&ns]
                               [library :as &&library]
                               [graph :as &&graph])))

;; [Protocols]
(defprotocol $Context
  (current-ns [context])
  (create-ns [context ns])
  (enter-ns [context ns]))

;; [Implementations]
(defrecord Context [_current-ns _namespaces _library _graph]
  &&graph/$TypeGraph
  (&&graph/ann [self var-name node-id]
    (update-in self [:_graph] &&graph/ann var-name node-id))
  (&&graph/get-var [self id]
    (&&graph/get-var _graph id))
  (&&graph/add-var [self var-name type]
    (let [[_graph $node] (&&graph/add-var _graph var-name type)]
      [(assoc self :_graph _graph)
       $node]))
  (&&graph/get-type [self id]
    (&&graph/get-type _graph id))
  (&&graph/add-type [self type]
    (let [[_graph $node] (&&graph/add-type _graph type)]
      [(assoc self :_graph _graph)
       $node]))
  (&&graph/constrain [self id top]
    (update-in self [:_graph] &&graph/constrain id top))
  (&&graph/find [self binding-name]
    (&&graph/find _graph binding-name))
  (&&graph/push [self frame]
    (update-in self [:_graph] &&graph/push frame))
  (&&graph/pop [self]
    (update-in self [:_graph] &&graph/pop))
  (&&graph/instance [self type-fn]
    (let [[_graph =type] (&&graph/instance _graph type-fn)]
      [(assoc self :_graph _graph)
       =type]))

  &&library/$Library
  (&&library/save [self type-name type]
    (when-let [ns (namespace type-name)]
      (assert (= _current-ns (symbol ns)) (str "Can't save types belonging to another namespace [" type-name "]")))
    (update-in self [:_library] &&library/save type-name type))
  (&&library/lookup [selfx type-name]
    (&&library/lookup _library type-name))

  $Context
  (current-ns [self]
    (get _namespaces _current-ns))
  (create-ns [self ns-sym]
    (if (contains? _namespaces ns-sym)
      self
      (update-in self [:_namespaces] assoc ns-sym (&&ns/make-ns ns-sym))))
  (enter-ns [self ns-sym]
    (-> self (create-ns ns-sym) (assoc :_current-ns ns-sym)))

  &&ns/$NS
  (&&ns/ns-name [self]
    (-> _namespaces (get _current-ns) &&ns/ns-name))
  (&&ns/common-name [self sym]
    (-> _namespaces (get _current-ns) (&&ns/common-name sym)))
  (&&ns/ns-alias [self real-ns]
    (-> _namespaces (get _current-ns) (&&ns/ns-alias real-ns)))
  (&&ns/ns-import [self class-name]
    (-> _namespaces (get _current-ns) (&&ns/ns-import class-name)))
  (&&ns/public-vars [self]
    (-> _namespaces (get _current-ns) &&ns/public-vars))
  (&&ns/resolve [self symbol]
    (-> _namespaces (get _current-ns) (&&ns/resolve symbol)))
  (&&ns/refer [self ns-name alias only exclude rename]
    (assert (contains? _namespaces ns-name))
    (update-in self [:_namespaces _current-ns] &&ns/refer (get _namespaces ns-name) alias only exclude rename))
  (&&ns/import [self class-name]
    (update-in self [:_namespaces _current-ns] &&ns/import class-name))
  (&&ns/intern [self var-name]
    (update-in self [:_namespaces _current-ns] &&ns/intern var-name))
  )

;; [Constants]
(def +new-context+
  (Context. nil {} &&library/+new-library+ &&graph/+new-graph+))
