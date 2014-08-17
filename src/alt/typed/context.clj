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
(defrecord Context [_current-ns _namespaces]
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
  (-> (Context. nil {})
      &&graph/install
      &&library/install))
