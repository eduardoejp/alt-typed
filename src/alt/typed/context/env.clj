(ns alt.typed.context.env
  (:refer-clojure :exclude [find pop])
  (:require [alt.typed.util :as &util]))

;; [Methods]
(defn ann [env var-name type]
  (assert (namespace var-name) ["Can't annotate unqualified vars." {:var var-name}])
  (assert (not (contains? (::global env) var-name)) ["Can't annotate the same var twice." {:var var-name}])
  (assoc-in env [::global var-name] type))

(defn find [env binding-name]
  (if (namespace binding-name)
    (get (::global env) binding-name)
    (some (&util/partial* get binding-name) (::local env))))

(defn push [env frame]
  (assert (not (some namespace (keys frame))) "The local environment is for local (unqualified) vars.")
  (update-in env [::local] conj frame))

(defn pop [env]
  (assert (not (empty? (::local env))) "Can't pop an empty stack!")
  (update-in env [::local] rest))

;; [Functions]
(defn install [obj]
  (merge obj {::global (hash-map), ::local '()}))
