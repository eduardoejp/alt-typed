(ns alt.typed.prelude.clojure-core
  (:require [alt.typed.context :as &context]
            (alt.typed.syntax representation
                              [parser :as &parser])
            (alt.typed.context [ns :as &ns])
            [alt.typed.ann :as &ann :refer [ann ann-macro ann-class defop]])
  (:import (alt.typed.syntax.representation Fn)))

;; [Functions]
(defn init [context]
  (-> context
      (&context/enter-ns 'clojure.core)
      (&ns/refer 'alt.typed 't nil #{} {})
      (&ns/import "clojure.lang.ISeq")
      (&ns/import "clojure.lang.IPersistentMap")
      (ann-macro ns)
      (ann-macro defn)
      (ann-macro fn)
      (ann-macro let)
      (ann-macro if-let)
      (ann-macro comment)
      (ann-macro cond)
      (ann reduce (t/All [a b] [[a b -> a] a (ISeq b) -> a]))
      (ann get (t/All [k v] [(t/Map k v) k -> (t/Maybe v)]))
      (ann assoc (t/All [k v] [(t/Map k v) k v -> (t/Map k v)]))
      (ann map? (t/Fn [(Map Any Any) -> true]
                      [(Not (Map Any Any)) -> false]))
      (ann nil? (t/Fn [nil -> true]
                      [(Not nil) -> false]))
      ))
