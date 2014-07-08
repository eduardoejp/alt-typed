(ns alt.typed.prelude.clojure-lang
  (:require [alt.typed.context :as &context]
            (alt.typed.context [ns :as &ns])
            (alt.typed.syntax representation
                              [parser :as &parser])
            [alt.typed.ann :as &ann :refer [ann ann-class defop]])
  (:import (alt.typed.syntax.representation Fn)))

;; [Functions]
(defn init [context]
  (-> context
      (&context/enter-ns 'clojure.lang)
      (&ns/import "clojure.lang.Keyword")
      (&ns/import "clojure.lang.IPersistentMap")
      (&ns/import "clojure.lang.ISeq")
      (ann-class Keyword [])
      (ann-class (ISeq x) [])
      (ann-class (IPersistentMap k v) [])
      ))
