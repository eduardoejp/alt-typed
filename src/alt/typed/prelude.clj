(ns alt.typed.prelude
  (:require (alt.typed [context :as &context])
            (alt.typed.context [ns :as &ns])
            (alt.typed.prelude [clojure-lang :as &clojure-lang]
                               [alt-typed :as &alt-typed]
                               [clojure-core :as &clojure-core])))

;; [Functions]
(defn init [context]
  (-> context
      &clojure-lang/init
      &alt-typed/init
      &clojure-core/init
      (&context/enter-ns 'user)
      (&ns/refer 'clojure.core nil nil #{} {})))
