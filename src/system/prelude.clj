(ns system.prelude
  (:require (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]])
            (system.prelude [java-lang :as &java-lang])))

;; [Interface]
(def install
  (exec state-seq-m
    [_ &java-lang/install]
    (return state-seq-m nil)))
