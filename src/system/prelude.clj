(ns system.prelude
  (:require (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]])
            (system.prelude [java-lang :as &java-lang])))

;; [Interface]
(def install
  (exec state-seq-m
    [_ &java-lang/install
     state &util/get-state
     ;; :let [_ (prn 'install/state (:types state))]
     ]
    (return state-seq-m nil)))
