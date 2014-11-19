(ns system.prelude
  (:require (system [util :as &util :refer [exec
                                            zero return return-all
                                            map-m reduce-m]])
            (system.prelude [java-lang :as &java-lang])))

;; [Interface]
(def install
  (exec [;; state &util/get-state
         ;; :let [_ (prn 'prelude/state1 state)]
         _ &java-lang/install
         ;; state &util/get-state
         ;; :let [_ (prn 'prelude/state2 state)]
         ]
    (return nil)))
