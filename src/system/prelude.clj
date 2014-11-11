(ns system.prelude
  (:require (system [util :as &util :refer [exec
                                            zero return return-all
                                            map-m reduce-m]])
            (system.prelude [java-lang :as &java-lang])))

;; [Interface]
(def install
  (exec [_ &java-lang/install]
    (return nil)))
