(ns system.prelude.java-lang
  (:require (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]]
                    [env :as &env]
                    [type :as &type])))

;; [Interface]
(def install
  (exec state-seq-m
    [_ (&util/with-field :env
         (&env/in-ns 'java.lang))
     _ (&util/with-field* :types
         (exec state-seq-m
           [_ (&type/define-class '[Object []] '[])
            _ (&type/define-class '[String []] '[[Object []]])
            _ (&type/define-class '[Number []] '[[Object []]])
            _ (&type/define-class '[Byte []] '[[Number []]])
            _ (&type/define-class '[Short []] '[[Number []]])
            _ (&type/define-class '[Integer []] '[[Number []]])
            _ (&type/define-class '[Long []] '[[Number []]])]
           (return state-seq-m nil)))]
    (return state-seq-m nil)))
