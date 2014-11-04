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
           [_ (&type/define-class '[java.lang.Object []] '[])
            _ (&type/define-class '[java.lang.String []] '[[java.lang.Object []]])
            _ (&type/define-class '[java.lang.Number []] '[[java.lang.Object []]])
            _ (&type/define-class '[java.lang.Byte []] '[[java.lang.Number []]])
            _ (&type/define-class '[java.lang.Short []] '[[java.lang.Number []]])
            _ (&type/define-class '[java.lang.Integer []] '[[java.lang.Number []]])
            _ (&type/define-class '[java.lang.Long []] '[[java.lang.Number []]])]
           (return state-seq-m nil)))]
    (return state-seq-m nil)))
