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
            _ (&type/define-class '[java.lang.String []] '[[::&type/object java.lang.Object []]])
            _ (&type/define-class '[java.lang.Number []] '[[::&type/object java.lang.Object []]])
            _ (&type/define-class '[java.lang.Boolean []] '[[::&type/object java.lang.Object []]])
            _ (&type/define-class '[java.lang.Byte []] '[[::&type/object java.lang.Number []]])
            _ (&type/define-class '[java.lang.Short []] '[[::&type/object java.lang.Number []]])
            _ (&type/define-class '[java.lang.Integer []] '[[::&type/object java.lang.Number []]])
            _ (&type/define-class '[java.lang.Long []] '[[::&type/object java.lang.Number []]])
            _ (&type/define-class '[java.lang.Exception []] '[[::&type/object java.lang.Object []]])
            _ (&type/define-class '[clojure.lang.Var [x]] '[[::&type/object java.lang.Object []]])]
           (return state-seq-m nil)))]
    (return state-seq-m nil)))
