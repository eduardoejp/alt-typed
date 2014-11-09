(ns system.prelude.java-lang
  (:require (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]]
                    [env :as &env]
                    [type :as &type]
                    [parser :as &parser]
                    [type-checker :as &type-checker])))

;; [Interface]
(def install
  (exec state-seq-m
    [_ (&util/with-field :env
         (&env/in-ns 'java.lang))
     parsed-code (&parser/parse '(do (ann-class java.lang.Object [])
                                   (ann-class java.lang.String [java.lang.Object])
                                   (ann-class java.lang.Number [java.lang.Object])
                                   (ann-class java.lang.Boolean [java.lang.Object])
                                   (ann-class java.lang.Byte [java.lang.Number])
                                   (ann-class java.lang.Short [java.lang.Number])
                                   (ann-class java.lang.Integer [java.lang.Number])
                                   (ann-class java.lang.Long [java.lang.Number]
                                              :ctor [java.lang.String -> java.lang.Long]
                                              :static-methods {decode [java.lang.String -> java.lang.Long]}
                                              :static-fields {MAX_VALUE java.lang.Long}
                                              :methods {doubleValue [-> java.lang.Double]}
                                              :fields {value java.lang.Long})
                                   (ann-class java.lang.Double [java.lang.Number])
                                   (ann-class java.lang.Exception [java.lang.Object])
                                   (ann-class (clojure.lang.Var x) [java.lang.Object])))]
    (&type-checker/check* parsed-code)))
