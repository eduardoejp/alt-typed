(ns system.prelude.java-lang
  (:require (system [util :as &util :refer [exec
                                            map-m reduce-m
                                            zero return return-all]]
                    [env :as &env]
                    [type :as &type]
                    [parser :as &parser]
                    [type-checker :as &type-checker])))

;; [Interface]
(def install
  (exec [;; state &util/get-state
         ;; :let [_ (prn 'java-lang/state1 state)]
         _ (&util/with-field :env
             (&env/in-ns 'java.lang))
         ;; state &util/get-state
         ;; :let [_ (prn 'java-lang/state2 state)]
         parsed-code (&parser/parse '(do (ann-class java.lang.Object [])
                                       (ann-class (java.lang.Class x) [java.lang.Object])
                                       (ann-class java.lang.String [java.lang.Object])
                                       (ann-class java.lang.Number [java.lang.Object])
                                       (ann-class java.lang.Boolean [java.lang.Object])
                                       (ann-class java.lang.Byte [java.lang.Number])
                                       (ann-class java.lang.Short [java.lang.Number])
                                       (ann-class java.lang.Integer [java.lang.Number])
                                       (ann-class java.lang.Double [java.lang.Number])
                                       (ann-class clojure.lang.IPersistentMap [java.lang.Object])
                                       (ann-class java.lang.Long [java.lang.Number]
                                                  :ctor (Fn [java.lang.String -> java.lang.Long])
                                                  :static-methods {decode (Fn [java.lang.String -> java.lang.Long])}
                                                  :static-fields {MAX_VALUE java.lang.Long}
                                                  :methods {doubleValue (Fn [-> java.lang.Double])}
                                                  :fields {value java.lang.Long})
                                       (ann-class java.lang.Throwable [java.lang.Object])
                                       (ann-class java.lang.Exception [java.lang.Throwable])
                                       (ann-class (clojure.lang.Var x) [java.lang.Object])
                                       (ann-class (clojure.lang.PersistentList elems) [java.lang.Object])
                                       (ann-class (clojure.lang.IPersistentSet elems) [java.lang.Object])))
         ;; state &util/get-state
         ;; :let [_ (prn 'java-lang/state3 state)]
         ]
    (&type-checker/check* parsed-code)))
