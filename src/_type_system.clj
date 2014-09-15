(ns type-system
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :refer :all]))

;; [Utils]
(defn %assoc [m k v o]
  (matche [m k v o]
          ([[] _ _ [[k v]]])
          ([[[k v] . _] _ _ m])
          ([[[k ?v]] _ _ [[k v]]]
             (!= ?v v))
          ([[[k ?v] . ?r] _ _ [[k v] . ?r]]
             (!= ?r ()) (!= ?v v) (!= m o))
          ([[[?j ?v]] _ _ [[?j ?v] [k v]]]
             (!= ?j k))
          ([[[?j ?u] . ?r] _ _ [[?j ?u] . ?o]]
             (!= ?r ()) (!= ?j k) (!= m o)
             (%assoc ?r k v ?o))))

(defn %same-length [l1 l2]
  (matche [l1 l2]
          ([[] []])
          ([[?f1 .  ?r1] [?f2 . ?r2]]
             (%same-length ?r1 ?r2))))

;; [Rules]
;; DB
(db-rel %subclass-of sub super)
(db-rel %annotated var-sym type)

;; Types
(def types (db [%subclass-of 'java.lang.String 'java.lang.Number]
               [%subclass-of 'java.lang.Long   'java.lang.Number]
               [%subclass-of 'java.lang.Double 'java.lang.Number]
               ;; [%annotated 'assoc-if
               ;;  [:all ['k 'v]
               ;;   [:function (list {:params [[:alias 'Map [:class 'clojure.lang.Map ['k 'v]]]
               ;;                              'k
               ;;                              [:union [[:nil] 'v]]]
               ;;                     :return [:alias 'Map [:class 'clojure.lang.Map ['k 'v]]]})]]]
               ))

(defn %apply-instance-params [%apply-instance token type-var types applied]
  (matcha [types]
          ([[?param . ?&params]]
             (fresh [$param $&params]
               (%apply-instance token type-var ?param $param)
               (%apply-instance-params %apply-instance token type-var ?&params $&params)
               (conso $param $&params applied)))
          ([[]] (emptyo applied))))

(defn %apply-instance [param type-var template applied]
  (matcha [template]
          ([param]
             (== applied type-var))
          ([[:literal _ _]]
             (== applied template))
          ([[:nil]]
             (== applied template))
          ([[:function ?arities]]
             (fresh [$arities]
               (%apply-instance param type-var ?arities $arities)
               (== applied [:function $arities])))
          ([[{:params ?params, :return ?return} . ?&arities]]
             (conde [(fresh [$params $return $&arities]
                       (%apply-instance-params %apply-instance param type-var ?params $params)
                       (conde [(emptyo ?&arities)
                               (emptyo $&arities)]
                              [(%apply-instance param type-var ?&arities $&arities)])
                       (%apply-instance param type-var ?return $return)
                       (conso {:params $params, :return $return}
                              $&arities
                              applied))]))
          ([[:alias ?alias ?inner]]
             (fresh [$inner]
               (%apply-instance param type-var ?inner $inner)
               (== applied [:alias ?alias $inner])))
          ([[:class ?class ?params]]
             (fresh [$params]
               (%apply-instance-params %apply-instance param type-var ?params $params)
               (== applied [:class ?class $params])))
          ([[:union ?types]]
             (fresh [$types]
               (%apply-instance-params %apply-instance param type-var ?types $types)
               (== applied [:union $types])))
          ([_]
             (== applied template))
          ))

(defn ^:private %_instance [params inner type]
  (matche [params]
          ([[?param . ?&params]]
             (fresh [$upper $inner]
               (%apply-instance ?param [:var ?param (list $upper [:any])]
                                inner  $inner)
               (trace-lvars (pr-str "%_instance ::" '[?param . ?&params])
                            ?param $inner)
               (%_instance ?&params $inner type)))
          ([[]]
             (== inner type))))

(defn %instance [for-all type]
  (matche [for-all]
          ([[:all ?params ?inner]]
             (%_instance ?params ?inner type))))

;; Solving
(defn ^:private %solve-class-params [%solve args inputs]
  (fresh [$arg $&args $input $&inputs]
    (conde [(emptyo args)
            (emptyo inputs)]
           [(conso $arg $&args args)
            (conso $input $&inputs inputs)
            (%solve-class-params %solve $&args $&inputs)
            (%solve $arg $input)])))

(defn %solve-union [%solve types actual]
  (fresh [$type $&types]
    (conso $type $&types types)
    (conde [(%solve $type actual)]
           [(%solve-union %solve $&types actual)])))

(defn %solve [expected actual]
  (matcha [expected actual]
          ([[:any] _])
          ([_ [:nothing]])
          ([[:nil] [:nil]])
          ([[:alias _ ?type] _]
             (%solve ?type actual))
          ([_ [:alias _ ?type]]
             (%solve expected ?type))
          ([[:class ?class _] [:literal ?class _]])
          ([[:literal ?class ?value] [:literal ?class ?value]])
          ([[:class ?class ?e-params] [:class ?class ?a-params]]
             (%solve-class-params %solve ?e-params ?a-params))
          ([[:union ?types] _]
             (%solve-union %solve ?types actual))
          ([[:var _ [?e-upper-link ?e-upper]] [:var _ [?a-upper-link ?a-upper]]]
             (conde [(%solve ?e-upper ?a-upper)
                     (fresh [$e-upper-link]
                       (== ?e-upper-link (list $e-upper-link ?a-upper)))]
                    ;; [(%solve expected ?e-upper)
                    ;;  ]
                    ))
          ([[:var _ [?e-upper-link ?e-upper]] _]
             (conde [(%solve ?e-upper actual)
                     (fresh [$e-upper-link]
                       (== ?e-upper-link (list $e-upper-link actual)))]
                    ;; [(%solve expected ?e-upper)
                    ;;  ]
                    ))
          ([_ [:var _ [?a-upper-link ?a-upper]]]
             (conde [(%solve ?a-upper expected)
                     (fresh [$a-upper-link]
                       (== ?a-upper-link (list $a-upper-link expected)))]
                    ;; [(%solve expected ?e-upper)
                    ;;  ]
                    ))
          ))

(defn %solve-arity [args inputs]
  (fresh [$arg $&args $input $&inputs]
    (conde [(emptyo args)
            (emptyo inputs)]
           [(conso $arg $&args args)
            (conso $input $&inputs inputs)
            (%solve-arity $&args $&inputs)
            (%solve $arg $input)])))

(defn ^:private %solve-arities [arities inputs return]
  (fresh [$arity $&arities]
    (conso $arity $&arities arities)
    (conde [(fresh [$params $return]
              (== $arity {:params $params, :return $return})
              (%solve-arity $params inputs)
              (== return $return))]
           [(%solve-arities $&arities inputs return)])))

(defn %solve-function [function inputs return]
  (fresh [$arities]
    (== function [:function $arities])
    (%solve-arities $arities inputs return)))

;; (defn %solve [args inputs]
;;   (cond))

;; Analysis
(defn %resolve [symbol type]
  (conde [(%annotated symbol type)]))

(defn %analyze-body [%analyze body env type]
  (matcha [body]
          ([(?form . ?others)]
             (fresh [$type]
               (%analyze ?form $type)
               (conde [(emptyo ?others)
                       (== type $type)]
                      [(%analyze-body %analyze ?others type)])))
          ([[]]
             (== type [:nil]))
          ))

(defn %analyze-bindings [%analyze env bindings env*]
  (matcha [bindings]
          ([[?label ?value . ?bindings]]
             (fresh [$value $env]
               (%analyze ?value $value)
               (%assoc env ?label $value $env)
               (%analyze-bindings %analyze $env ?bindings env*)))
          ([[]]
             (== env env*))
          ))

(defn %analyze-type-params [%analyze-type-def &params &types]
  (matche [&params &types]
          ([[] []])
          ([[?param . ?rest] [?type . ?rem]]
             (%analyze-type-def ?param ?type)
             (%analyze-type-params ?rest ?rem))))

(defn %analyze-type-def [type-def type]
  (matche [type-def]
          ([['Fn . ?arities]]
             u#)
          ([['All ?vars . ?arities]]
             u#)
          ([[?poly . ?params]]
             (fresh [$poly $params $types]
               (%analyze-type-def ?poly $poly)
               (matche [$poly]
                       ([[:all ?poly-params ?inner]]
                          (%same-length ?poly-params ?params)
                          (%analyze-type-params %analyze-type-def ?params $params)
                          (%solve-params $params $types)
                          (%instance-with $poly $types type)))))
          ([?type]
             (fresh [$type-def]
               (conde [(%assoc library ?type type library)]
                      [(%assoc aliases ?type $type-def aliases)
                       (%analyze-type-def $type-def type)]))
             u#)))

(defn %analyze [form env type]
  (matcha [form]
          ([[:do ?body]]
             (%analyze-body %analyze ?body env type))
          ([[:let ?bindings ?body]]
             (fresh [$env]
               (%analyze-bindings %analyze env ?bindings $env)
               (%analyze-body %analyze ?body $env type)))
          ([[:ann ?var-name ?type-def]]
             (fresh [$type]
               (%analyze-type-def ?type-def $type)
               (== $type [:nil])))
          ))

;; Annotating
(comment
  String
  (Map String Long)
  [String -> (Map String Long)]
  (Fn [String -> (Map String Long)]
      [Long -> (Map Long String)])
  (All [x y]
       [(Map x y) x y -> (Map x y)])
  )

;; Tests
(comment
  (alter-var-root #'clojure.core/println
                  (constantly (fn [& strs]
                                (.println System/out (apply str strs)))))
  
  (time
   (with-db types
     (run* [return]
       (fresh [$for-all $instance $inputs]
         (%resolve 'assoc-if $for-all)
         (trace-lvars (pr-str "RUN ::" '$for-all) $for-all)
         ;; (== return $for-all)
         (%instance $for-all $instance)
         (== $inputs (list [:alias 'Map [:class 'clojure.lang.Map [[:class 'java.lang.String []]
                                                                   [:class 'java.lang.Long []]]]]
                           [:class 'java.lang.String []]
                           [:class 'java.lang.Long []]))
         (trace-lvars (pr-str "RUN ::" '$instance) $instance)
         (%solve-function $instance $inputs return)
         ))))

  (run* [return]
    (fresh [$map]
      (featurec $map {:foo 10})
      (featurec $map {:bar "YOLO"})
      (featurec $map {:foo return})))

  (time
   (run* [return]
     (fresh [$map]
       (%assoc [] :foo "LOL" $map)
       (%assoc $map :bar "YOLO" return)
       ;; (%assoc $map :yolo return)
       ;; (%assoc $map return "LOL")
       ;; (== return $map)
       )))
  
  (time
   (with-db types
     (run* [return]
       (fresh [$expected $actual]
         (== $actual [:literal 'java.lang.Long 15])
         (%solve $expected $actual)
         (== return [$expected $actual]))
       )))

  (time
   (with-db types
     (run* [return]
       (fresh [$expected $actual
               $input-1 $input-2]
         (== $expected [['java.lang.Number []]
                        ['java.lang.Long []]])
         (== $actual [$input-1 $input-2])
         (%solve-arity $expected $actual)
         (== return [$expected $actual]))
       )))

  [
   [[[java.lang.Number []] [java.lang.Long []]]
    [[:nothing] _0]]
   [[[java.lang.Number []] [java.lang.Long []]]
    [[java.lang.Double _0] _1]]
   [[[java.lang.Number []] [java.lang.Long []]]
    [[java.lang.Long _0] _1]]
   ]

  (ann assoc-if (All [k v] [(Map k v) k (Maybe v) -> (Map k v)]))
  (defn assoc-if [m k v]
    (if v
      (assoc m k v)
      m))

  [:all '[k v]
   [:function (list {:params [[:alias 'Map [:class 'clojure.lang.Map [k v]]]
                              k
                              [:union [[:nil] v]]]
                     :return [:alias 'Map [:class 'clojure.lang.Map [k v]]]})]]

  (do (defn |assoc-if| [instance]
        (fresh [k v]
          (== instance [:function (list {:params [[:alias 'Map [:class 'clojure.lang.Map [k v]]]
                                                  k
                                                  [:union [[:nil] v]]]
                                         :return [:alias 'Map [:class 'clojure.lang.Map [k v]]]})])))

    (time
     (with-db types
       (run 1 [return]
            (fresh [$instance $inputs]
              (|assoc-if| $instance)
              (== $inputs (list [:alias 'Map [[:class 'java.lang.String []] [:class 'java.lang.Long []]]]
                                [:class 'java.lang.String []]
                                [:class 'java.lang.Long []]))
              (%solve-function $instance $inputs return))
            ))))
  )
