(ns type-system
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :refer :all]))

;; [Utils]
(defn %map [&map]
  (== &map []))

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

(defn %last [&list &last]
  (matche [&list]
    ([[]]
       (== &last nil))
    ([[?prev . ?next]]
       (conde [(== [] ?next)
               (== &last ?next)]
              [(%last ?next &last)]))
    ))

(defn %in-domain [&lvar &domain]
  (matche [&domain]
    ([[&lvar . ?rest]])
    ([[_ . ?rest]]
       (%in-domain &lvar ?rest))))

;; [Rules]
;; Types
(comment
  :any
  :nothing
  :nil
  [:primitive ?type]
  [:literal ?class ?value]
  [:object ?class ?params]
  [:alias ?params ?type] ;; ???
  [:union ?types]
  [:function ?arities]
  [:multimethod ?dispatcher]
  [:class ?name ?abstract ?constructors ?static-fields ?static-methods ?dynamic-fields ?dynamic-methods]
  [:interface ?name ?fields ?methods]
  [:tuple ?kind ?types]
  [:record ?kind ?slots]
  [:recur ?token ?type]

  (ann conj (All [type new-type]
                 (Fn [(List* ~@type) new-type -> (List* new-type ~@type)]
                     [(Vector* ~@type) new-type -> (Vector* ~@type new-type)]
                     [(List type) new-type -> (List (Or type new-type))]
                     [(Vector type) new-type -> (Vector (Or type new-type))]
                     [(IPersistentCollection type) new-type -> (IPersistentCollection (Or type new-type))])))
  )

(def +empty-list+ [:object 'clojure.lang.IPersistentList [:nothing]])
(def +empty-vector+ [:object 'clojure.lang.IPersistentVector [:nothing]])
(def +empty-map+ [:object 'clojure.lang.IPersistentMap [:nothing :nothing]])
(def +empty-set+ [:object 'clojure.lang.IPersistentSet [:nothing]])
(def +throwable+ [:object 'java.lang.Throwable []])

(defn %simple-literal [&class &value &type]
  (all (matche [&class]
         (['java.lang.Boolean])
         (['java.lang.Long])
         (['java.lang.Double])
         (['java.lang.Character])
         (['java.lang.String])
         (['clojure.lang.Keyword])
         (['clojure.lang.Symbol]))
       (== &type [:literal &class &value])))

(defne %class [&object &class]
  ([[:object &class ?params]]))

(let [map-arities (fn [&key-type]
                    (list {:args (list [:object 'clojure.lang.IPersistentMap [&key-type 'v]])
                           :return [:union (list :nil 'v)]}
                          {:args (list [:object 'clojure.lang.IPersistentMap [&key-type 'v]]
                                       'v)
                           :return 'v}))
      record-arities (fn [&record-class &slot]
                       (list [:record :map (list [&slot 'v])]
                             [:record &record-class (list [&slot 'v])]))
      kv-arities (fn [&key &val]
                   (list {:args (list &key)
                          :return [:union (list :nil &val)]}
                         {:args (list &key &val)
                          :return &val}))]
  (defn %as-function [&type &function]
    (matche [&type]
      ([:literal 'clojure.lang.Keyword ?value]
         (fresh [?record-class]
           (== &function [:all ['k 'v] [:function (concat (map-arities [:object 'clojure.lang.Keyword []])
                                                          (record-arities ?record-class &type))]])))
      ([:literal 'clojure.lang.Symbol ?value]
         (fresh [?record-class]
           (== &function [:all ['k 'v] [:function (concat (map-arities [:object 'clojure.lang.Symbol []])
                                                          (record-arities ?record-class &type))]])))
      ([:object 'clojure.lang.Keyword []]
         (== &function [:all ['k 'v] [:function (map-arities &type)]]))
      ([:object 'clojure.lang.Symbol []]
         (== &function [:all ['k 'v] [:function (map-arities &type)]]))
      ([:object 'clojure.lang.IPersistentVector [?elem]]
         (fresh [$idx]
           (%unalias &context 'alt.typed/AnyInteger $idx)
           (== &function [:function (kv-arities $idx ?elem)])))
      ([:object 'clojure.lang.IPersistentMap [?key ?val]]f
         (== &function [:function (kv-arities ?key ?val)]))
      ([:object 'clojure.lang.IPersistentSet [?elem]]
         (== &function [:function (kv-arities ?elem ?elem)]))
      )))

(defn %union-add [&union &type &new-union]
  (matcha [&union &type]
    ([[:union _] [:union ?type . ?rest]]
       (conde [(== ?rest [])
               (%union-append &union ?type &new-union)]
              [(fresh [$union]
                 (%union-append &union ?type $union)
                 (%union-append $union [:union ?rest] &new-union))]))
    ([[:union [?ot . ?rest]] _]
       (conde [(%solve ?ot &type)
               (== &new-union &union)]
              [(%solve &type ?ot)
               (conde [(== ?rest [])
                       (== &new-union [:union [&type]])]
                      [(%union-append [:union ?rest] &type &new-union)])]
              [(conde [(== ?rest [])
                       (== &new-union (== &new-union [:union [?ot &type]]))]
                      [(fresh [$rest]
                         (%union-append ?rest &type $rest)
                         (matche [$rest]
                           ([[:union ?new-types]]
                              (fresh [$new-types]
                                (conso ?ot ?new-types $new-types)
                                (== &new-union [:union $new-types])))))])]
              ))
    ))

(defn %union [&types &union]
  (matche [&types]
    ([[?type . ?rest]]
       (conda [(== ?rest [])
               (== &union ?type)]
              [(%union-add [:union [?type]] [:union ?rest] &union)]))
    ))

;; Type-checker
(defmacro with-context [&context goal]
  `(fresh ~'[&global &local]
     (== ~&context {:env/global ~'&global :env/local ~'&local})
     ~goal))

(defn %context [&context]
  (fresh [$global $local]
    (== &context {:env/global $global :env/local $local})))

;; PHASE 2
(defn %type-check-all [%type-check &context &forms &types]
  (matche [&forms &types]
    ([[] []])
    ([[?form . ?rest] [?type . ?rem]]
       (%type-check &context ?form $type)
       (%type-check-all %type-check &context ?rest $rem))))

(defn %type-check-body [%type-check &context ?body &type]
  (fresh [$types]
    (%type-check-all %type-check &context ?body $types)
    (%last $types &type)))

(defn %type-check-let [%type-check &context &bindings &body &type]
  (with-context &context
    (matche [&bindings]
      ([[]]
         (%type-check-body &context &body &type))
      ([[?label ?value . ?bindings]]
         (fresh [$value $local $context]
           (%type-check &context ?value $value)
           (%with-local &context ?label $value $context)
           (%type-check-let %type-check $context ?bindings &body &type)
           ))
      )))

(defn %type-check-recur [%type-check &context &args]
  (with-context &context
    (fresh [$recur $args]
      (%assoc &local :recur $recur &local)
      (%type-check-all &context &args $args)
      (%solve-all $args $recur))))

(defn %type-check-case [%type-check &context &form-type &pairs &type]
  (with-context &context
    (matche [&pairs]
      ([[?else]]
         (%type-check &context ?else &type))
      ([[?match ?expr . ?rest]]
         (fresh [$match $expr]
           (%type-check &context ?match $match)
           (%type-check &context ?expr $expr)
           (conde [(== [] ?rest)
                   (== &type $expr)]
                  [(fresh [$others]
                     (%type-check-case %type-check &context &form-type ?rest $others)
                     (%as-union $others &type))]))))))

(defn %type-check-catch [%type-check &context &catch &type]
  (matche [&catch]
    ([[:catch ?class ?ex . ?body]]
       (fresh [$ex $context]
         (%instance-class ?class nil $ex)
         (%with-local &context ?ex $ex $context)
         (%type-check-body %type-check &context ?body &type)))))

(defn %intern-var [&context &var &type &new-context]
  (matche [&context]
    ([{:env/global &global :env/local &local}]
       (fresh [$global]
         (%assoc &global &var &type $global)
         (== &new-context {:env/global $global :env/local &local})))))

(defn %type-check-loop-bindings [%type-check &context &bindings &recur]
  (matche [&bindings]
    ([[]]
       (== &recur []))
    ([[?label ?value . ?bindings]]
       (fresh [$value $context $recur]
         (%type-check &context ?value $value)
         (%with-local &context ?label $value $context)
         (%type-check-loop-bindings %type-check $context ?bindings $recur)
         (conso $value $recur &recur)))
    ))

(defn %var [&var-name &var]
  (== &var [:var &var-name]))

(defn %vars [&names &vars]
  (matche [&names &vars]
    ([[] []])
    ([[?name . ?rest] [?var . ?rem]]
       (%var ?name ?var)
       (%vars ?rest ?rem))
    ))

(defn %interleave [&l1 &l2 &interleaved]
  (matche [&l1 &l2]
    ([[] []])
    ([[?head1 . ?tail1] [?head2 . ?tail2]]
       (fresh [$temp]
         (%interleave ?tail1 ?tail2 $temp)
         (conso [?head1 ?head2] $temp &interleaved)))
    ))

(defn %arity [&arity &type]
  (matche [&arity &type]
    ([[?args ?body] [:arity ?inputs ?output]]
       (%vars ?args ?inputs))
    ))

(defn %arities [&arities &types]
  (matche [&arities &types]
    ([[] []])
    ([[?arity . ?rest] [?type . ?rem]]
       (%arity ?arity ?type)
       (%arities ?rest ?rem))
    ))

(defn %with-locals [&context &labels &types &new-context]
  (matche [&labels &types]
    ([[] []]
       (== &context &new-context))
    ([[?label . ?rest] [?type . ?rem]]
       (fresh [$context]
         (%with-local &context ?label ?type $context)
         (%with-locals $context ?rest ?rem &new-context)))
    ))

(defn %type-check-arity [%type-check &context &arity &type]
  (matche [&arity &type]
    ([[?args ?body] [:arity ?inputs ?output]]
       (fresh [$context]
         (%with-locals &context ?args ?inputs $context)
         (%type-check $context ?body ?output)))
    ))

(defn %type-check-arities [%type-check &context &arities &types]
  (matche [&arities &types]
    ([[] []])
    ([[?arity . ?rest] [?type . ?rem]]
       (%type-check-arity %type-check &context ?arity ?type)
       (%type-check-arities %type-check &context ?rest ?rem))
    ))

(defn %type-check-fn [%type-check &context &name &arities &type]
  (fresh [$types]
    (%arities &arities $types)
    (== &type [:function $types])
    (%with-local &context &name &type $context)
    (%type-check-arities %type-check $context &arities $types)
    ))

(letfn [(%helper [&arities &args &type]
          (matche [&arities]
            ([[?arity . ?rest]]
               (%solve-arity ?arity &args &type))
            ([[_ . ?rest]]
               (%helper ?rest &args &type))))]
  (defn %fn-call [&function &args &type]
    (matche [&function]
      ([[:function ?arities]]
         (%helper ?arities &args &type))
      )))

(defn %field-read [&context &object|class &field &type]
  (matche [&object|class]
    ([[:object ?class-name ?params]]
       (fresh [$class]
         (%class-lookup &context ?class-name $class)
         (matche [$class]
           ([[:class _ _ _ _ _ ?dynamic-fields _]]
              (%assoc ?dynamic-fields &field &type ?dynamic-fields)))
         ))
    ([[:class _ _ _ ?static-fields _ _ _]]
       (%assoc ?static-fields &field &type ?static-fields))
    ))

(defb %method-call [&context &object|class &method &args &type]
  (matche [&object|class]
    ([[:object ?class-name ?params]]
       (fresh [$class]
         (%class-lookup &context ?class-name $class)
         (matche [$class]
           ([[:class _ _ _ _ _ _ ?dynamic-methods]]
              (fresh [$method]
                (%assoc ?dynamic-methods &method $method ?dynamic-methods)
                (%fn-call $method &args &type))))
         ))
    ([[:class _ _ _ _ ?static-methods _ _]]
       (fresh [$method]
         (%assoc ?static-methods &method $method ?static-methods)
         (%fn-call $method &args &type)))
    ))

(defn %in-ns [&context ?name &new-context]
  (with-context &context
    (== &new-context {:ns {:name ?name
                           :refers []
                           :imports []}
                      :env {:global &global
                            :local &local}})))

(defn %import [&context ?imports &new-context]
  (with-context &context
    (matche [?imports]
      ([[]]
         (== &context $context))
      ([[[?short ?long] . ?rest]]
         (fresh [$context $name $refers $imports]
           (%assoc &imports ?short ?long $imports)
           (== $context {:ns {:name $name
                              :refers $refers
                              :imports $imports}
                         :env {:global &global
                               :local &local}})
           (%import-all $context ?rest &new-context))))))

(defn %refer [&context ?requires $context]
  (with-context &context
    (matche [?requires]
      ([[]]
         (== &context $context))
      ([[?refer . ?rest]]
         (fresh [$context $name $refers $imports]
           (conso ?refer &refers $refers)
           (== $context {:ns {:name $name
                              :refers $refers
                              :imports $imports}
                         :env {:global &global
                               :local &local}})
           (%require-all $context ?rest &new-context))))))

;; PHASE 1
(defn %type-check [&context &form &type]
  (with-context &context
    (matcha [&form]
      ([:literal/nil]
         (== &type :nil))
      ([[:literal/boolean ?value]]
         (%simple-literal 'java.lang.Boolean ?value &type))
      ([[:literal/integer ?value]]
         (%simple-literal 'java.lang.Long ?value &type))
      ([[:literal/real ?value]]
         (%simple-literal 'java.lang.Double ?value &type))
      ([[:literal/character ?value]]
         (%simple-literal 'java.lang.Character ?value &type))
      ([[:literal/string ?value]]
         (%simple-literal 'java.lang.String ?value &type))
      ([[:literal/keyword ?value]]
         (%simple-literal 'clojure.lang.Keyword ?value &type))
      ([[:literal/symbol ?value]]
         (%simple-literal 'clojure.lang.Symbol ?value &type))
      ([:literal/list []]
         (== &type +empty-list+))
      ([:literal/vector []]
         (== &type +empty-vector+))
      ([:literal/map []]
         (== &type +empty-map+))
      ([:literal/set []]
         (== &type +empty-set+))
      ([[:symbol ?symbol]]
         (conde [(%assoc &local ?symbol &type &local)]
                [(%assoc &global ?symbol &type &global)]
                [(fresh [$long]
                   (%assoc &imports ?symbol $long &imports)
                   (%assoc &classes $long &type &classes))]
                [(fresh [$short]
                   (%assoc &imports $short ?symbol &imports)
                   (%assoc &classes ?symbol &type &classes))]))
      ([[:form/do . ?body]]
         (%type-check-body %type-check &context ?body &type))
      ([[:form/letfn ?bindings . ?body]]
         (log! "[SYSTEM ERROR] letfn hasn't been implemented yet.")
         u#)
      ([[:form/let ?bindings . ?body]]
         (%type-check-let %type-check &context ?bindings ?body &type))
      ([[:form/if ?test ?then ?else]]
         (fresh [$test $then $else]
           (%type-check &context ?test $test)
           (%type-check &context ?then $then)
           (%type-check &context ?else $else)
           (%union [$then $else] &type)))
      ([[:form/case ?form . ?pairs]]
         (fresh [$form]
           (%type-check &context ?form $form)
           (%type-check-case %type-check &context $form ?pairs &type)))
      ([[:form/loop ?bindings ?body]]
         (fresh [$context $recur $local]
           (%type-check-loop-bindings %type-check &context ?bindings $recur)
           (%assoc $local :recur $recur &local)
           (%type-check-body %type-check &context ?body &type)))
      ([[:form/fn ?name ?arities]]
         (%type-check-fn %type-check &context ?name ?arities &type))
      ([[:form/def ?var]]
         (fresh [$global]
           (%intern-var $context ?var :nothing &context)
           (== &type [:object 'clojure.lang.Var [:nothing]])))
      ([[:form/def ?var ?value]]
         (fresh [$global $var-type]
           (%type-check &context ?test $var-type)
           (%intern-var $context ?var $var-type &context)
           (== &type [:object 'clojure.lang.Var [$var-type]])))
      ([[:form/var ?var]]
         (fresh [$var-type]
           (%assoc &global ?var $var-type &global)
           (== &type [:object 'clojure.lang.Var [$var-type]])))
      ([[:form/dot ?object|class ?field|method]]
         (fresh [$object|class]
           (%type-check &context ?object|class $object|class)
           (conde [(%field-read &context $object|class ?field|method &type)]
                  [(%method-call &context $object|class ?field|method [] &type)])))
      ([[:form/dot ?object|class [?method ?args]]]
         (fresh [$object|class]
           (%type-check &context ?object|class $object|class)
           (%method-call &context $object|class ?method ?args &type)))
      ([[:form/new ?class ?args]]
         (fresh [$class]
           (%type-check &context ?class $class)
           (matche [$class]
             ([[:class _ _ ?constructor _ _ _ _]]
                (fresh [$args]
                  (%type-check-all %type-check &context ?args $args)
                  (%ctor-call ?constructor $args &type))))))
      ([[:form/gen-class ?options]]
         (log! "[SYSTEM ERROR] gen-class hasn't been implemented yet.")
         u#)
      ([[:form/defprotocol ?name ?method-defs]]
         (log! "[SYSTEM ERROR] defprotocol hasn't been implemented yet.")
         u#
         ;; (fresh [$protocol]
         ;;   (%type-check-defprotocol &context ?method-defs $protocol)
         ;;   (%simple-literal 'clojure.lang.Symbol ?name &type))
         )
      ([[:form/deftype ?name ?fields ?impls]]
         (log! "[SYSTEM ERROR] deftype hasn't been implemented yet.")
         u#
         ;; (fresh [$type $object]
         ;;   (%type-check-deftype &context ?fields ?impls $type)
         ;;   (%instance-class $type $object nil)
         ;;   (== &type [:object 'java.lang.Class [$object]]))
         )
      ([[:form/defrecord ?name ?fields ?impls]]
         (log! "[SYSTEM ERROR] defrecord hasn't been implemented yet.")
         u#
         ;; (fresh [$type $object]
         ;;   (%type-check-defrecord &context ?fields ?impls $type)
         ;;   (%instance-class $type $object nil)
         ;;   (== &type [:object 'java.lang.Class [$object]]))
         )
      ([[:form/reify ?impls]]
         (log! "[SYSTEM ERROR] reify hasn't been implemented yet.")
         u#
         ;; (fresh [$type]
         ;;   (%type-check-reify &context ?impls &type))
         )
      ([[:form/proxy]]
         (log! "[SYSTEM ERROR] proxy hasn't been implemented yet.")
         u#
         ;; (fresh [$type]
         ;;   (%type-check-proxy &context ?impls &type))
         )
      ([[:form/defmulti ?name ?dispatcher]]
         (log! "[SYSTEM ERROR] defmulti hasn't been implemented yet.")
         u#
         ;; (fresh [$dispatcher $context]
         ;;   (%type-check &context ?dispatcher $dispatcher)
         ;;   (== &type [:multimethod $dispatcher])
         ;;   (%intern-var $context ?name &type &context))
         )
      ([[:form/defmethod ?name ?dispatch-val ?args ?body]]
         (log! "[SYSTEM ERROR] defmethod hasn't been implemented yet.")
         u#
         ;; (fresh [$multi $args $body]
         ;;   (%resolve &context ?name $multi)
         ;;   (%multimethod-args &context $multi ?args $args)
         ;;   (%type-check-body %type-check &context ?body &type))
         )
      ([[:form/throw ?ex]]
         (fresh [$ex]
           (%type-check &context ?ex $ex)
           (conde [(%solve +throwable+ $ex)
                   (== &type :nothing)]
                  [(log! "[ERROR] Must throw a java.lang.Throwable.")
                   u#])))
      ([[:form/try ?body ?catches ?finally]]
         (fresh [$body $catches $finally $all]
           (%type-check-body %type-check &context ?body $body)
           (%type-check-all (partial %type-check-catch %type-check) &context ?catches $catches)
           (%type-check-body %type-check &context ?finally $finally)
           (conso $body $catches $all)
           (%union $all &type)))
      ([[:form/binding ?bindings ?body]]
         (log! "[SYSTEM ERROR] binding hasn't been implemented yet.")
         u#
         ;; (%type-check-binding &context ?bindings)
         ;; (%type-check-body %type-check &context ?body &type)
         )
      ([[:form/recur ?args]]
         (%type-check-recur %type-check &context ?args)
         (== &type :nothing))
      ([[:form/import ?import]]
         (fresh [$context $class]
           (%import &context ?import $context)
           (matche [?import]
             ([[?short ?long]]
                (%resolve-class $context ?long $class)
                (== &type [:object 'java.lang.Class [$class]])))))
      ([[:form/refer ?requires]]
         (fresh [$context]
           (%refer &context ?requires $context)
           (== &type :nil)))
      ([[:form/ns ?name ?options]]
         (fresh [$context $options]
           (%in-ns &context ?name $context)
           (%type-check-all %type-check $context ?options $options)
           (== &type :nil)))
      ([[:form/fn-call ?function ?args]]
         (fresh [$function $function* $args]
           (%type-check $context ?function $function)
           (%type-check-all %type-check $context ?args $args)
           (%as-function $function $function*)
           (%fn-call $function* $args &type)))
      )))

(comment
  ;; Literal types...
  BigInteger
  BigInt
  BigDecimal
  Regex
  )

;; [TODO]
;; IF still doesn't do ocurrence-typing.
;; Add all the missing literal types.
;; When an expression in a fn-call position can't be %as-function, and it's unknown, create a brand-new function for it and set it as it's type.
;; LOAD form
;; ASSERT form
;; pre/post conditions.
;; Metadata.
;; SET!
