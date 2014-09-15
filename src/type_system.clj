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

(defn %boolean [&boolean]
  (matche [&boolean]
    ([true])
    ([false])))

(defn %last [&list &last]
  (matche [&list]
    ([[]]
       (== &last nil))
    ([[&last]])
    ([[?prev . ?next]]
       (%last ?next &last))))

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

;; Type-checker
(defmacro with-context [&context goal]
  `(fresh ~'[&global &local]
     (== ~&context {:env/global ~'&global :env/local ~'&local})
     ~goal))

(defn %context [&context]
  (fresh [$global $local]
    (== &context {:env/global $global :env/local $local})))

(defn %type-check [&context &form &type]
  (with-context &context
    (matche [&form]
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
      ([[:form/do ?body]]
         (%type-check-body &context ?body &type))
      ([[:form/letfn ?bindings ?body]]
         (%type-check-letfn &context %type-check ?bindings)
         (%type-check-body &context ?body &type))
      ([[:form/let ?bindings ?body]]
         (%type-check-let &context %type-check ?bindings)
         (%type-check-body &context ?body &type))
      ([[:form/if ?test ?then ?else]]
         (fresh [$test $then $else]
           (%type-check &context ?test $test)
           (%type-check &context ?then $then)
           (%type-check &context ?else $else)
           (%union [$then $else] &type)))
      ([[:form/case ?pairs]]
         (%type-check-case &context ?pairs &type))
      ([[:form/loop ?bindings ?body]]
         (fresh [$context $recur $local]
           (%type-check-loop-bindings %type-check &context ?bindings $recur)
           (%assoc $local :recur $recur &local)
           (%type-check-body &context ?body &type)))
      ([[:form/fn ?name ?arities]]
         (fresh [$arities]
           (%type-check-arities &context ?arities ?name $arities)
           (== &type [:function $arities])))
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
             ([[:class _ _ ?constructors _ _ _ _]]
                (%new ?constructors ?args &type)))))
      ([[:form/gen-class ?options]]
         (log! "[SYSTEM ERROR] gen-class hasn't been implemented yet.")
         u#)
      ([[:form/defprotocol ?name ?method-defs]]
         (fresh [$protocol]
           (%type-check-defprotocol &context ?method-defs $protocol)
           (%simple-literal 'clojure.lang.Symbol ?name &type)))
      ([[:form/deftype ?name ?fields ?impls]]
         (fresh [$type $object]
           (%type-check-deftype &context ?fields ?impls $type)
           (%instance-class $type $object nil)
           (== &type [:object 'java.lang.Class [$object]])))
      ([[:form/defrecord ?name ?fields ?impls]]
         (fresh [$type $object]
           (%type-check-defrecord &context ?fields ?impls $type)
           (%instance-class $type $object nil)
           (== &type [:object 'java.lang.Class [$object]])))
      ([[:form/reify ?impls]]
         (fresh [$type]
           (%type-check-reify &context ?impls &type)))
      ([[:form/proxy]]
         (fresh [$type]
           (%type-check-proxy &context ?impls &type)))
      ([[:form/defmulti ?name ?dispatcher]]
         (fresh [$dispatcher $context]
           (%type-check &context ?dispatcher $dispatcher)
           (== &type [:multimethod $dispatcher])
           (%intern-var $context ?name &type &context)))
      ([[:form/defmethod ?name ?dispatch-val ?args ?body]]
         (fresh [$multi $args $body]
           (%resolve &context ?name $multi)
           (%multimethod-args &context $multi ?args $args)
           (%type-check-body &context ?body &type)))
      ([[:form/throw ?ex]]
         (fresh [$ex]
           (%type-check &context ?ex $ex)
           (conde [(%solve +throwable+ $ex)
                   (== &type :nothing)]
                  [(log! "[ERROR] Must throw a java.lang.Throwable.")
                   u#])))
      ([[:form/try ?forms]]
         (%type-check-try &context ?forms &type))
      ;; ([[:form/catch ]])
      ;; ([[:form/finally ]])
      ([[:form/binding ?bindings ?body]]
         (%type-check-binding &context ?bindings)
         (%type-check-body &context ?body &type))
      ([[:form/recur ?args]]
         (%type-check-recur &context ?args)
         (== &type :nothing))
      ([[:form/import ?imports]]
         (fresh [$ns]
           (%import-all $ns ?imports &ns)))
      ([[:form/require ?requires]]
         (fresh [$refers]
           (%require-all $refers ?requires &refers)))
      ([[:form/use ?uses]]
         (fresh [$refers]
           (%use-all $refers ?uses &refers)))
      ([[:form/ns ?name ?options]]
         (fresh [$context $options]
           (%in-ns ?name &context $context)
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
