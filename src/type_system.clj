(ns type-system
  (:refer-clojure :exclude [==])
  (:require [clojure.template :refer [do-template]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :refer :all]
            [clojure.core.logic.protocols :refer [walk ext-no-check]]))

(declare %as-function
         %union-add)

(alter-var-root #'clojure.core.logic/trace-lvar
                (constantly (fn [a lvar] `(println (format "\t%5s = %s" (str '~lvar) (pr-str (-reify ~a ~lvar)))))))

;; (alter-var-root #'clojure.core/println
;;                 (constantly (fn [& args]
;;                               (.println System/out (apply str args)))))

;; [Utils]
;; (defn %assoc [m k v o]
;;   (matche [m k v o]
;;     ([[] _ _ [[k v]]])
;;     ([[[k v] . _] _ _ m])
;;     ([[[k ?v]] _ _ [[k v]]]
;;        (!= ?v v))
;;     ([[[k ?v] . ?r] _ _ [[k v] . ?r]]
;;        (!= ?r ())
;;        (!= ?v v)
;;        (!= m o))
;;     ([[[?j ?v]] _ _ [[?j ?v] [k v]]]
;;        (!= ?j k))
;;     ([[[?j ?u] . ?r] _ _ [[?j ?u] . ?o]]
;;        (!= ?r ())
;;        (!= ?j k)
;;        (!= m o)
;;        (%assoc ?r k v ?o))))

(defn %assoc [m k v o]
  (matcha [m k v o]
    ;; If there isn't a KV pair, add it.
    ([[] _ _ [[k v]]])
    ;; If you've found a KV pair, return it
    ([[[k v] . _] _ _ m])
    ;; If the value has changed, change the map
    ([[[k ?v] . ?r] _ _ [[k v] . ?r]])
    ;; If this isn't the KV pair, check the next
    ([[[?j ?v] . ?m] _ _ [[?j ?v] . ?o]]
       (%assoc ?m k v ?o))))

(defn %assoc-in [m ks v o]
  (matche [ks]
    ([[?k . ?ks]]
       (conda [(== ?ks [])
               (%assoc m ?k v o)]
              [(!= ?ks [])
               (fresh [$v $v*]
                 (%assoc m ?k $v o)
                 (%assoc-in $v* ?ks v $v))]
              ))
    ))

(defn %assoc-in! [m ks v m*]
  (fn [substs]
    (cond (lvar? v)
          ((== (get-in (walk substs m) (walk substs ks)) v)
           substs)
          
          (lvar? m*)
          ((== (assoc-in (walk substs m) (walk substs ks) v) m*)
           substs)
          
          :else
          (assert false "Invalid use of %assoc-in!"))
    ))

(defn %rebind! [&var &top]
  (fn [substs]
    (let [[_ _ $top $bottom _] (walk substs &var)]
      (-> substs
          (ext-no-check $top &top)))))

(defn %apply! [term f return]
  (fn [substs]
    ((== return (f (-reify substs term))) substs)))

(comment
  (let [+map+ (list [:bar (list [:foo 10])])]
    (run* [&return]
      (%assoc-in +map+ [:yolo :lol] "meme" &return)
      ))

  (let [+map+ (list [:bar (list [:foo 10])])]
    (run* [&return]
      (%assoc-in +map+ [:bar :foo] &return +map+)
      ))
  )

(defn %same-length [l1 l2]
  (matche [l1 l2]
    ([[] []])
    ([[?f1 .  ?r1] [?f2 . ?r2]]
       (%same-length ?r1 ?r2))))

(defn %last [&list &last]
  (matche [&list]
    ([[?prev . ?next]]
       (conda [(== [] ?next)
               (== &last ?prev)]
              [(%last ?next &last)]))
    ))

(defn %in-domain [&lvar &domain]
  (matche [&domain]
    ([[&lvar . ?rest]])
    ([[_ . ?rest]]
       (%in-domain &lvar ?rest))))

;; Function normalization
(defn extract-vars [type]
  (case (nth type 0)
    :function
    (let [[_ arities] type]
      (reduce merge (map extract-vars arities)))
    :arity
    (let [[_ args return] type
          args-vars (reduce merge (map extract-vars args))
          return-vars (extract-vars return)]
      (into (array-map) (for [[k :as kv] return-vars
                              :when (contains? args-vars k)]
                          kv)))
    :?
    (let [[_ _ top bottom id] type]
      (array-map id true))

    :nil
    (array-map)

    :literal
    (array-map)
    
    :object
    (let [[_ _ params] type]
      (reduce merge (map extract-vars params)))

    :union
    (let [[_ types] type]
      (reduce merge (map extract-vars types)))
    ))

(defn substitute-vars [substs type]
  (case (nth type 0)
    :function
    (let [[_ arities] type]
      [:function (map (partial substitute-vars substs) arities)])
    :arity
    (let [[_ args return] type]
      [:arity
       (map (partial substitute-vars substs) args)
       (substitute-vars substs return)])
    :?
    (let [[_ _ top bottom id] type]
      (or (get substs id)
          (if (= [:nothing] bottom)
            top)))

    :nil
    type

    :literal
    type
    
    :object
    (let [[_ class params] type]
      [:object class (mapv (partial substitute-vars substs) params)])

    :union
    (let [[_ types] type]
      [:union (map (partial substitute-vars substs) types)])
    ))

(let [+var-names+ (for [digit (iterate inc 1)
                        letter (seq "abcdefghijklmnopqrstuvwxyz")]
                    (if (= 1 digit)
                      (symbol (str letter))
                      (symbol (str letter digit))))]
  (defn normalize-fn [type]
    (prn 'normalize-fn type)
    (let [vars (extract-vars type)
          names (take (count vars) +var-names+)
          substs (into (array-map) (map vector (-> vars keys reverse) names))
          pretty (substitute-vars substs type)]
      (if (empty? substs)
        pretty
        [:all (-> substs vals distinct vec) pretty])
      )))

;; [Rules]
;; Types
(comment
  [:any]
  [:nothing]
  [:nil]
  [:primitive ?type]
  [:literal ?class ?value]
  [:object ?class ?params]
  [:alias ?params ?type] ;; ???
  [:union ?types]
  [:function ?arities]
  [:multimethod ?dispatcher]
  [:class ?name ?params ?abstract ?constructors ?static-fields ?static-methods ?dynamic-fields ?dynamic-methods]
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

(def +empty-list+ [:object 'clojure.lang.IPersistentList [[:nothing]]])
(def +empty-vector+ [:object 'clojure.lang.IPersistentVector [[:nothing]]])
(def +empty-map+ [:object 'clojure.lang.IPersistentMap [[:nothing] [:nothing]]])
(def +empty-set+ [:object 'clojure.lang.IPersistentSet [[:nothing]]])
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

(defn %class [&object &class]
  (matche [&object]
    ([[:object &class _]])))

;; Solver
(defn %solve-all [%solve &context &expected &actual]
  (matche [&expected &actual]
    ([[] []])
    ([[?e . ?rest] [?a . ?rem]]
       (%solve &context ?e ?a)
       (%solve-all %solve &context ?rest ?rem))
    ))

(letfn [(%helper [%solve &expected &arity]
          (matche [&expected]
            ([[?e-arity . ?rest]]
               (conda [(%solve ?e-arity &arity)]
                      [(%helper %solve ?rest &arity)]))
            ))]
  (defn %solve-arities [%solve &expected &actual]
    (matche [&actual]
      ([[]])
      ([[?a-arity . ?rem]]
         (%helper &expected ?a-arity)
         (%solve-arities &expected ?rem))
      )))

(defn %solve [&context &expected &actual]
  (all (trace-lvars '%solve &expected &actual)
       (matcha [&expected &actual]
         ([_ [:var _ ?type]]
            (%solve &context &expected ?type))
         ([[:any] _])
         ([_ [:nothing]])
         ([[:nil] [:nil]])
         ([[:primitive ?type] [:primitive ?type]])
         ([[:literal ?class ?value] [:literal ?class ?value]])
         ([[:object ?class _] [:literal ?class _]])
         ([[:object ?class ?e-params] [:object ?class ?a-params]]
            (%solve-all %solve &context ?e-params ?a-params))
         ;; ([[:object ?super-class ?e-params] [:object ?sub-class ?a-params]]
         ;;    (fresh [$object]
         ;;      (%as-object ?super-class &actual $object)
         ;;      (%solve &expected $object)))
         ([[:function ?e-arities] [:function ?a-arities]]
            (%solve-arities %solve &context ?e-arities ?a-arities))
         ([[:function ?e-arities] _]
            (fresh [$function]
              (%as-function &context &actual $function)
              (%solve &context &expected $function)))
         ([_ [:union [?type . ?rest]]]
            (%solve &context &expected ?type)
            (conda [(== ?rest [])]
                   [(%solve &context &expected [:union ?rest])]))
         ([[:union [?type . ?rest]] _]
            (conda [(%solve &context ?type &actual)]
                   [(!= ?rest [])
                    (%solve &context [:union ?rest] &actual)]))
         ([[:not ?inner] _]
            (conda [(%solve &context ?inner &actual)
                    u#]
                   [s#]))
         ([[:alias _ ?e] [:alias _ ?a]]
            (%solve &context ?e ?a))
         ([[:alias _ ?type] _]
            (%solve &context ?type &actual))
         ([_ [:alias _ ?type]]
            (%solve &context &expected ?type))
         ([_ [:? _ ?a-top ?a-bottom ?a-id]]
            (conda [(%solve &context &expected ?a-top)]
                   [(%solve &context ?a-top &expected)
                    (%rebind! &actual &expected)]))
         )))

;; Filter
(defn %filter [&context &filter &test &filtered]
  (matche [&test]
    ([[:union [?given . ?rest]]]
       (conda [(%solve &context &filter ?given)
               (conda [(== ?rest [])
                       (== &filtered ?given)]
                      [(!= ?rest [])
                       (fresh [$rest]
                         (conda [(%filter &context &filter [:union ?rest] $rest)
                                 (%union-add &context [:union [?given]] $rest &filtered)]
                                [(== &filtered ?given)])
                         )])]
              [(!= ?rest [])
               (%filter &context &filter [:union ?rest] &filtered)]
              ))
    ))

(comment
  (let [&filter [:not [:union (list [:nil] [:literal/boolean false])]]
        &test [:union (list [:nil] [:object 'java.lang.Long []])]]
    (run* [&return]
      (%filter +new-context+ &filter &test &return)))
  [:object java.lang.Long []]

  (let [&filter [:union (list [:nil] [:literal/boolean false])]
        &test [:union (list [:nil] [:object 'java.lang.Long []])]]
    (run* [&return]
      (%filter +new-context+ &filter &test &return)))
  [:nil]
  )

;; Type-checker
(defmacro with-context [&context goal]
  `(fresh ~'[&global &local
             &aliases &classes
             &imports &refers]
     (== ~&context ~'{:env/global &global :env/local &local
                      :types/aliases &aliases, :types/classes &classes
                      :deps/imports &imports, :deps/refers &refers})
     ~goal))

(def +new-context+ (list [:env/global []]
                         [:env/local []]
                         [:types []]
                         [:types/context []]
                         [:types/aliases []]
                         [:types/classes []]
                         [:deps/imports []]
                         [:deps/refers []]))

(defn %union-add [&context &union &type &new-union]
  (matcha [&union &type]
    ([[:union _] [:union [?type . ?rest]]]
       (conda [(== ?rest [])
               (%union-add &context &union ?type &new-union)]
              [(fresh [$union]
                 (%union-add &context &union ?type $union)
                 (%union-add &context $union [:union ?rest] &new-union))]))
    ([[:union [?ot . ?rest]] _]
       (conda [(%solve &context ?ot &type)
               (== &new-union &union)]
              [(%solve &context &type ?ot)
               (conda [(== ?rest [])
                       (== &new-union [:union [&type]])]
                      [(%union-add &context [:union ?rest] &type &new-union)])]
              [(conda [(== ?rest [])
                       (== &new-union [:union [?ot &type]])]
                      [(fresh [$rest]
                         (%union-add &context [:union ?rest] &type $rest)
                         (matche [$rest]
                           ([[:union ?new-types]]
                              (fresh [$new-types]
                                (conso ?ot ?new-types $new-types)
                                (== &new-union [:union $new-types])))))])]
              ))
    ))

(defn %union [&context &types &union]
  (all (trace-lvars '%union &types)
       (matche [&types]
         ([[?type . ?rest]]
            (conda [(== ?rest [])
                    (== &union ?type)]
                   [(fresh [$sub-union]
                      (%union &context ?rest $sub-union)
                      (matcha [?type]
                        ([[:union _]]
                           (log "IT'S A UNION")
                           (%union-add &context ?type $sub-union &union))
                        ([[?tag . _]]
                           (!= ?tag :union)
                           (log "NOT A UNION")
                           (%union-add &context [:union [?type]] $sub-union &union))
                        ))]
                   ))
         )
       (trace-lvars '%union/return &union)))

(defn %unalias [&context &alias &type]
  (with-context &context
    (%assoc &aliases &alias &type &aliases)))

(let [map-arities (fn [&key-type]
                    (list {:args (list [:object 'clojure.lang.IPersistentMap [&key-type 'v]])
                           :return [:union (list [:nil] 'v)]}
                          {:args (list [:object 'clojure.lang.IPersistentMap [&key-type 'v]]
                                       'v)
                           :return 'v}))
      record-arities (fn [&record-class &slot]
                       (list [:record :map (list [&slot 'v])]
                             [:record &record-class (list [&slot 'v])]))
      kv-arities (fn [&key &val]
                   (list {:args (list &key)
                          :return [:union (list [:nil] &val)]}
                         {:args (list &key &val)
                          :return &val}))]
  (defn %as-function [&context &type &function]
    (matche [&type]
      ([[:literal 'clojure.lang.Keyword ?value]]
         (fresh [?record-class]
           (== &function [:all ['k 'v] [:function (concat (map-arities [:object 'clojure.lang.Keyword []])
                                                          (record-arities ?record-class &type))]])))
      ([[:literal 'clojure.lang.Symbol ?value]]
         (fresh [?record-class]
           (== &function [:all ['k 'v] [:function (concat (map-arities [:object 'clojure.lang.Symbol []])
                                                          (record-arities ?record-class &type))]])))
      ([[:object 'clojure.lang.Keyword []]]
         (== &function [:all ['k 'v] [:function (map-arities &type)]]))
      ([[:object 'clojure.lang.Symbol []]]
         (== &function [:all ['k 'v] [:function (map-arities &type)]]))
      ([[:object 'clojure.lang.IPersistentVector [?elem]]]
         (fresh [$idx]
           (%unalias &context 'alt.typed/AnyInteger $idx)
           (== &function [:function (kv-arities $idx ?elem)])))
      ([[:object 'clojure.lang.IPersistentMap [?key ?val]]]
         (== &function [:function (kv-arities ?key ?val)]))
      ([[:object 'clojure.lang.IPersistentSet [?elem]]]
         (== &function [:function (kv-arities ?elem ?elem)]))
      ([[:function _]]
         (== &function &type))
      )))

;; PHASE 2
(defn %type-check-all [%type-check &context &forms &types &new-context]
  (matche [&forms &types]
    ([[] []]
       (== &new-context &context))
    ([[?form . ?rest] [?type . ?rem]]
       (fresh [$context]
         (%type-check &context ?form ?type $context)
         (%type-check-all %type-check $context ?rest ?rem &new-context)))))

(do-template [<rel> <multi> <finder> <key>]
  (do (defn <rel> [&context &label &type &new-context]
        ;; (%assoc-in &context [<key> &label] &type &new-context)
        (fresh [&original $changed]
          (%assoc &context <key> &original &context)
          (%assoc &original &label &type $changed)
          (%assoc &context <key> $changed &new-context)))
    (defn <multi> [&context &labels &types &new-context]
      (matche [&labels &types]
        ([[] []]
           (== &context &new-context))
        ([[?label . ?rest] [?type . ?rem]]
           (fresh [$context]
             (<rel> &context ?label ?type $context)
             (<multi> $context ?rest ?rem &new-context)))
        ))
    (defn <finder> [&context &label &value]
      (fresh [&data]
        (%assoc &context <key> &data &context)
        (%assoc &data &label &value &data))))

  %with-local    %with-locals    %find-local    :env/local
  %with-global   %with-globals   %find-global   :env/global
  %with-type     %with-types     %find-type     :types
  %with-type-var %with-type-vars %find-type-var :types/context
  )

(defn %type-check-let [%type-check &context &bindings &body &type &new-context]
  (matche [&bindings]
    ([[]]
       (%type-check &context &body &type &new-context))
    ([[?label ?value . ?bindings]]
       (fresh [$value $local $context $context*]
         (%type-check &context ?value $value &context)
         (%with-local &context ?label $value $context)
         (%type-check-let %type-check $context ?bindings &body &type $context*)
         (== &context &new-context)
         ))
    ))

(defn %type-check-recur [%type-check &context &args]
  (with-context &context
    (fresh [$recur $args]
      (%assoc &local :recur $recur &local)
      (%type-check-all &context &args $args)
      (%solve-all %solve $args $recur))))

(defn %type-check-case [%type-check &context &form-type &pairs &type]
  (with-context &context
    (matche [&pairs]
      ([[?else]]
         (%type-check &context ?else &type))
      ([[?match ?expr . ?rest]]
         (fresh [$match $expr]
           (%type-check &context ?match $match)
           (%type-check &context ?expr $expr)
           (conda [(== [] ?rest)
                   (== &type $expr)]
                  [(fresh [$others]
                     (%type-check-case %type-check &context &form-type ?rest $others)
                     (%union-add [:union [$expr]] $others &type))])
           ))
      )))

(defn %init-type-vars [&templates &type-vars]
  (matche [&templates &type-vars]
    ([[] []])
    ([[?template . ?rest] [?var . ?rem]]
       (== ?var [:var ?template])
       (%init-type-vars ?rest ?rem))
    ))

(defn %instance-class [&class &instance]
  (matche [&class]
    ([[:class ?name ?params . _]]
       (fresh [$params]
         (%init-type-vars ?params $params)
         (== &instance [:object ?name $params])))
    ))

(defn %type-check-catch [%type-check &context &catch &type]
  (matche [&catch]
    ([[:catch ?class ?ex . ?body]]
       (fresh [$ex $context $class]
         (%type-check &context ?class $class)
         (matche [$class]
           ([[:class . _]]
              (%instance-class $class $ex)
              (%with-local &context ?ex $ex $context)
              (%type-check &context ?body &type)))
         ))
    ))

(defn %intern-var [&context &var &type &new-context]
  (fresh [&global $global]
    (%assoc &context :env/global &global &context)
    (%assoc &global &var &type $global)
    (%assoc &context :env/global $global &new-context)))

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
  (fresh [$top $bottom $id]
    (== &var [:? &var-name $top $bottom $id])
    (== $top [:any])
    (== $bottom [:nothing])))

(defn %vars [&names &vars]
  (matche [&names &vars]
    ([[] []])
    ([[?name . ?rest] [?var . ?rem]]
       (%var ?name ?var)
       (%vars ?rest ?rem))
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

(defn %type-check-arity [%type-check &context &arity &type &new-context]
  (all (trace-lvars '%type-check-arity &arity &type)
       (matche [&arity &type]
         ([[?args ?body] [:arity ?inputs ?output]]
            (fresh [$context]
              (%with-locals &context ?args ?inputs $context)
              (trace-lvars '%type-check-arity/$context $context)
              (%type-check $context ?body ?output &new-context)))
         )))

(defn %type-check-arities [%type-check &context &arities &types &new-context]
  (all (trace-lvars '%type-check-arities &arities &types)
       (matche [&arities &types]
         ([[] []]
            (== &new-context &context))
         ([[?arity . ?rest] [?type . ?rem]]
            (fresh [$context]
              (%type-check-arity %type-check &context ?arity ?type $context)
              (%type-check-arities %type-check $context ?rest ?rem &new-context)))
         )))

(defn %type-check-fn [%type-check &context &name &arities &type &new-context]
  (all (trace-lvars '%type-check-fn &name &arities)
       (fresh [$types]
         (%arities &arities $types)
         (trace-lvars '%type-check-fn/%arities $types)
         (== &type [:function $types])
         (trace-lvars '%type-check-fn/&type &type)
         (fresh [$context]
           (%with-local &context &name &type $context)
           (%type-check-arities %type-check $context &arities $types &new-context))
         )))

(letfn [(%helper [&context &arities &args &type]
          (all (trace-lvars '%helper &arities &args)
               (matche [&arities]
                 ([[[:arity ?args ?return] . ?rest]]
                    (%solve-all %solve &context ?args &args)
                    (== &type ?return)
                    (trace-lvars '%helper/&type &type))
                 ([[_ . ?rest]]
                    (%helper &context ?rest &args &type)))))]
  (defn %fn-call [&context &function &args &type]
    (all (trace-lvars '%fn-call &function &args)
         (matche [&function]
           ([[:function ?arities]]
              (%helper &context ?arities &args &type))
           ))))

(defn %class-lookup [&context &name &class]
  (with-context &context
    (%assoc &classes &name &class &classes)))

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

(defn %method-call [&context &object|class &method &args &type]
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

(letfn [(%helper [&constructors &args &object]
          (matche [&constructors]
            ([[?ctor . ?rest]]
               (conda [(%fn-call ?ctor &args &object)]
                      [(%helper ?rest &args &object)]))
            ))]
  (defn %ctor-call [&class &args &object]
    (matche [&class]
      ([[:class _ _ ?abstract ?constructors . _]]
         (== ?abstract false)
         (%helper ?constructors &args &object)
         ))))

(defn %in-ns [&context ?name &new-context]
  (with-context &context
    (== &new-context {:ns {:name ?name
                           :refers []
                           :imports []}
                      :env {:global &global
                            :local &local}})))

(defn %import [&context &new-imports &new-context]
  (with-context &context
    (matche [&new-imports]
      ([[]]
         (== &context &new-context))
      ([[[?short ?long] . ?rest]]
         (fresh [$context $name $refers $imports]
           (%assoc &imports ?short ?long $imports)
           (== $context {:ns {:name $name
                              :refers $refers
                              :imports $imports}
                         :env {:global &global
                               :local &local}})
           (%import $context ?rest &new-context))))))

(defn %refer [&context &new-refers &new-context]
  (with-context &context
    (matche [&new-refers]
      ([[]]
         (== &context &new-context))
      ([[?refer . ?rest]]
         (fresh [$context $name $refers $imports]
           (conso ?refer &refers $refers)
           (== $context {:ns {:name $name
                              :refers $refers
                              :imports $imports}
                         :env {:global &global
                               :local &local}})
           (%refer $context ?rest &new-context))))))

(defn %parse-all-types [%parse-type &context &descs &types]
  (matche [&descs &types]
    ([[] []])
    ([[?desc . ?rest] [?type . ?rem]]
       (%parse-all-types %parse-type &context ?rest ?rem)
       (%parse-type &context ?desc ?type))
    ))

(defn %lookup-type [&context &type-name &type]
  (fresh [&types]
    (%assoc &context :types &types &context)
    (%assoc &types &type-name &type &types)))

(defn %type-ctor-call [&context &ctor &args &type]
  (all (trace-lvars (pr-str '%type-ctor-call)
                    &ctor &args)
       (matche [&ctor]
         ([[:ctor/union]]
            (log :ctor/union)
            (%union &context &args &type)
            (trace-lvars '[:ctor/union] &type)))))

(defn %parse-type [&context &type-desc &type]
  (all (trace-lvars (pr-str '%parse-type)
                    &type-desc)
       (matche [&type-desc]
         ([[:form/function ?arities]]
            (!= ?arities [])
            (fresh [$arities]
              (%parse-all-types %parse-type &context ?arities $arities)
              (== &type [:function $arities])))
         ([[:form/arity ?args ?return]]
            (fresh [$args $return]
              (%parse-all-types %parse-type &context ?args $args)
              (%parse-type &context ?return $return)
              (== &type [:arity $args $return])))
         ([[:form/type-name ?name]]
            (conda [(== ?name nil)
                    (== &type [:nil])]
                   [(!= ?name nil)
                    (%lookup-type &context ?name &type)])
            (trace-lvars (pr-str '[:form/type-name ?name])
                         ?name &type)
            (matcha [&type]
              ([[:form/type-ctor . _]]
                 u#)
              ([_]
                 s#)))
         ([[:form/type-ctor ?name ?args]]
            (trace-lvars (pr-str :form/type-ctor)
                         ?name ?args)
            (fresh [$ctor $args]
              (%lookup-type &context ?name $ctor)
              (%parse-all-types %parse-type &context ?args $args)
              (%type-ctor-call &context $ctor $args &type)))
         ([[:all ?args ?inner]]
            (fresh [$context $inner]
              (%with-type-vars &context ?args ?args $context)
              (%parse-type $context ?inner $inner)
              (== &type [:all ?args $inner])))
         ([[:alias ?name ?params ?inner]]
            (fresh [$inner]
              (%parse-type &context ?inner $inner)
              (== &type [:alias ?name ?params $inner])))
         ([[:union [?type . ?rest]]]
            (fresh [$type]
              (%parse-type &context ?type $type)
              (conda [(== ?rest [])
                      (== &type [:union [$type]])]
                     [(!= ?rest [])
                      (fresh [$rest]
                        (%parse-type &context [:union ?rest] $rest)
                        (matche [$rest]
                          ([[:union ?parsed-rest]]
                             (fresh [$full]
                               (conso $type ?parsed-rest $full)
                               (== &type [:union $full])))))])))
         ([_]
            (%find-type-var &context &type-desc &type))
         )))

(defn %type-check [&context &form &type &new-context]
  (all (trace-lvars '%type-check &form)
       (matcha [&form &new-context]
         ([:literal/nil &context]
            (== &type [:nil]))
         ([[:literal/boolean ?value] &context]
            (%simple-literal 'java.lang.Boolean ?value &type))
         ([[:literal/integer ?value] &context]
            (%simple-literal 'java.lang.Long ?value &type))
         ([[:literal/real ?value] &context]
            (%simple-literal 'java.lang.Double ?value &type))
         ([[:literal/character ?value] &context]
            (%simple-literal 'java.lang.Character ?value &type))
         ([[:literal/string ?value] &context]
            (%simple-literal 'java.lang.String ?value &type))
         ([[:literal/keyword ?value] &context]
            (%simple-literal 'clojure.lang.Keyword ?value &type))
         ([[:literal/symbol ?value] &context]
            (%simple-literal 'clojure.lang.Symbol ?value &type))
         ([[:literal/big-int ?value] &context]
            (== &type [:literal 'clojure.lang.BigInt ?value]))
         ([[:literal/big-decimal ?value] &context]
            (== &type [:literal 'java.math.BigDecimal ?value]))
         ([[:literal/regex ?value] &context]
            (== &type [:literal 'java.util.regex.Pattern ?value]))
         ([[:literal/list []] &context]
            (== &type +empty-list+))
         ([[:literal/vector []] &context]
            (== &type +empty-vector+))
         ([[:literal/map []] &context]
            (== &type +empty-map+))
         ([[:literal/set []] &context]
            (== &type +empty-set+))
         ([[:symbol ?symbol] &context]
            (conda [(fresh [&local $type]
                      (%assoc &context :env/local &local &context)
                      (%assoc &local ?symbol &type &local))]
                   [(fresh [&global]
                      (%assoc &context :env/global &global &context)
                      (%assoc &global ?symbol &type &global))]
                   [(fresh [&imports &classes $long]
                      (%assoc &context :deps/imports &imports &context)
                      (%assoc &context :types/classes &classes &context)
                      (%assoc &imports ?symbol $long &imports)
                      (%assoc &classes $long &type &classes))]
                   [(fresh [&imports &classes $short]
                      (%assoc &context :deps/imports &imports &context)
                      (%assoc &context :types/classes &classes &context)
                      (%assoc &imports $short ?symbol &imports)
                      (%assoc &classes ?symbol &type &classes))])
            (trace-lvars '[:symbol ?symbol] &type))
         ([[:form/do . ?body] ?context]
            (fresh [$types]
              (%type-check-all %type-check &context ?body $types ?context)
              (conda [(%last $types &type)]
                     [(== &type [:nil])])))
         ([[:form/letfn ?bindings . ?body] _]
            (log "[SYSTEM ERROR] letfn hasn't been implemented yet.")
            u#)
         ([[:form/let ?bindings ?body] ?context]
            (%type-check-let %type-check &context ?bindings ?body &type ?context))
         ([[:form/if ?test ?then ?else] &context]
            (let [+falsey+ [:union (list [:nil] [:literal/boolean false])]
                  +truthy+ [:not +falsey+]]
              (fresh [$test $test-then $test-else]
                (%type-check &context ?test $test &context)
                (trace-lvars 'if/$test $test)
                (conda [(%filter &context +truthy+ $test $test-then)
                        (%type-check &context ?then &type &context)]
                       [(%filter &context +falsey+ $test $test-else)
                        (%type-check &context ?else &type &context)]
                       [(fresh [$then $else]
                          (%type-check &context ?then $then &context)
                          (%type-check &context ?else $else &context)
                          (%union &context [$then $else] &type))])
                ;; (fresh [$test-then $context-then]
                ;;   (matcha [?test]
                ;;     ([[:symbol ?symbol]]
                ;;        (%filter &context +truthy+ $test $test-then)
                ;;        (%with-local &context ?symbol $test-then $context-then)
                ;;        (%type-check $context-then ?then $then $context-then))
                ;;     ([_]
                ;;        (%type-check &context ?then $then &context))))
                ;; (fresh [$test-else $context-else]
                ;;   (matcha [?test]
                ;;     ([[:symbol ?symbol]]
                ;;        (%filter &context +falsey+ $test $test-else)
                ;;        (%with-local &context ?symbol $test-else  $context-else)
                ;;        (%type-check $context-else ?else $else $context-else))
                ;;     ([_]
                ;;        (%type-check &context ?else $else &context))))
                ;; (%union &context [$then $else] &type)
                )))
         ([[:form/case ?form . ?pairs] _]
            (fresh [$form]
              (%type-check &context ?form $form)
              (%type-check-case %type-check &context $form ?pairs &type)))
         ([[:form/loop ?bindings ?body] _]
            (fresh [$recur &local $local $context]
              (%assoc &context :env/local &local &context)
              (%type-check-loop-bindings %type-check &context ?bindings $recur)
              (%assoc &local :recur $recur $local)
              (%assoc &context :env/local $local $context)
              (%type-check $context ?body &type)))
         ([[:form/fn ?name ?arities] ?context]
            (fresh [$fn]
              (%type-check-fn %type-check &context ?name ?arities $fn ?context)
              (%apply! $fn normalize-fn &type)))
         ([[:form/def ?var] ?context]
            (fresh [$global]
              (%intern-var &context ?var [:nothing] ?context)
              (== &type [:object 'clojure.lang.Var [[:nothing]]])))
         ([[:form/def ?var ?value] ?context]
            (fresh [$global $value $context]
              (%type-check &context ?value $value $context)
              (%intern-var $context ?var $value ?context)
              (== &type [:object 'clojure.lang.Var [$value]])))
         ([[:form/var ?var] &context]
            (fresh [&global $var-type]
              (%assoc &context :env/global &global &context)
              (%assoc &global ?var $var-type &global)
              (== &type [:object 'clojure.lang.Var [$var-type]])))
         ([[:form/dot ?object|class ?field|method] _]
            (fresh [$object|class]
              (%type-check &context ?object|class $object|class)
              (conda [(%field-read &context $object|class ?field|method &type)]
                     [(%method-call &context $object|class ?field|method [] &type)])))
         ([[:form/dot ?object|class [?method ?args]] _]
            (fresh [$object|class]
              (%type-check &context ?object|class $object|class)
              (%method-call &context $object|class ?method ?args &type)))
         ([[:form/new ?class ?args] _]
            (fresh [$class]
              (fresh [$args]
                (%type-check-all %type-check &context ?args $args)
                (%type-check &context ?class $class)
                (%ctor-call $class $args &type))))
         ([[:form/gen-class ?options] _]
            (log "[SYSTEM ERROR] gen-class hasn't been implemented yet.")
            u#)
         ([[:form/defprotocol ?name ?method-defs] _]
            (log "[SYSTEM ERROR] defprotocol hasn't been implemented yet.")
            u#
            ;; (fresh [$protocol]
            ;;   (%type-check-defprotocol &context ?method-defs $protocol)
            ;;   (%simple-literal 'clojure.lang.Symbol ?name &type))
            )
         ([[:form/deftype ?name ?fields ?impls] _]
            (log "[SYSTEM ERROR] deftype hasn't been implemented yet.")
            u#
            ;; (fresh [$type $object]
            ;;   (%type-check-deftype &context ?fields ?impls $type)
            ;;   (%instance-class $type $object nil)
            ;;   (== &type [:object 'java.lang.Class [$object]]))
            )
         ([[:form/defrecord ?name ?fields ?impls] _]
            (log "[SYSTEM ERROR] defrecord hasn't been implemented yet.")
            u#
            ;; (fresh [$type $object]
            ;;   (%type-check-defrecord &context ?fields ?impls $type)
            ;;   (%instance-class $type $object nil)
            ;;   (== &type [:object 'java.lang.Class [$object]]))
            )
         ([[:form/reify ?impls] _]
            (log "[SYSTEM ERROR] reify hasn't been implemented yet.")
            u#
            ;; (fresh [$type]
            ;;   (%type-check-reify &context ?impls &type))
            )
         ([[:form/proxy] _]
            (log "[SYSTEM ERROR] proxy hasn't been implemented yet.")
            u#
            ;; (fresh [$type]
            ;;   (%type-check-proxy &context ?impls &type))
            )
         ([[:form/defmulti ?name ?dispatcher] _]
            (log "[SYSTEM ERROR] defmulti hasn't been implemented yet.")
            u#
            ;; (fresh [$dispatcher $context]
            ;;   (%type-check &context ?dispatcher $dispatcher)
            ;;   (== &type [:multimethod $dispatcher])
            ;;   (%intern-var $context ?name &type &context))
            )
         ([[:form/defmethod ?name ?dispatch-val ?args ?body] _]
            (log "[SYSTEM ERROR] defmethod hasn't been implemented yet.")
            u#
            ;; (fresh [$multi $args $body]
            ;;   (%resolve &context ?name $multi)
            ;;   (%multimethod-args &context $multi ?args $args)
            ;;   (%type-check-body %type-check &context ?body &type))
            )
         ([[:form/throw ?ex] _]
            (fresh [$ex]
              (%type-check &context ?ex $ex)
              (conda [(%solve +throwable+ $ex)
                      (== &type [:nothing])]
                     [(log "[ERROR] Must throw a java.lang.Throwable.")
                      u#])))
         ([[:form/try ?body ?catches ?finally] _]
            (fresh [$body $catches $finally $all]
              (%type-check &context ?body $body)
              (%type-check-all (partial %type-check-catch %type-check) &context ?catches $catches)
              (%type-check &context ?finally $finally)
              (conso $body $catches $all)
              (%union $all &type)))
         ([[:form/binding ?bindings ?body] _]
            (log "[SYSTEM ERROR] binding hasn't been implemented yet.")
            u#
            ;; (%type-check-binding &context ?bindings)
            ;; (%type-check-body %type-check &context ?body &type)
            )
         ([[:form/recur ?args] _]
            (%type-check-recur %type-check &context ?args)
            (== &type [:nothing]))
         ([[:form/import ?import] _]
            (fresh [$context $class]
              (%import &context ?import $context)
              (matche [?import]
                ([[?short ?long]]
                   (== &type [:object 'java.lang.Class [?long]])))))
         ([[:form/refer ?requires] _]
            (fresh [$context]
              (%refer &context ?requires $context)
              (== &type [:nil])))
         ([[:form/ns ?name ?options] _]
            (fresh [$context $options]
              (%in-ns &context ?name $context)
              (%type-check-all %type-check $context ?options $options)
              (== &type [:nil])))
         ([[:form/fn-call ?function ?args] ?context]
            (fresh [$function $function* $args
                    $context]
              (%type-check &context ?function $function $context)
              (%type-check-all %type-check &context ?args $args ?context)
              (%as-function ?context $function $function*)
              (%fn-call &context $function* $args &type)))
         ([[:form/ann ?var ?type-desc] ?context]
            (trace-lvars '[:form/ann ?var ?type-desc] ?var ?type-desc)
            (fresh [$type]
              (%parse-type &context ?type-desc $type)
              (%with-global &context ?var $type ?context)
              (== &type [:nil])))
         ([[:form/defalias [?alias . ?params] ?type-def] ?context]
            (conda [(== ?params [])
                    (fresh [$type]
                      (%parse-type &context ?type-def $type)
                      (%with-type &context ?alias $type ?context))]
                   [(!= ?params [])
                    (fresh [$type-def $type]
                      (== $type-def [:all ?params
                                     [:alias ?alias ?params
                                      ?type-def]])
                      (%parse-type &context $type-def $type)
                      (%with-type &context ?alias $type ?context))]
                   )
            (== &type [:nil]))
         )))

(comment
  (defn try-form
    ([form]
       (let [results (run* [&type &context]
                       (%type-check +new-context+ form &type &context))]
         (prn '(count results) (count results))
         (assert (= 1 (count results)))
         (let [[[type context]] results]
           (prn 'context context)
           type)))
    ([locals form]
       (let [locals* (for [[label type] locals] [label type])
             results (run* [&type &context]
                       (fresh [$context]
                         (%assoc +new-context+ :env/local locals* $context)
                         (%type-check $context form &type &context)))]
         (prn '(count results) (count results))
         ;; (assert (= 1 (count results)))
         (mapv (comp prn first) results)
         (let [[[type context]] results]
           ;; (prn 'context context)
           type)
         )))

  (defn try-form+
    ([context form]
       (let [results (run* [&type &context]
                       (%type-check context form &type &context))]
         (assert (== 1 (count results)))
         (let [[[type context]] results]
           (prn 'context context)
           type))))

  (do (assert (= [:nil]
                 (try-form :literal/nil)))
    (assert (= [:literal 'java.lang.Boolean true]
               (try-form [:literal/boolean true])))
    (assert (= [:literal 'java.lang.Long 10]
               (try-form [:literal/integer 10])))
    (assert (= [:literal 'java.lang.Double 10.0]
               (try-form [:literal/real 10.0])))
    (assert (= [:literal 'java.lang.Character \a]
               (try-form [:literal/character \a])))
    (assert (= [:literal 'java.lang.String "YOLO"]
               (try-form [:literal/string "YOLO"])))
    (assert (= [:literal 'clojure.lang.Keyword :lol]
               (try-form [:literal/keyword :lol])))
    (assert (= [:literal 'clojure.lang.Symbol 'meme]
               (try-form [:literal/symbol 'meme])))
    (assert (= [:literal 'clojure.lang.BigInt 10N]
               (try-form [:literal/big-int 10N])))
    (assert (= [:literal 'java.math.BigDecimal 10M]
               (try-form [:literal/big-decimal 10M])))
    (assert (let [regex #"yolo"]
              (= [:literal 'java.util.regex.Pattern regex]
                 (try-form [:literal/regex regex]))))
    (assert (= [:object 'clojure.lang.IPersistentList [[:nothing]]]
               (try-form [:literal/list []])))
    (assert (= [:object 'clojure.lang.IPersistentVector [[:nothing]]]
               (try-form [:literal/vector []])))
    (assert (= [:object 'clojure.lang.IPersistentMap [[:nothing] [:nothing]]]
               (try-form [:literal/map []])))
    (assert (= [:object 'clojure.lang.IPersistentSet [[:nothing]]]
               (try-form [:literal/set []])))
    (assert (= [:nil]
               (try-form [:form/do :literal/nil])))
    (assert (= [:object 'clojure.lang.Var [[:nothing]]]
               (try-form [:form/def 'foo])))
    (assert (= [:object 'clojure.lang.Var [[:nil]]]
               (try-form [:form/def 'foo [:form/do :literal/nil]])))
    (assert (= [:nil]
               (try-form [:form/let ['foo :literal/nil]
                          [:form/do
                           :literal/nil]])))
    (assert (= [:nil]
               (try-form [:form/let ['foo :literal/nil]
                          [:form/do
                           [:symbol 'foo]]])))
    (assert (= [:nil]
               (try-form [:form/do
                          [:form/def 'foo :literal/nil]
                          [:symbol 'foo]])))
    (assert (= [:object 'clojure.lang.Var [[:nil]]]
               (try-form [:form/do
                          [:form/def 'foo :literal/nil]
                          [:form/var 'foo]])))
    (assert (= [:union (list [:nil] [:object 'java.lang.Long []])]
               (try-form {'parse-int [:function (list [:arity
                                                       (list [:object 'java.lang.String []])
                                                       [:union (list [:nil] [:object 'java.lang.Long []])]])]}
                         [:form/fn-call [:symbol 'parse-int] (list [:literal/string "1234"])])))
    (assert (= [:union (list [:object 'java.lang.Long []] [:literal 'java.lang.String "YOLO"])]
               (try-form {'parse-int [:function (list [:arity
                                                       (list [:object 'java.lang.String []])
                                                       [:union (list [:nil] [:object 'java.lang.Long []])]])]}
                         [:form/let ['result [:form/fn-call [:symbol 'parse-int] (list [:literal/string "1234"])]]
                          [:form/do
                           [:form/if [:symbol 'result]
                            [:symbol 'result]
                            [:literal/string "YOLO"]]
                           ]])))
    (let [+new-context+ (list [:env/global []]
                              [:env/local []]
                              [:types (list ['java.lang.String [:object 'java.lang.String []]]
                                            ['java.lang.Long [:object 'java.lang.Long []]]
                                            ['alt.typed/Or [:ctor/union]])]
                              [:types/aliases []]
                              [:types/classes []]
                              [:deps/imports []]
                              [:deps/refers []])]
      (assert (= [:union [[:nil] [:object 'java.lang.Long []]]]
                 (try-form+ +new-context+
                            [:form/do
                             [:form/ann 'parse-int
                              [:form/function (list [:form/arity
                                                     (list [:form/type-name 'java.lang.String])
                                                     [:form/type-ctor 'alt.typed/Or (list [:form/type-name nil]
                                                                                          [:form/type-name 'java.lang.Long])]])]]
                             [:form/fn-call [:symbol 'parse-int] (list [:literal/string "1234"])]]))))
    (assert (= [:nil]
               (try-form [:form/defalias ['Maybe 'x]
                          [:union (list [:form/type-name nil] 'x)]])))
    (assert (= '[:all [a] [:function ([:arity (a) a])]]
               (try-form [:form/fn 'foo
                          (list [['x]
                                 [:form/do [:symbol 'x]]])])))
    (assert (= '[:function ([:arity ([:object java.lang.String []]) [:union ([:nil] [:object java.lang.Long []])]])]
               (try-form {'parse-int [:function (list [:arity
                                                       (list [:object 'java.lang.String []])
                                                       [:union (list [:nil] [:object 'java.lang.Long []])]])]}
                         [:form/fn 'foo
                          (list [['x]
                                 [:form/fn-call [:symbol 'parse-int] (list [:symbol 'x])]])])))
    )
  
  (try-form {'long? [:function (list [:arity
                                      (list [:object 'java.lang.Long []])
                                      [:literal 'java.lang.Boolean true]]
                                     [:arity
                                      (list [:not [:object 'java.lang.Long []]])
                                      [:literal 'java.lang.Boolean false]])]}
            [:form/fn 'foo
             (list [['x]
                    [:form/if [:form/fn-call [:symbol 'long?] (list [:symbol 'x])]
                     [:symbol 'x]
                     [:literal/string "YOLO"]]]
                   )])

  [:function ([:arity ([:? x [:object java.lang.Long []] [:nothing] _0])
               [:union [[:? x [:object java.lang.Long []] [:nothing] _0]
                        [:literal java.lang.String "YOLO"]]]])]

  (fn foo [x]
    (if (long? x)
      x
      "YOLO"))

  [:all [a] [:function ([:arity (a) [:union (a [:literal java.lang.String "YOLO"])]])]]

  (Fn [Long -> Long]
      [(Not Long) -> "YOLO"])

  [:function ([:arity ([:? x [:any] [:nothing] _0])
               [:union ([:nil] [:object java.lang.Long []])]])]

  [:function ([:arity ([:? x [:object java.lang.String []] [:nothing] _0])
               [:union ([:nil] [:object java.lang.Long []])]])]

  [:function ([:arity ([:? x [:object java.lang.String []] [:nothing] _0])
               [:union ([:nil] [:object java.lang.Long []])]])]

  [:all [a] [:function ([:arity (a) [:union (a [:literal java.lang.String "YOLO"])]])]]
  [:function ([:arity ([:literal java.lang.String "YOLO"]) [:union ([:literal java.lang.String "YOLO"])]])]
  [:function ([:arity ([:literal java.lang.String "YOLO"]) [:union ([:literal java.lang.String "YOLO"])]])]

  )

;; (defn %map! [f &inputs &outputs]
;;   (matcha [&inputs &outputs]
;;     ([[] []])
;;     ([[?in . ?ins] [?out . ?outs]]
;;        (f ?in ?out)
;;        (%map! f ?ins ?outs))
;;     ))

;; (defn %type-syntax! [&type &syntax]
;;   (matche [&type]
;;     ([[:function ?arities]]
;;        (fresh [$arities]
;;          (%map! %type-syntax! ?arities $arities)
;;          (conso 'Fn $arities &syntax)))
;;     ))

;; [TODO]
;; IF still doesn't do ocurrence-typing.
;; When an expression in a fn-call position can't be %as-function, and it's unknown, create a brand-new function for it and set it as it's type.
;; LOAD form
;; ASSERT form
;; pre/post conditions.
;; Metadata.
;; SET!
