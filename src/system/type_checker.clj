(ns system.type-checker
  (:require [clojure.set :as set]
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]]
                    [env :as &env]
                    [type :as &type]
                    [parser :as &parser]))
  (:import (system.env Env)))

;; [Data]
(defrecord Context [env types])

;; [Utils]
(defn ^:private clean-env [to-clean type]
  ;; (prn 'clean-env to-clean type)
  (match type
    [::&type/bound _]
    (exec state-seq-m
      [=type (&util/with-field* :types
               (&type/deref-binding type))
       =type (clean-env to-clean =type)
       _ (&util/with-field* :types
           (&type/update-binding type =type))]
      (return state-seq-m (if (contains? to-clean type)
                            =type
                            type)))

    [::&type/var _]
    (exec state-seq-m
      [[=top =bottom] (&util/with-field* :types
                        (&type/deref-var type))
       =top (clean-env to-clean =top)
       =bottom (clean-env to-clean =bottom)
       _ (&util/with-field* :types
           (&type/update-var type =top =bottom))]
      (return state-seq-m type))

    [::&type/object ?class ?params]
    (exec state-seq-m
      [=params (map-m state-seq-m (partial clean-env to-clean) ?params)]
      (return state-seq-m [::&type/object ?class =params]))

    
    [::&type/union ?types]
    (exec state-seq-m
      [=types (map-m state-seq-m (partial clean-env to-clean) ?types)]
      (return state-seq-m [::&type/union =types]))

    
    [::&type/complement ?type]
    (exec state-seq-m
      [=type (clean-env to-clean ?type)]
      (return state-seq-m [::&type/complement =type]))
    
    :else
    (return state-seq-m type)))

(defn with-env [env inner]
  ;; (prn `with-env env)
  (exec state-seq-m
    [_ (&util/with-field :env
         (&env/enter env))
     =type* inner
     bound-ids (&util/with-field :env
                 (fn [^Env state]
                   ;; (prn 'bound-ids/state state)
                   [state (-> state .-stack first vals set)]))
     ;; :let [_ (prn 'bound-ids bound-ids)]
     =type (clean-env bound-ids =type*)
     _ (&util/with-field :env
         &env/exit)]
    (return state-seq-m =type)))

(defn ^:private clean [type]
  (match type
    [::&type/bound _]
    (exec state-seq-m
      [=type (&util/with-field* :types
               (&type/deref-binding type))]
      (clean =type))

    [::&type/var _]
    (exec state-seq-m
      [[=top =bottom] (&util/with-field* :types
                        (&type/deref-var type))]
      (clean =top))
    
    :else
    (return state-seq-m type)))

(defn ^:private extract-vars [type]
  (match type
    [::&type/bound _]
    (exec state-seq-m
      [=type (&util/with-field* :types
               (&type/deref-binding type))]
      (extract-vars =type))
    
    [::&type/var _]
    (return state-seq-m (list type))

    [::&type/object _ ?params]
    (map-m state-seq-m extract-vars ?params)

    [::&type/union ?types]
    (map-m state-seq-m extract-vars ?types)

    [::&type/complement ?type]
    (extract-vars ?type)
    
    :else
    (return state-seq-m '())))

(defn ^:private prettify-type [mappings type]
  (match type
    [::&type/bound _]
    (exec state-seq-m
      [=type (&util/with-field* :types
               (&type/deref-binding type))]
      (prettify-type mappings =type))
    
    [::&type/var _]
    (if-let [var-name (get mappings type)]
      (return state-seq-m var-name)
      (exec state-seq-m
        [[=top =bottom] (&util/with-field* :types
                          (&type/deref-var type))]
        (prettify-type mappings =top)))

    [::&type/object ?class ?params]
    (exec state-seq-m
      [=params (map-m state-seq-m (partial prettify-type mappings) ?params)]
      (return state-seq-m [::&type/object ?class =params]))

    [::&type/union ?types]
    (exec state-seq-m
      [=types (map-m state-seq-m (partial prettify-type mappings) ?types)]
      (return state-seq-m [::&type/union =types]))

    [::&type/complement ?type]
    (exec state-seq-m
      [=type (prettify-type mappings ?type)]
      (return state-seq-m [::&type/complement =type]))

    [::&type/arity ?args ?body]
    (exec state-seq-m
      [=args (map-m state-seq-m (partial prettify-type mappings) ?args)
       =body (prettify-type mappings ?body)]
      (return state-seq-m [::&type/arity =args =body]))
    
    :else
    (return state-seq-m type)))

(let [+var-names+ (for [idx (iterate inc 1)
                        alphabet "abcdefghijklmnopqrstuvwxyz"]
                    (if (= 1 idx)
                      (symbol (str alphabet))
                      (symbol (str alphabet idx))))]
  (defn ^:private generalize-arity [arity]
    ;; (prn 'generalize-arity arity)
    (match arity
      [::&type/arity ?args ?body]
      (exec state-seq-m
        [body-vars* (extract-vars ?body)
         args-vars* (map-m state-seq-m extract-vars ?args)
         :let [body-vars (set body-vars*)
               args-vars (set (apply concat args-vars*))
               poly-vars (set/intersection args-vars body-vars)
               used-vars (take (count poly-vars) +var-names+)
               mappings (into {} (map vector (seq poly-vars) used-vars))
               ;; _ (prn 'generalize-arity/vars body-vars args-vars poly-vars mappings)
               ]
         arity* (prettify-type mappings arity)
         ;; :let [_ (prn '(prettify-type mappings arity) arity*)]
         ]
        (return state-seq-m (if (empty? used-vars)
                              arity*
                              [::&type/all (vec used-vars) arity*])))
      )))

(defn ^:private classify [worlds]
  (if (empty? worlds)
    zero
    (let [[[state type :as world] & others] worlds
          [take leave] (reduce (fn [[take leave] [state* _ :as pair]]
                                 (if (= state state*)
                                   [(conj take pair) leave]
                                   [take (conj leave pair)]))
                               [[world] []]
                               others)]
      #(let [classification (if (= 1 (count take))
                              (list [% type])
                              (list [% [::&type/union (map second take)]]))]
         (concat classification ((classify leave) %))))))

(defn ^:private merge-arities [worlds]
  (if (empty? worlds)
    zero
    (let [[[state arity :as world] & others] worlds
          [taken left] (reduce (fn [[taken left] [state* arity* :as world*]]
                                 (match [arity arity*]
                                   [[::&type/arity ?args ?body] [::&type/arity ?args* ?body*]]
                                   (if (= ?args ?args*)
                                     [(conj taken world*) left]
                                     [taken (conj left world*)])))
                               [[world] []]
                               others)]
      (fn [state]
        (let [batch (if (= 1 (count taken))
                      (list [state (-> taken first (nth 1))])
                      (list [state (let [returns [::&type/union (map #(-> % (nth 1) (nth 2)) taken)]]
                                     (-> taken first (nth 1) (assoc-in [2] returns)))]))]
          (concat batch ((merge-arities left) state))))
      )))

(defn ^:private refine-local [local type]
  ;; (prn 'refine-local local type)
  (match type
    [::&type/union ?types]
    (exec state-seq-m
      [=type (return-all ?types)
       _ (&util/parallel [(&util/with-field* :types
                            (&type/solve &type/+truthy+ =type))
                          (&util/with-field* :types
                            (&type/solve &type/+falsey+ =type))
                          (&util/with-field* :types
                            (&type/solve [::&type/any] =type))])
       _ (&util/with-field* :types
           (&type/update-binding local =type))]
      (return state-seq-m =type))
    
    [::&type/object 'java.lang.Boolean []]
    (exec state-seq-m
      [=type (return-all (list [::&type/literal java.lang.Boolean true]
                               [::&type/literal java.lang.Boolean false]))
       _ (&util/with-field* :types
           (&type/update-binding local =type))]
      (return state-seq-m =type))

    :else
    (return state-seq-m type)
    ))

(defn ^:private refine [check* form]
  ;; (prn 'refine form)
  (exec state-seq-m
    [=form (check* form)
     state &util/get-state
     ;; :let [_ (prn 'refine/=form =form 'state state)]
     _ (match =form
         [::&type/bound _]
         (exec state-seq-m
           [=type (&util/with-field* :types
                    (&type/deref-binding =form))
            _ (refine-local =form =type)]
           (return state-seq-m true))

         :else
         (return state-seq-m true))]
    (return state-seq-m =form)))

(defn ^:private check-arity [=arity =args]
  ;; (prn 'check-arity =arity =args)
  (match =arity
    [::&type/arity ?args ?return]
    (exec state-seq-m
      [_ (map-m state-seq-m
                (fn [[arg input]]
                  (&util/with-field* :types
                    (&type/solve arg input)))
                (map vector ?args =args))]
      (return state-seq-m ?return))))

(defn ^:private fn-call [=fn =args]
  ;; (prn 'fn-call =fn =args)
  (match =fn
    [::&type/function ?arities]
    (exec state-seq-m
      [=arity (return-all (for [[_ args _ :as arity] ?arities
                                :when (= (count args) (count =args))]
                            arity))]
      (check-arity =arity =args))))

(defn check* [form]
  ;; (prn 'check* form)
  (match form
    [::&parser/#nil]
    (return state-seq-m [::&type/nil])
    
    [::&parser/#boolean ?value]
    (return state-seq-m [::&type/literal 'java.lang.Boolean ?value])

    [::&parser/#integer ?value]
    (return state-seq-m [::&type/literal 'java.lang.Long ?value])

    [::&parser/#real ?value]
    (return state-seq-m [::&type/literal 'java.lang.Double ?value])

    [::&parser/#big-int ?value]
    (return state-seq-m [::&type/literal 'clojure.lang.BigInt ?value])

    [::&parser/#big-decimal ?value]
    (return state-seq-m [::&type/literal 'java.math.BigDecimal ?value])

    [::&parser/#ratio ?value]
    (return state-seq-m [::&type/literal 'clojure.lang.Ratio ?value])

    [::&parser/#character ?value]
    (return state-seq-m [::&type/literal 'java.lang.Character ?value])

    [::&parser/#string ?value]
    (return state-seq-m [::&type/literal 'java.lang.String ?value])

    [::&parser/#regex ?value]
    (return state-seq-m [::&type/literal 'java.util.regex.Pattern ?value])

    [::&parser/#keyword ?value]
    (return state-seq-m [::&type/literal 'clojure.lang.Keyword ?value])

    [::&parser/#vector ?value]
    (if (empty? ?value)
      (return state-seq-m [::&type/object 'clojure.lang.IPersistentVector [[::&type/nothing]]])
      (exec state-seq-m
        [=members (map-m state-seq-m check* ?value)]
        (return state-seq-m [::&type/object 'clojure.lang.IPersistentVector [[::&type/union =members]]])))

    [::&parser/#map ?value]
    (if (empty? ?value)
      (return state-seq-m [::&type/object 'clojure.lang.IPersistentMap [[::&type/nothing] [::&type/nothing]]])
      (exec state-seq-m
        [=members (map-m state-seq-m check* (seq ?value))
         :let [[=k =v] (reduce (fn [[ks vs] [k v]]
                                 [(conj ks k) (conj vs v)])
                               [[] []]
                               (partition 2 =members))]]
        (return state-seq-m [::&type/object 'clojure.lang.IPersistentMap [[::&type/union =k] [::&type/union =v]]])))

    [::&parser/#set ?value]
    (if (empty? ?value)
      (return state-seq-m [::&type/object 'clojure.lang.IPersistentSet [[::&type/nothing]]])
      (exec state-seq-m
        [=members (map-m state-seq-m check* ?value)]
        (return state-seq-m [::&type/object 'clojure.lang.IPersistentSet [[::&type/union =members]]])))
    
    [::&parser/symbol ?symbol]
    (&util/with-field :env
      (fn [state]
        ;; (prn [::&parser/symbol ?symbol] state)
        ((&env/resolve ?symbol) state)))

    [::&parser/do & ?forms]
    (case (count ?forms)
      0 (return state-seq-m [::&type/nil])
      1 (check* (first ?forms))
      ;; else
      (exec state-seq-m
        [=forms (map-m state-seq-m check* ?forms)]
        (return state-seq-m (last =forms))))
    
    [::&parser/let ([[?label ?value] & ?bindings] :seq) ?body]
    (exec state-seq-m
      [=value (check* ?value)
       =binding (&util/with-field* :types
                  (&type/bind =value))
       ;; :let [_ (prn ::&parser/let '=binding =binding)]
       ]
      (with-env {?label =binding}
        (if (empty? ?bindings)
          (check* ?body)
          (check* [::&parser/let ?bindings ?body]))))

    [::&parser/if ?test ?then ?else]
    (exec state-seq-m
      [=test (refine check* ?test)
       ;; :let [_ (prn ::&parser/if '=test =test)]
       ]
      (&util/parallel [(exec state-seq-m
                         [_ (&util/with-field* :types
                              (&type/solve &type/+truthy+ =test))
                          ;; :let [_ (prn ::&parser/if 'THEN)]
                          ]
                         (check* ?then))
                       (exec state-seq-m
                         [_ (&util/with-field* :types
                              (&type/solve &type/+falsey+ =test))
                          ;; :let [_ (prn ::&parser/if 'ELSE)]
                          ]
                         (check* ?else))
                       (exec state-seq-m
                         [_ (&util/with-field* :types
                              (&type/solve [::&type/any] =test))
                          =then (check* ?then)
                          =else (check* ?else)
                          ;; :let [_ (prn ::&parser/if 'THEN+ELSE)]
                          ]
                         (return state-seq-m [::&type/union (list =then =else)]))]))

    [::&parser/def ?var]
    (exec state-seq-m
      [:let [=value [::&type/nothing]]
       _ (&util/with-field :env
           (&env/annotate ?var =value))]
      (return state-seq-m [::&type/object 'clojure.lang.Var [=value]]))

    [::&parser/def ?var ?value]
    (exec state-seq-m
      [=value (check* ?value)
       _ (&util/with-field :env
           (&env/annotate ?var =value))]
      (return state-seq-m [::&type/object 'clojure.lang.Var [=value]]))

    [::&parser/var ?var]
    (exec state-seq-m
      [=var (&util/with-field :env
              (&env/resolve-var ?var))]
      (return state-seq-m [::&type/object 'clojure.lang.Var [=var]]))


    [::&parser/fn ?local-name ?args ?body]
    (exec state-seq-m
      [worlds (&util/collect (exec state-seq-m
                               [=fn (&util/with-field* :types
                                      &type/fresh-var)
                                =args (map-m state-seq-m
                                             (fn [arg]
                                               (&util/with-field* :types
                                                 &type/fresh-var))
                                             ?args)
                                =return (with-env {?local-name =fn}
                                          (with-env (into {} (map vector ?args =args))
                                            (check* `[::&parser/do ~@?body])))]
                               (generalize-arity [::&type/arity =args =return])))]
      (case (count worlds)
        0 zero
        1 (&util/spread worlds)
        ;; else
        (exec state-seq-m
          [=arities (&util/collect (merge-arities worlds))]
          (return state-seq-m [::&type/function (map second =arities)]))))

    [::&parser/ann ?var ?type]
    (do ;; (prn `[::&parser/ann ~?var ~?type])
      (exec state-seq-m
        [_ (&util/with-field :env
             (&env/annotate ?var ?type))
         ;; :let [_ (println "ANNOTATED:" ?var ?type)]
         ]
        (return state-seq-m [::&type/nil])))

    [::&parser/ann-class ?class ?parents]
    (do ;; (prn [::&parser/ann-class ?class ?parents])
      (exec state-seq-m
        [_ (&util/with-field* :types
             (&type/define-class ?class ?parents))]
        (do ;; (println "DONE ANNOTATING")
          (return state-seq-m [::&type/nil]))))

    [::&parser/defalias ?name ?params ?type-def]
    (let [=type (if (empty? ?params)
                  [::&type/alias ?name ?type-def]
                  [::&type/type-ctor ?params [::&type/alias ?name ?type-def]])]
      (exec state-seq-m
        [_ (&util/with-field* :types
             (&type/define-type ?name =type))]
        (return state-seq-m [::&type/nil])))

    [::&parser/fn-call ?fn ?args]
    (do ;; (prn [::&parser/fn-call ?fn ?args])
      (exec state-seq-m
        [=fn (check* ?fn)
         =args (map-m state-seq-m check* ?args)]
        (fn-call =fn =args)))
    ))

;; [Interface]
;; Contants
(def +init+ (Context. &env/+init+ &type/+init+))

;; Functions
(defn check [form]
  #(let [results ((check* form) %)]
     (case (count results)
       0 '()
       1 (list [% (-> results first (nth 1))])
       ;; else
       (list [% [::&type/union (map second results)]])
       )))
