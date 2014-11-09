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
      (&util/with-field* :types
        (&type/$or (vec =types))))

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
  (prn 'prettify-type mappings type)
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
      (&util/with-field* :types
        (&type/$or =types)))

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

(defn ->pretty [type]
  (match type
    [::&type/bound _]
    (exec state-seq-m
      [=type (&util/with-field* :types
               (&type/deref-binding type))]
      (->pretty =type))
    
    [::&type/var _]
    (exec state-seq-m
      [[=top =bottom] (&util/with-field* :types
                        (&type/deref-var type))]
      (->pretty =top))

    [::&type/object ?class ?params]
    (exec state-seq-m
      [=params (map-m state-seq-m ->pretty ?params)]
      (return state-seq-m [::&type/object ?class =params]))

    [::&type/union ?types]
    (exec state-seq-m
      [=types (map-m state-seq-m ->pretty ?types)]
      (&util/with-field* :types
        (&type/$or =types)))

    [::&type/complement ?type]
    (exec state-seq-m
      [=type (->pretty ?type)]
      (return state-seq-m [::&type/complement =type]))

    [::&type/arity ?args ?body]
    (exec state-seq-m
      [=args (map-m state-seq-m ->pretty ?args)
       =body (->pretty ?body)]
      (return state-seq-m [::&type/arity =args =body]))

    [::&type/function ?arities]
    (exec state-seq-m
      [=arities (map-m state-seq-m ->pretty ?arities)]
      (return state-seq-m [::&type/function =arities]))
    
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
               rev-mappings (set/map-invert mappings)
               ;; _ (prn 'generalize-arity/vars body-vars args-vars poly-vars mappings)
               ]
         arity* (prettify-type mappings arity)
         :let [_ (prn '(prettify-type mappings arity) arity*)]
         ]
        (if (empty? used-vars)
          (return state-seq-m arity*)
          (exec state-seq-m
            [user-vars* (map-m state-seq-m
                               (fn [uv]
                                 (exec state-seq-m
                                   [[=top =bottom] (&util/with-field* :types
                                                     (&type/deref-var (get rev-mappings uv)))]
                                   (return state-seq-m (if (= [::&type/any] =top)
                                                         uv
                                                         [uv :< =top]))))
                               used-vars)]
            (return state-seq-m [::&type/all {} (vec user-vars*) arity*])))
        ))))

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
                      (list [state (let [[[_ returns]] ((&util/with-field* :types
                                                          (&type/parallel-combine-types (mapv #(-> % (nth 1) (nth 2)) taken))) state)]
                                     (-> taken first (nth 1) (assoc-in [2] returns)))])
                      )]
          (concat batch ((merge-arities left) state))))
      )))

(defn ^:private refine-local [types local type]
  ;; (prn 'refine-local types local type)
  (match type
    [::&type/union ?types]
    (exec state-seq-m
      [=type (return-all ?types)
       _ (&util/parallel (mapv (fn [expected]
                                 (&util/with-field* :types (&type/solve expected =type)))
                               types))
       _ (&util/with-field* :types
           (&type/update-binding local =type))]
      (return state-seq-m =type))
    
    [::&type/object 'java.lang.Boolean []]
    (do ;; (println "Reached:" [::&type/object 'java.lang.Boolean []])
      (exec state-seq-m
        [=type (return-all (list [::&type/literal java.lang.Boolean true]
                                 [::&type/literal java.lang.Boolean false]))
         ;; :let [_ (prn 'refine-local/=type =type)]
         _ (&util/with-field* :types
             (&type/update-binding local =type))]
        (return state-seq-m =type)))
    
    :else
    (return state-seq-m type)
    ))

(defn ^:private refine [check* types form]
  ;; (prn 'refine types form)
  (exec state-seq-m
    [=form (check* form)
     ;; :let [_ (prn 'refine/=form =form)]
     ;; state &util/get-state
     ;; :let [_ (prn 'refine/=form =form 'state state)]
     _ (match =form
         [::&type/bound _]
         (exec state-seq-m
           [=type (&util/with-field* :types
                    (&type/deref-binding =form))
            ;; :let [_ (prn 'refine/=form+ =type)]
            =type* (refine-local types =form =type)
            ;; :let [_ (prn 'refine/=form++ =type*)]
            ]
           (return state-seq-m true))

         :else
         (return state-seq-m true))]
    (return state-seq-m =form)))

(defn ^:private check-arity [=arity =args]
  (prn 'check-arity =arity =args)
  (match =arity
    [::&type/arity ?args ?return]
    (exec state-seq-m
      [_ (map-m state-seq-m
                (fn [[arg input]]
                  (&util/with-field* :types
                    (&type/solve arg input)))
                (map vector ?args =args))
       ;; :let [_ (prn 'check-arity =arity =args)]
       ]
      (return state-seq-m ?return))))

(defn ^:private fn-call [=fn =args]
  (prn 'fn-call =fn =args)
  (exec state-seq-m
    [=fn (&util/with-field* :types
           (exec state-seq-m
             [=fn (&type/instantiate =fn)
              :let [_ (prn '(&type/type-fn? =fn) (&type/type-fn? =fn) =fn)]]
             (if (&type/type-fn? =fn)
               (fn-call =fn =args)
               (&type/upcast ::&type/$fn =fn))))
     :let [_ (prn 'fn-call '=fn =fn '=args =args)]
     ]
    (match =fn
      [::&type/function ?arities]
      (exec state-seq-m
        [=arity (return-all (for [[_ args _ :as arity] ?arities
                                  :when (= (count args) (count =args))]
                              arity))
         ;; :let [_ (prn 'fn-call/=arity =arity)]
         ]
        (check-arity =arity =args)))))

(defrecord ClassTypeCtor [class args])

(defn qualify [prefix body]
  (symbol (name prefix) (name body)))

(defn ^:private ann-class [class parents]
  (exec state-seq-m
    [:let [class+ [::&type/class class]]
     ns (&util/with-field :env
          &env/current-ns)
     _ (&util/with-field* :types
         (&type/define-class (qualify ns (:class class)) (map :class parents)))]
    (return state-seq-m [::&type/nil])))

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

    [::&parser/#symbol ?value]
    (return state-seq-m [::&type/literal 'clojure.lang.Symbol ?value])

    [::&parser/#list ?value]
    (if (empty? ?value)
      (return state-seq-m [::&type/object 'clojure.lang.PersistentList [[::&type/nothing]]])
      (exec state-seq-m
        [=elems (map-m state-seq-m check* ?value)
         =elems (&util/with-field* :types
                  (&type/$or (vec =elems)))]
        (return state-seq-m [::&type/object 'clojure.lang.PersistentList [=elems]])))
    
    [::&parser/#vector ?value]
    (if (empty? ?value)
      (return state-seq-m [::&type/tuple []])
      (exec state-seq-m
        [=elems (map-m state-seq-m check* ?value)]
        (return state-seq-m [::&type/tuple (vec =elems)])))

    [::&parser/#map ?value]
    (if (empty? ?value)
      (return state-seq-m [::&type/record {}])
      (exec state-seq-m
        [=elems (map-m state-seq-m
                       (fn [[?k ?v]]
                         (exec state-seq-m
                           [=k (check* ?k)
                            =v (check* ?v)]
                           (return state-seq-m [=k =v])))
                       (seq ?value))]
        (return state-seq-m [::&type/record (into {} =elems)])))

    [::&parser/#set ?value]
    (if (empty? ?value)
      (return state-seq-m [::&type/object 'clojure.lang.IPersistentSet [[::&type/nothing]]])
      (exec state-seq-m
        [=elems (map-m state-seq-m check* ?value)
         =elems (&util/with-field* :types
                  (&type/$or (vec =elems)))]
        (return state-seq-m [::&type/object 'clojure.lang.IPersistentSet [=elems]])))
    
    [::&parser/symbol ?symbol]
    (do (prn [::&parser/symbol ?symbol])
      (if-let [ns (namespace ?symbol)]
        (exec state-seq-m
          [[class =field] (&util/with-field* :types
                            (&type/member-candidates [(-> ?symbol name symbol) :static-fields]))
           :let [_ (prn '[class =field] [class =field])]]
          (if (= class (symbol ns))
            (return state-seq-m =field)
            zero))
        (exec state-seq-m
          [=symbol (&util/with-field :env
                     (&env/resolve ?symbol))]
          (if (not= [::&type/macro] =symbol)
            (return state-seq-m =symbol)
            zero))))
    
    [::&parser/do & ?forms]
    (do ;; (prn [::&parser/do ?forms])
        (case (count ?forms)
          0 (return state-seq-m [::&type/nil])
          1 (exec state-seq-m
              [?form (&parser/parse (first ?forms))]
              (check* ?form))
          ;; else
          (exec state-seq-m
            [=forms (map-m state-seq-m
                           (fn [?form]
                             (exec state-seq-m
                               [?form (&parser/parse ?form)]
                               (check* ?form)))
                           ?forms)
             =body (&type/sequentially-combine-types =forms)]
            (return state-seq-m =body))))

    [::&parser/let ([[?label ?value] & ?bindings] :seq) ?body]
    (exec state-seq-m
      [=value (check* ?value)
       ;; :let [_ (prn ::&parser/let '?label ?label)]
       [?label =value] (match ?label
                         [::&parser/symbol ?local]
                         (exec state-seq-m
                           [_ (&util/with-field* :types
                                (&type/solve [::&type/any] =value))]
                           (return state-seq-m [?local =value])))
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
      [=test (refine check* [&type/+truthy+ &type/+falsey+ [::&type/any]] ?test)
       ;; =test* (&util/with-field* :types
       ;;          (&type/deref-binding =test))
       ;; :let [_ (prn 'IF '=test =test =test*)]
       =return (&util/parallel [(exec state-seq-m
                                  [_ (&util/with-field* :types
                                       (&type/solve &type/+truthy+ =test))
                                   =then (check* ?then)
                                   ;; =test* (&util/with-field* :types
                                   ;;          (&type/deref-binding =test))
                                   ;; :let [_ (prn 'IF 'THEN =test* =then)]
                                   ]
                                  (return state-seq-m =then))
                                (exec state-seq-m
                                  [_ (&util/with-field* :types
                                       (&type/solve &type/+falsey+ =test))
                                   =else (check* ?else)
                                   ;; =test* (&util/with-field* :types
                                   ;;          (&type/deref-binding =test))
                                   ;; :let [_ (prn 'IF 'ELSE =test* =else)]
                                   ]
                                  (return state-seq-m =else))
                                (exec state-seq-m
                                  [_ (&util/with-field* :types
                                       (&type/solve [::&type/any] =test))
                                   =then (check* ?then)
                                   ;; =then* (&util/with-field* :types
                                   ;;          (&type/deref-binding =then))
                                   =else (check* ?else)
                                   ;; =test* (&util/with-field* :types
                                   ;;          (&type/deref-binding =test))
                                   ;; :let [_ (prn 'IF 'THEN+ELSE =test* =then =else)]
                                   ]
                                  (&util/with-field* :types
                                    (&type/parallel-combine-types [=then =else])))
                                ])
       ;; :let [_ (println 'IF '=return =return)]
       ]
      (return state-seq-m =return))

    [::&parser/case ?value ?clauses ?default]
    (exec state-seq-m
      [;; :let [_ (prn '?clauses ?clauses)
       ;;       _ (prn '?default ?default)]
       =branches* (map-m state-seq-m
                         (fn [[?test ?form]]
                           (exec state-seq-m
                             [;; :let [_ (prn '?test ?test)]
                              =test (if (seq? ?test)
                                      (exec state-seq-m
                                        [?parts (map-m state-seq-m check* ?test)]
                                        (&util/with-field* :types
                                          (&type/$or (vec ?parts))))
                                      (check* ?test))
                              ;; :let [_ (prn '=test =test)]
                              ]
                             (return state-seq-m [=test ?form])))
                         ?clauses)
       ;; :let [_ (prn '=branches* (mapv first =branches*) =branches*)]
       =value (refine check* (mapv first =branches*) ?value)
       ;; :let [_ (prn '=value =value)]
       =branch (&util/parallel* (let [main-branches (mapv (fn [[=test ?form]]
                                                            (exec state-seq-m
                                                              [=value+ (&util/with-field* :types
                                                                         (exec state-seq-m
                                                                           [=value (&type/deref-binding =value)]
                                                                           (&type/deref-var =value)))
                                                               ;; :let [_ (prn '[=test =value] [=test =value+])]
                                                               _ (&util/with-field* :types
                                                                   (&type/solve =test =value))
                                                               =form (check* ?form)
                                                               ;; :let [_ (prn '=form =form)]
                                                               ]
                                                              (return state-seq-m =form)))
                                                          =branches*)]
                                  (if ?default
                                    (conj main-branches
                                          (check* ?default))
                                    main-branches)))
       ;; :let [_ (prn '=branch =branch)]
       ;; =default (check* ?default)
       ]
      ;; (return state-seq-m [::&type/union (conj (vec =branches) =default)])
      ;; (return state-seq-m [::&type/union (vec =branches)])
      (return state-seq-m =branch))

    [::&parser/loop ?locals ?body]
    (exec state-seq-m
      [=locals (map-m state-seq-m
                      (fn [[label value]]
                        (exec state-seq-m
                          [=value (&util/with-field :env
                                    (&env/resolve value))]
                          (return state-seq-m [label =value])))
                      ?locals)
       locals-pre (map-m state-seq-m
                         #(exec state-seq-m
                            [=bound (&util/with-field :env
                                      (&env/resolve %))]
                            (&util/with-field* :types
                              (&type/deref-binding =bound)))
                         (mapv first =locals))
       ;; :let [_ (prn 'locals-pre locals-pre)]
       _ (with-env (into {::recur (mapv first =locals)}
                         =locals)
           (check* ?body))
       locals-post (map-m state-seq-m
                          #(exec state-seq-m
                             [=bound (&util/with-field :env
                                       (&env/resolve %))]
                             (&util/with-field* :types
                               (&type/deref-binding =bound)))
                          (mapv first =locals))
       ;; :let [_ (prn 'locals-post locals-pre)]
       ]
      (with-env (into {::recur (mapv first =locals)}
                      =locals)
        (check* ?body)))

    [::&parser/recur ?args]
    (exec state-seq-m
      [=recur (&util/with-field :env
                (&env/resolve ::recur))
       =recur (map-m state-seq-m
                     #(&util/with-field :env
                        (&env/resolve %))
                     =recur)
       _ (if (= (count =recur) (count ?args))
           (return state-seq-m nil)
           zero)
       =args (map-m state-seq-m check* ?args)
       ;; :let [_ (prn '=recur =recur)
       ;;       _ (prn '=args =args)]
       _ (map-m state-seq-m
                (fn [[=e =a]]
                  (exec state-seq-m
                    [=wider (&util/with-field* :types
                              (exec state-seq-m
                                [_ (&type/solve =a =e)
                                 =e (&type/deref-binding =e)]
                                (&type/$or [=e =a])))]
                    (&util/with-field* :types
                      (&type/update-binding =e =wider))))
                (map vector =recur =args))]
      (return state-seq-m [::&type/nothing]))

    [::&parser/assert ?test ?message]
    (exec state-seq-m
      [=message (check* ?message)
       _ (&util/with-field* :types
           (&type/solve [::&type/any] =message))
       =test (check* ?test)
       ;; =test (refine check* [&type/+truthy+] ?test)
       ;; :let [_ (prn '=test =test)]
       _ (&util/parallel [(&util/with-field* :types
                            (&type/solve &type/+truthy+ =test))
                          (&util/with-field* :types
                            (exec state-seq-m
                              [=boolean (&type/instantiate* 'java.lang.Boolean [])]
                              (if (= =boolean =test)
                                (return state-seq-m true)
                                zero)))])
       _ (fn [state]
           (prn 'state state)
           (list [state nil]))]
      (return state-seq-m [::&type/nil]))
    
    [::&parser/def ?var ?value]
    (exec state-seq-m
      [=value (if ?value
                (check* ?value)
                (return state-seq-m [::&type/nothing]))
       ;; :let [_ (prn '=value =value)]
       _ (&util/with-field :env
           (&env/intern ?var =value))]
      (&util/with-field* :types
        (&type/instantiate* 'clojure.lang.Var [=value])))

    [::&parser/var ?var]
    (exec state-seq-m
      [=value (&util/with-field :env
                (&env/resolve-var ?var))]
      (&util/with-field* :types
        (&type/instantiate* 'clojure.lang.Var [=value])))

    [::&parser/throw ?ex]
    (exec state-seq-m
      [=ex (check* ?ex)
       _ (&util/with-field* :types
           (exec state-seq-m
             [=exception (&type/instantiate* 'java.lang.Exception [])]
             (&type/solve =exception =ex)))]
      (return state-seq-m [::&type/eff [::&type/nothing] {:try =ex}]))
    
    [::&parser/try ?body ?catches ?finally]
    (exec state-seq-m
      [=body (check* ?body)
       =clean-body (match =body
                     [::&type/eff ?data ?effs]
                     (let [thrown-exs (match (:try ?effs)
                                        nil
                                        #{}
                                        
                                        [::&type/object ?class _]
                                        #{?class}

                                        [::&type/union ?types]
                                        (set (map second ?types)))
                           handled-exs (set (map second ?catches))
                           rem-exs (set/difference thrown-exs handled-exs)]
                       (return state-seq-m (case (count rem-exs)
                                             0 ?data
                                             1 [::&type/eff ?data {:try [::&type/object (first rem-exs) []]}]
                                             ;; else
                                             [::&type/eff ?data {:try [::&type/union (mapv (fn [ex] [::&type/object ex []]) rem-exs)]}])))
                     
                     :else
                     (return state-seq-m =body))
       =catches (map-m state-seq-m check* ?catches)
       =finally (check* ?finally)
       =all-returning (&type/parallel-combine-types (cons =clean-body =catches))]
      (&type/sequentially-combine-types [=finally =all-returning]))

    [::&parser/catch ?class ?label ?body]
    (with-env {?label [::&type/object ?class []]}
      (check* ?body))
    
    [::&parser/monitor-enter ?object]
    (exec state-seq-m
      [=object (check* ?object)
       _ (&util/with-field* :types
           (&type/solve [::&type/complement [::&type/nil]] =object))]
      (return state-seq-m [::&type/nil]))

    [::&parser/monitor-exit ?object]
    (exec state-seq-m
      [=object (check* ?object)
       _ (&util/with-field* :types
           (&type/solve [::&type/complement [::&type/nil]] =object))]
      (return state-seq-m [::&type/nil]))

    [::&parser/binding ?bindings ?body]
    (exec state-seq-m
      [_ (map-m state-seq-m
                (fn [[label value]]
                  (match label
                    [::&parser/symbol ?label]
                    (exec state-seq-m
                      [=var (&util/with-field :env
                              (&env/resolve-var ?label))
                       =value (check* value)]
                      (&util/with-field* :types
                        (&type/solve =var =value)))
                    
                    :else
                    zero))
                ?bindings)]
      (check* ?body))
    
    [::&parser/fn ?local-name ?args ?body]
    (exec state-seq-m
      [worlds (&util/collect (exec state-seq-m
                               [=fn (&util/with-field* :types
                                      (exec state-seq-m
                                        [=var &type/fresh-var]
                                        (&type/bind =var)))
                                =args (map-m state-seq-m
                                             (fn [arg]
                                               (&util/with-field* :types
                                                 (exec state-seq-m
                                                   [=var &type/fresh-var]
                                                   (&type/bind =var))))
                                             ?args)
                                =return (with-env {?local-name =fn}
                                          (with-env (into {} (map vector ?args =args))
                                            (check* ?body)))
                                :let [_ (prn '=return =return)]]
                               (generalize-arity [::&type/arity =args =return])))
       ;; :let [_ (prn (map second worlds))]
       ]
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
               (&env/intern ?var ?type))
           ;; :let [_ (println "ANNOTATED:" ?var ?type)]
           ]
          (return state-seq-m [::&type/nil])))

    [::&parser/ann-class ?class ?parents ?fields+methods]
    (do ;; (prn [::&parser/ann-class ?class ?parents])
        (exec state-seq-m
          [=class (&util/with-field* :types
                    (&type/define-class ?class ?parents))
           all-categories+members (map-m state-seq-m
                                         (fn [[category members]]
                                           (if (= :ctor category)
                                             (exec state-seq-m
                                               [=ctor (&parser/parse-type-def members)]
                                               (return state-seq-m [:ctor =ctor]))
                                             (exec state-seq-m
                                               [all-members+types (map-m state-seq-m
                                                                         (fn [[name type]]
                                                                           (exec state-seq-m
                                                                             [=type (&parser/parse-type-def type)]
                                                                             (return state-seq-m [name =type])))
                                                                         members)]
                                               (return state-seq-m [category (into {} all-members+types)]))))
                                         (apply hash-map ?fields+methods))
           _ (&util/with-field* :types
               (&type/define-class-members (nth ?class 0) (into {} all-categories+members)))
           ;; state &util/get-state
           ;; :let [_ (prn ::&parser/ann-class (:types state))]
           ]
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

    [::&parser/field-access ?field ?obj]
    (exec state-seq-m
      [=obj (check* ?obj)
       [class =field] (&util/with-field* :types
                        (&type/member-candidates [?field :fields]))]
      (fn-call =field (list =obj)))
    
    [::&parser/method-call ?method ?obj ?args]
    (exec state-seq-m
      [:let [_ (prn [::&parser/method-call ?method ?obj ?args])]
       =obj (check* ?obj)
       =args (map-m state-seq-m check* ?args)
       :let [_ (prn '=obj =obj '=args =args)]
       [class =method] (&util/with-field* :types
                         (&type/member-candidates [?method :methods]))
       :let [_ (prn '[class =method] [class =method])]
       _ (&util/with-field* :types
           (exec state-seq-m
             [=object (&type/instantiate* class [])
              :let [_ (prn '=object =object)]]
             (&type/solve =object =obj)))
       :let [_ (println "SOLVED")]
       =method (fn-call =method (list =obj))]
      (fn-call =method =args))

    [::&parser/new ?class ?args]
    (exec state-seq-m
      [=args (map-m state-seq-m check* ?args)
       [_ =ctor] (&util/with-field* :types
                   (&type/member-candidates [?class :ctor]))]
      (fn-call =ctor =args))

    [::&parser/fn-call ?fn ?args]
    (if-let [[?class ?method] (match ?fn
                                [::&parser/symbol ?symbol]
                                (if-let [ns (namespace ?symbol)]
                                  [(symbol ns) (symbol (name ?symbol))])

                                :else
                                nil)]
      (exec state-seq-m
        [=args (map-m state-seq-m check* ?args)
         [class =method] (&util/with-field* :types
                           (&type/member-candidates [?method :static-methods]))
         =method (if (= class ?class)
                   (return state-seq-m =method)
                   zero)]
        (fn-call =method =args))
      (do ;; (prn [::&parser/fn-call ?fn ?args])
          (exec state-seq-m
            [=fn (check* ?fn)
             ;; :let [_ (prn '=fn =fn)]
             =args (map-m state-seq-m check* ?args)
             =return (fn-call =fn =args)
             ;; :let [_ (prn '=return =return)]
             ]
            (return state-seq-m =return))))
    ))

;; [Interface]
;; Contants
(def +init+ (Context. &env/+init+ &type/+init+))

;; Functions
(defn check [form]
  #(let [results ((exec state-seq-m
                    [raw (check* form)]
                    (->pretty raw))
                  %)]
     (case (count results)
       0 '()
       1 (list [% (-> results first (nth 1))])
       ;; else
       ((&util/with-field* :types
          (&type/parallel-combine-types (mapv second results)))
        %)
       )))
