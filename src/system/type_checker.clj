(ns system.type-checker
  (:require [clojure.set :as set]
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [exec
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
  (match type
    [::&type/hole _]
    (exec [[=top =bottom] (&util/with-field :types
                            (&type/get-hole type))
           =top (clean-env to-clean =top)
           =bottom (clean-env to-clean =bottom)
           ;; :let [_ (prn 'clean-env type =top =bottom)]
           ]
      (if (contains? to-clean type)
        (return (cond (= [::&type/nothing] =bottom)
                      =top
                      
                      (= [::&type/any] =top)
                      =bottom

                      :else
                      =top))
        (exec [_ (&util/with-field :types
                   (&type/narrow-hole type =top =bottom))]
          (return type))))
    
    [::&type/object ?class ?params]
    (exec [=params (map-m (partial clean-env to-clean) ?params)]
      (return [::&type/object ?class =params]))

    [::&type/union ?types]
    (exec [=types (map-m (partial clean-env to-clean) ?types)]
      (&util/with-field :types
        (reduce-m &type/$or [::&type/nothing] =types)))

    [::&type/complement ?type]
    (exec [=type (clean-env to-clean ?type)]
      (return [::&type/complement =type]))
    
    :else
    (return type)))

(defn with-env [env inner]
  (exec [:let [bound-ids (-> env vals set)]
         _ (&util/with-field :env
             (&env/enter env))
         =type* inner
         =type (clean-env bound-ids =type*)
         _ (&util/with-field :env
             &env/exit)]
    (return =type)))

(defn with-env* [env inner]
  (exec [:let [bound-ids (-> env vals set)]
         _ (&util/with-field :env
             (&env/enter env))
         =type inner
         _ (&util/with-field :env
             &env/exit)]
    (return =type)))

(defn ^:private extract-holes [type]
  (match type
    [::&type/hole _]
    (exec [=hole (&util/with-field :types
                   (&type/normalize-hole type))
           [=top =bottom] (&util/with-field :types
                            (&type/get-hole =hole))
           at-top (extract-holes =top)
           at-bottom (extract-holes =bottom)
           :let [total-count (merge-with + {=hole 1} at-top at-bottom)]]
      (return total-count))
    
    ;; [::&type/var _]
    ;; (return (list type))

    [::&type/object _ ?params]
    (exec [all-holes (map-m extract-holes ?params)]
      (return (apply merge-with + all-holes)))

    [::&type/union ?types]
    (exec [all-holes (map-m extract-holes ?types)]
      (return (apply merge-with + all-holes)))

    [::&type/complement ?type]
    (extract-holes ?type)

    [::&type/function ?arities]
    (exec [all-holes (map-m extract-holes ?arities)]
      (return (apply merge-with + all-holes)))

    [::&type/arity ?args ?return]
    (exec [all-holes (map-m extract-holes ?args)
           return-holes (extract-holes ?return)]
      (return (apply merge-with + return-holes all-holes)))
    
    :else
    (return {})))

(defn ^:private prettify-type [mappings type]
  (match type
    [::&type/hole _]
    (if-let [var-name (get mappings type)]
      (return var-name)
      (exec [=type (&util/with-field :types
                     (&type/normalize-hole type))]
        (if-let [var-name (get mappings =type)]
          (return var-name)
          ;; (exec [[=top =bottom] (&util/with-field :types
          ;;                         (&type/get-hole =type))
          ;;        ;; =top (prettify-type mappings =top)
          ;;        ;; =bottom (prettify-type mappings =bottom)
          ;;        ;; _ (&util/with-field :types
          ;;        ;;     (&type/narrow-hole type =top =bottom))
          ;;        ]
          ;;   ;; (return type)
          ;;   (prettify-type mappings =top))
          (exec [[=top =bottom] (&util/with-field :types
                                  (&type/get-hole =type))
                 ;; :let [_ (prn 'Prettifying =type =top =bottom)]
                 ]
            (if (and (= [::&type/any] =top)
                     (not= [::&type/nothing] =bottom))
              (prettify-type mappings =bottom)
              (prettify-type mappings =top)))
          )))
    
    [::&type/object ?class ?params]
    (exec [=params (map-m (partial prettify-type mappings) ?params)]
      (return [::&type/object ?class =params]))

    [::&type/union ?types]
    (exec [=types (map-m (partial prettify-type mappings) ?types)]
      (&util/with-field :types
        (reduce-m &type/$or [::&type/nothing] =types)))

    [::&type/complement ?type]
    (exec [=type (prettify-type mappings ?type)]
      (return [::&type/complement =type]))

    [::&type/function ?arities]
    (exec [=arities (map-m (partial prettify-type mappings) ?arities)]
      (return [::&type/function =arities]))

    [::&type/arity ?args ?body]
    (exec [=args (map-m (partial prettify-type mappings) ?args)
           =body (prettify-type mappings ?body)]
      (return [::&type/arity =args =body]))
    
    :else
    (return type)))

(defn ^:private fresh-poly-fn [num-args]
  (exec [=args (map-m (fn [_] &type/fresh-hole) (repeat num-args nil))
         =return &type/fresh-hole]
    (return [::&type/function (list [::&type/arity (vec =args) =return])])))

(let [+var-names+ (for [idx (iterate inc 1)
                        alphabet "abcdefghijklmnopqrstuvwxyz"]
                    (if (= 1 idx)
                      (symbol (str alphabet))
                      (symbol (str alphabet idx))))]
  (defn ^:private generalize-arity [arity]
    ;; (prn 'generalize-arity arity)
    (match arity
      [::&type/arity ?args ?body]
      (exec [body-vars (extract-holes ?body)
             ;; :let [_ (prn 'body-vars body-vars)]
             args-vars (exec [all-holes (map-m extract-holes ?args)]
                         (return (apply merge-with + all-holes)))
             ;; :let [_ (prn 'args-vars args-vars)]
             :let [poly-vars (merge-with + args-vars body-vars)
                   poly-vars (sort < (for [[k cnt] poly-vars
                                           :when (> cnt 1)]
                                       (nth k 1)))
                   ;; _ (prn 'poly-vars poly-vars)
                   used-vars (take (count poly-vars) +var-names+)
                   mappings (into {} (map (fn [id name]
                                            [[::&type/hole id] name])
                                          poly-vars used-vars))
                   ;; _ (prn 'mappings mappings)
                   rev-mappings (set/map-invert mappings)]
             arity* (prettify-type mappings arity)]
        (if (empty? used-vars)
          (return arity*)
          (exec [user-vars* (map-m (fn [uv]
                                     (exec [[=top =bottom] (&util/with-field :types
                                                             (&type/get-hole (get rev-mappings uv)))]
                                       (return [uv =top])))
                                   used-vars)]
            (return [::&type/all {} (vec user-vars*) arity*])))
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
                      (list [state (let [[[_ returns]] ((&util/with-field :types
                                                          (reduce-m &type/parallel [::&type/nothing] (mapv #(-> % (nth 1) (nth 2)) taken))) state)]
                                     (-> taken first (nth 1) (assoc-in [2] returns)))])
                      )]
          (concat batch ((merge-arities left) state))))
      )))

(defn ^:private check-arity [=arity =args]
  (match =arity
    [::&type/arity ?args ?return]
    (exec [_ (map-m (fn [[arg input]]
                      (&util/with-field :types
                        (&type/solve arg input)))
                    (map vector ?args =args))]
      (return ?return))))

(defn ^:private fn-call [=fn =args]
  ;; (prn 'fn-call =fn =args)
  (exec [=fn (&util/with-field :types
               (exec [=fn (&type/instantiate =fn)]
                 (if (&type/type-fn? =fn)
                   (fn-call =fn =args)
                   (&type/upcast ::&type/$fn =fn))))]
    (match =fn
      [::&type/function ?arities]
      (exec [=arity (return-all (for [[_ args _ :as arity] ?arities
                                      :when (= (count args) (count =args))]
                                  arity))]
        (check-arity =arity =args)))))

(defrecord ClassTypeCtor [class args])

(defn qualify [prefix body]
  (symbol (name prefix) (name body)))

(defn ^:private ann-class [class parents]
  (exec [:let [class+ [::&type/class class]]
         ns (&util/with-field :env
              &env/current-ns)
         _ (&util/with-field :types
             (&type/define-class (qualify ns (:class class)) (map :class parents)))]
    (return [::&type/nil])))

(defn check* [form]
  (match form
    [::&parser/#nil]
    (return [::&type/nil])
    
    [::&parser/#boolean ?value]
    (return [::&type/literal 'java.lang.Boolean ?value])

    [::&parser/#integer ?value]
    (return [::&type/literal 'java.lang.Long ?value])

    [::&parser/#real ?value]
    (return [::&type/literal 'java.lang.Double ?value])

    [::&parser/#big-int ?value]
    (return [::&type/literal 'clojure.lang.BigInt ?value])

    [::&parser/#big-decimal ?value]
    (return [::&type/literal 'java.math.BigDecimal ?value])

    [::&parser/#ratio ?value]
    (return [::&type/literal 'clojure.lang.Ratio ?value])

    [::&parser/#character ?value]
    (return [::&type/literal 'java.lang.Character ?value])

    [::&parser/#string ?value]
    (return [::&type/literal 'java.lang.String ?value])

    [::&parser/#regex ?value]
    (return [::&type/literal 'java.util.regex.Pattern ?value])

    [::&parser/#keyword ?value]
    (return [::&type/literal 'clojure.lang.Keyword ?value])

    [::&parser/#symbol ?value]
    (return [::&type/literal 'clojure.lang.Symbol ?value])

    [::&parser/#list ?value]
    (exec [=elems (map-m check* ?value)
           =elems (&util/with-field :types
                    (reduce-m &type/$or [::&type/nothing] =elems))]
      (return [::&type/object 'clojure.lang.PersistentList [=elems]]))
    
    [::&parser/#vector ?value]
    (if (empty? ?value)
      (return [::&type/tuple []])
      (exec [=elems (map-m check* ?value)]
        (return [::&type/tuple (vec =elems)])))

    [::&parser/#map ?value]
    (if (empty? ?value)
      (return [::&type/record {}])
      (exec [=elems (map-m (fn [[?k ?v]]
                             (exec [=k (check* ?k)
                                    =v (check* ?v)]
                               (return [=k =v])))
                           (seq ?value))]
        (return [::&type/record (into {} =elems)])))

    [::&parser/#set ?value]
    (exec [=elems (map-m check* ?value)
           =elems (&util/with-field :types
                    (reduce-m &type/$or [::&type/nothing] =elems))]
      (return [::&type/object 'clojure.lang.IPersistentSet [=elems]]))
    
    [::&parser/symbol ?symbol]
    (if-let [ns (namespace ?symbol)]
      (exec [[class =field] (&util/with-field :types
                              (&type/member-candidates [(-> ?symbol name symbol) :static-fields]))
             :when (= class (symbol ns))]
        (return =field))
      (&util/try-all [(exec [=symbol (&util/with-field :env
                                       (&env/resolve ?symbol))
                             :when (not= [::&type/macro] =symbol)]
                        (return =symbol))
                      (exec [? (&util/with-field :types
                                 (&type/class-defined? ?symbol))
                             :when ?
                             =inner (&util/with-field :types
                                      (&type/instantiate* ?symbol))]
                        (&util/with-field :types
                          (&type/instantiate* 'java.lang.Class [=inner])))]))
    
    [::&parser/do & ?forms]
    (exec [=forms (map-m (fn [?form]
                           (exec [?form (&parser/parse ?form)]
                             (check* ?form)))
                         ?forms)]
      (&util/with-field :types
        (reduce-m &type/sequential [::&type/nil] =forms)))

    [::&parser/let ([[?label ?value] & ?bindings] :seq) ?body]
    (exec [=value (check* ?value)
           [?label =value] (match ?label
                             [::&parser/symbol ?local]
                             (return [?local =value]))
           ;; :let [_ (prn ::&parser/let '[?label =value] [?label =value])]
           =binding (&util/with-field :types
                      (exec [=hole (&type/fresh-var ?label)
                             _ (&type/narrow-hole =hole =value [::&type/nothing])]
                        (return =hole)))
           ;; :let [_ (prn ::&parser/let '=binding =binding)]
           ]
      (with-env {?label =binding}
        (if (empty? ?bindings)
          (check* ?body)
          (check* [::&parser/let ?bindings ?body]))))

    [::&parser/if ?test ?then ?else]
    (exec [branches (&util/collect (exec [=test (check* ?test)]
                                     (&util/try-all [(&util/parallel [(exec [_ (&util/with-field :types
                                                                                 (&type/solve &type/+truthy+ =test))
                                                                             =test* (match =test
                                                                                      [::&type/hole _]
                                                                                      (exec [[=top =bottom] (&util/with-field :types
                                                                                                              (&type/get-hole =test))]
                                                                                        (return =top))
                                                                                      :else
                                                                                      (return =test))
                                                                             :when (and (not= =test* [::&type/nothing])
                                                                                        (not= =test* [::&type/object 'java.lang.Boolean []]))]
                                                                        (check* ?then))
                                                                      (exec [_ (&util/with-field :types
                                                                                 (&type/solve &type/+falsey+ =test))
                                                                             =test* (match =test
                                                                                      [::&type/hole _]
                                                                                      (exec [[=top =bottom] (&util/with-field :types
                                                                                                              (&type/get-hole =test))]
                                                                                        (return =top))
                                                                                      :else
                                                                                      (return =test))
                                                                             :when (and (not= =test* [::&type/nothing])
                                                                                        (not= =test* [::&type/object 'java.lang.Boolean []]))]
                                                                        (check* ?else))])
                                                     (exec [_ (&util/with-field :types
                                                                (&type/solve &type/+ambiguous+ =test))
                                                            =then (check* ?then)
                                                            =else (check* ?else)]
                                                       (&util/with-field :types
                                                         (&type/parallel =then =else)))
                                                     ])))
           ;; :let [_ (prn 'branches (mapv second branches))]
           ]
      (&util/spread branches))
    
    [::&parser/case ?value ?clauses ?default]
    (exec [=branches* (map-m
                       (fn [[?test ?form]]
                         (exec [=test (if (seq? ?test)
                                        (exec [?parts (map-m check* ?test)]
                                          (&util/with-field :types
                                            (reduce-m &type/$or [::&type/nothing] ?parts)))
                                        (check* ?test))]
                           (return [=test ?form])))
                       ?clauses)
           =value (check* ?value)
           :let [main-branches (mapv (fn [[=test ?form]]
                                       (exec [_ (&util/with-field :types
                                                  (&type/solve =test =value))
                                              =form (check* ?form)]
                                         (return =form)))
                                     =branches*)]]
      (&util/parallel (if ?default
                        (conj main-branches
                              (check* ?default))
                        main-branches)))

    [::&parser/loop ?locals ?body]
    (exec [=locals (map-m (fn [[label value]]
                            (exec [=value (&util/with-field :env
                                            (&env/resolve value))
                                   [=top =bottom] (&util/with-field :types
                                                    (&type/get-hole =value))
                                   ;; :let [_ (prn ::&parser/loop [label =value] [=top =bottom])]
                                   =hole (&util/with-field :types
                                           (exec [=hole &type/fresh-hole
                                                  _ (&type/narrow-hole =hole [::&type/any] =top)
                                                  ;; [=top* =bottom*] (&type/get-hole =hole)
                                                  ;; :let [_ (prn ::&parser/loop =hole [=top* =bottom*])]
                                                  ]
                                             (return =hole)))]
                              (return [label =hole])))
                          ?locals)
           =body (with-env (into {::recur (mapv second =locals)}
                                 =locals)
                   (check* ?body))]
      ;; (clean-holes (into #{} (map second =locals)) =body)
      (return =body))

    [::&parser/recur ?args]
    (exec [=recur (&util/with-field :env
                    (&env/resolve ::recur))
           :when (= (count =recur) (count ?args))
           =args (map-m check* ?args)
           _ (&util/with-field :types
               (map-m (fn [[=e =a]] (&type/solve =a =e))
                      (map vector =recur =args)))]
      (return [::&type/nothing]))

    [::&parser/assert ?test ?message]
    (exec [=message (check* ?message)
           _ (&util/with-field :types
               (&type/solve [::&type/any] =message))
           =test (check* ?test)
           _ (&util/try-all [(&util/with-field :types
                               (&type/solve &type/+truthy+ =test))
                             (&util/with-field :types
                               (exec [=boolean (&type/instantiate* 'java.lang.Boolean [])]
                                 (if (= =boolean =test)
                                   (return true)
                                   zero)))])]
      (return [::&type/nil]))
    
    [::&parser/def ?var ?value]
    (exec [=value (if ?value
                    (check* ?value)
                    (return [::&type/nothing]))
           _ (&util/with-field :types
               (if-let [tag (-> ?var meta :tag)]
                 (exec [=tag (&type/instantiate* tag)
                        _ (&type/solve =tag =value)]
                   (return nil))
                 (return nil)))
           _ (&util/with-field :env
               (&env/intern ?var =value))]
      (&util/with-field :types
        (&type/instantiate* 'clojure.lang.Var [=value])))

    [::&parser/var ?var]
    (exec [=value (&util/with-field :env
                    (&env/resolve-var ?var))]
      (&util/with-field :types
        (&type/instantiate* 'clojure.lang.Var [=value])))

    [::&parser/throw ?ex]
    (exec [=ex (check* ?ex)
           _ (&util/with-field :types
               (exec [=exception (&type/instantiate* 'java.lang.Exception [])]
                 (&type/solve =exception =ex)))]
      (return [::&type/eff [::&type/nothing] {:try =ex}]))
    
    [::&parser/try ?body ?catches ?finally]
    (exec [=body (check* ?body)
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
                           (return (case (count rem-exs)
                                     0 ?data
                                     1 [::&type/eff ?data {:try [::&type/object (first rem-exs) []]}]
                                     ;; else
                                     [::&type/eff ?data {:try [::&type/union (mapv (fn [ex] [::&type/object ex []]) rem-exs)]}])))
                         
                         :else
                         (return =body))
           =catches (map-m check* ?catches)
           =finally (check* ?finally)
           =all-returning (&util/with-field :types
                            (reduce-m &type/parallel [::&type/nothing] (cons =clean-body =catches)))]
      (&util/with-field :types
        (&type/sequential =finally =all-returning)))

    [::&parser/catch ?class ?label ?body]
    (with-env {?label [::&type/object ?class []]}
      (check* ?body))

    [::&parser/defmulti ?name ?dispatch-fn]
    (exec [=dispatch-fn (check* ?dispatch-fn)
           ;; :let [_ (prn "#1")]
           :let [=multi-fn [::&type/multi-fn =dispatch-fn []]]
           ;; :let [_ (prn "#2")]
           _ (&util/with-field :env
               (&env/intern ?name =multi-fn))
           ;; :let [_ (prn "#3")]
           ]
      (&util/with-field :types
        (&type/instantiate* 'clojure.lang.Var [=multi-fn])))

    [::&parser/defmethod ?name ?dispatch-val ?args ?body]
    (exec [=multi-fn (check* [::&parser/symbol ?name])
           ;; :let [_ (prn "#1" =multi-fn)]
           ]
      (match =multi-fn
        [::&type/multi-fn ?dispatch-fn ?methods]
        (exec [=args (&util/with-field :types
                       (map-m (constantly &type/fresh-hole) ?args))
               ;; :let [_ (prn "#2")]
               =dispatch-val (check* ?dispatch-val)
               ;; :let [_ (prn "#3")]
               =return (fn-call ?dispatch-fn =args)
               ;; :let [_ (prn "#4")]
               _ (&util/with-field :types
                   (&type/solve =return =dispatch-val))
               ;; :let [_ (prn "#5" =return =dispatch-val =args)]
               worlds (&util/collect (exec [=return (with-env* (into {} (map vector ?args =args))
                                                      (check* ?body))]
                                       (generalize-arity [::&type/arity =args =return])))
               ;; :let [_ (prn "#6")]
               =new-multi-fn (if (empty? worlds)
                               zero
                               (exec [=arities (&util/collect (merge-arities worlds))
                                      :let [=new-multi-fn [::&type/multi-fn ?dispatch-fn (into ?methods (map second =arities))]]
                                      _ (&util/with-field :env
                                          (&env/intern ?name =new-multi-fn))]
                                 (return =new-multi-fn)))
               ;; :let [_ (prn "#7")]
               ]
          (&util/with-field :types
            (&type/instantiate* 'clojure.lang.Var [=new-multi-fn])))

        :else
        zero))
    
    [::&parser/monitor-enter ?object]
    (exec [=object (check* ?object)
           _ (&util/with-field :types
               (&type/solve [::&type/complement [::&type/nil]] =object))]
      (return [::&type/nil]))

    [::&parser/monitor-exit ?object]
    (exec [=object (check* ?object)
           _ (&util/with-field :types
               (&type/solve [::&type/complement [::&type/nil]] =object))]
      (return [::&type/nil]))

    [::&parser/binding ?bindings ?body]
    (exec [_ (map-m
              (fn [[label value]]
                (match label
                  [::&parser/symbol ?label]
                  (exec [=var (&util/with-field :env
                                (&env/resolve-var ?label))
                         =value (check* value)]
                    (&util/with-field :types
                      (&type/solve =var =value)))
                  
                  :else
                  zero))
              ?bindings)]
      (check* ?body))
    
    [::&parser/fn ?local-name ?args ?body]
    (let [[pre-post ?body] (match ?body
                             [::&parser/do ?pre-post & ?forms]
                             (if (and (map? ?pre-post)
                                      (or (contains? ?pre-post :pre)
                                          (contains? ?pre-post :post)))
                               [?pre-post `[::&parser/do ~@?forms]]
                               [nil ?body]))]
      (exec [all-pre (map-m #(&parser/parse `(~'assert ~%)) (:pre pre-post))
             ;; :let [_ (prn 'all-pre all-pre)]
             all-post (map-m #(&parser/parse `(~'assert ~%)) (:post pre-post))
             ;; :let [_ (prn 'all-post all-post)]
             worlds (&util/collect (exec [=args (&util/with-field :types
                                                  (map-m &type/fresh-var ?args))
                                          ;; :let [_ (println "Post =args")]
                                          _ (with-env* (into {} (map vector ?args =args))
                                              (map-m check* all-pre))
                                          ;; :let [_ (println "#1")]
                                          =return (if ?local-name
                                                    (exec [=fn (&util/with-field :types
                                                                 &type/fresh-hole)]
                                                      (with-env* {?local-name =fn}
                                                        (with-env* (into {::recur =args} (map vector ?args =args))
                                                          (check* ?body))))
                                                    (with-env* (into {::recur =args} (map vector ?args =args))
                                                      (check* ?body)))
                                          _ (with-env* {'% =return}
                                              (map-m check* all-post))
                                          ;; :let [_ (println "#2")]
                                          ]
                                     (generalize-arity [::&type/arity =args =return])))
             :when (not (empty? worlds))]
        (exec [=arities (&util/collect (merge-arities worlds))]
          (return [::&type/function (map second =arities)]))))
    
    [::&parser/ann ?var ?type]
    (exec [_ (&util/with-field :env
               (&env/intern ?var ?type))]
      (return [::&type/nil]))

    [::&parser/ann-class ?class ?parents ?fields+methods]
    (exec [=class (&util/with-field :types
                    (&type/define-class ?class ?parents))
           all-categories+members (map-m (fn [[category members]]
                                           (if (= :ctor category)
                                             (exec [=ctor (&parser/parse-type-def {} members)]
                                               (return [:ctor =ctor]))
                                             (exec [all-members+types (map-m (fn [[name type]]
                                                                               (exec [=type (&parser/parse-type-def {} type)]
                                                                                 (return [name =type])))
                                                                             members)]
                                               (return [category (into {} all-members+types)]))))
                                         (apply hash-map ?fields+methods))
           _ (&util/with-field :types
               (&type/define-class-members (nth ?class 0) (into {} all-categories+members)))]
      (return [::&type/nil]))
    
    [::&parser/defalias ?name ?type-def]
    (exec [_ (&util/with-field :types
               (&type/define-type ?name ?type-def))]
      (return [::&type/nil]))

    [::&parser/field-access ?field ?obj]
    (exec [=obj (check* ?obj)
           [class =field] (&util/with-field :types
                            (&type/member-candidates [?field :fields]))]
      (fn-call =field (list =obj)))
    
    [::&parser/method-call ?method ?obj ?args]
    (exec [=obj (check* ?obj)
           =args (map-m check* ?args)
           [class =method] (&util/with-field :types
                             (&type/member-candidates [?method :methods]))
           _ (&util/with-field :types
               (exec [=object (&type/instantiate* class [])]
                 (&type/solve =object =obj)))
           =method (fn-call =method (list =obj))]
      (fn-call =method =args))

    [::&parser/new ?class ?args]
    (exec [=args (map-m check* ?args)
           [_ =ctor] (&util/with-field :types
                       (&type/member-candidates [?class :ctor]))]
      (fn-call =ctor =args))

    [::&parser/fn-call ?fn ?args]
    (if-let [[?class ?method] (match ?fn
                                [::&parser/symbol ?symbol]
                                (if-let [ns (namespace ?symbol)]
                                  [(symbol ns) (symbol (name ?symbol))])

                                :else
                                nil)]
      (exec [=args (map-m check* ?args)
             [class =method] (&util/with-field :types
                               (&type/member-candidates [?method :static-methods]))
             =method (if (= class ?class)
                       (return =method)
                       zero)]
        (fn-call =method =args))
      (exec [=fn (check* ?fn)
             =args (map-m check* ?args)
             =fn (match =fn
                   [::&type/hole _]
                   (&util/with-field :types
                     (exec [=fn-type (fresh-poly-fn (count =args))
                            _ (&type/solve =fn-type =fn)]
                       (return =fn-type)))
                   
                   :else
                   (return =fn))
             =return (fn-call =fn =args)]
        (return =return)))
    ))

;; [Interface]
;; Contants
(def +init+ (Context. &env/+init+ &type/+init+))

;; Functions
(defn check [form]
  #(let [results ((exec [type (check* form)]
                    (prettify-type nil type)) %)]
     (if (empty? results)
       '()
       (do ;; (prn '(count results) (count results) (mapv second results))
         ((&util/with-field :types
            (reduce-m &type/parallel [::&type/nothing] (mapv second results)))
          %)))
     ))
