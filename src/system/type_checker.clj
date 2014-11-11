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
    [::&type/ref _]
    (exec [=type (&util/with-field :types
                   (&type/get-ref type))
           :let [=type (match =type
                         [::&type/interval ?top ?bottom]
                         ?top
                         
                         :else
                         =type)]
           =type (clean-env to-clean =type)
           _ (&util/with-field :types
               (&type/set-ref type =type))]
      (if (contains? to-clean type)
        (return =type)
        (return type)))
    
    ;; [::&type/var _]
    ;; (exec
    ;;   [=interval (&util/with-field :types
    ;;                (&type/deref-var type))
    ;;    :let [[=top =bottom] (match =interval
    ;;                           [::&type/interval =top =bottom]
    ;;                           [=top =bottom])]
    ;;    =top (clean-env to-clean =top)
    ;;    =bottom (clean-env to-clean =bottom)
    ;;    _ (&util/with-field :types
    ;;        (&type/update-var type [::&type/interval =top =bottom]))]
    ;;   (return type))

    [::&type/object ?class ?params]
    (exec [=params (map-m (partial clean-env to-clean) ?params)]
      (return [::&type/object ?class =params]))

    [::&type/union ?types]
    (exec [=types (map-m (partial clean-env to-clean) ?types)]
      (&util/with-field :types
        (&type/$or (vec =types))))

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

(defn ^:private extract-holes [type]
  (prn 'extract-holes type)
  (match type
    [::&type/hole _]
    (exec [:let [_ (prn '=hole/original type)]
           =hole (&util/with-field :types
                   (&type/normalize-hole type))
           :let [_ (prn '=hole/normal =hole)]
           =interval (&util/with-field :types
                       (&type/get-hole =hole))
           :let [[=top =bottom] (match =interval
                                  [::&type/interval =top =bottom]
                                  [=top =bottom])]
           at-top (extract-holes =top)
           :let [_ (prn 'at-top at-top)]
           at-bottom (extract-holes =bottom)
           :let [_ (prn 'at-bottom at-bottom)]
           :let [total-count (merge-with + {=hole 1} at-top at-bottom)]
           :let [_ (prn 'total-count total-count)]]
      (return total-count))
    
    [::&type/ref _]
    (exec [=type (&util/with-field :types
                   (&type/get-ref type))
           ;; :let [_ (prn '=type =type)]
           ]
      (extract-holes =type))
    
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
    (exec [all-holes (map-m extract-holes ?arities)
           :let [_ (prn 'function/all-holes all-holes)]]
      (return (apply merge-with + all-holes)))

    [::&type/arity ?args ?return]
    (exec [all-holes (map-m extract-holes ?args)
           return-holes (extract-holes ?return)
           :let [_ (prn 'arity/all-holes return-holes all-holes)]]
      (return (apply merge-with + return-holes all-holes)))
    
    :else
    (return {})))

(defn ^:private prettify-type [mappings type]
  (prn 'prettify-type mappings type)
  (match type
    [::&type/hole _]
    (if-let [var-name (get mappings type)]
      (return var-name)
      (exec [=type (&util/with-field :types
                     (&type/normalize-hole type))]
        (if-let [var-name (get mappings =type)]
          (return var-name)
          (exec [=interval (&util/with-field :types
                             (&type/get-hole =type))
                 :let [[=top =bottom] (match =interval
                                        [::&type/interval =top =bottom]
                                        [=top =bottom])]
                 ;; =top (prettify-type mappings =top)
                 ;; =bottom (prettify-type mappings =bottom)
                 ;; _ (&util/with-field :types
                 ;;     (&type/narrow-hole type =top =bottom))
                 ]
            ;; (return type)
            (prettify-type mappings =top)))))
    
    [::&type/ref _]
    (exec [=type (&util/with-field :types
                   (&type/get-ref type))
           :let [_ (prn '=type =type)]]
      (prettify-type mappings =type))

    [::&type/var _]
    (&util/try-all [(exec [=type (&util/with-field :types
                                   (&type/deref-var type))
                           ;; _ (fn [state]
                           ;;     (prn '(:types state) (:types state))
                           ;;     (list [state nil]))
                           :let [_ (prn 'prettify-type '[::&type/var _] =type)]
                           =type* (prettify-type mappings =type)
                           _ (&util/with-field :types
                               (&type/rebind-var type =type*))]
                      (return type))
                    (return type)])
    
    ;; (&util/try-all [(exec [=type (&util/with-field :types
    ;;                                (&type/deref-var type))
    ;;                        :let [_ (prn 'prettify-type '[::&type/var _] =type)]]
    ;;                   (prettify-type mappings =type))
    ;;                 (return [::&type/any])])
    
    ;; [::&type/var _]
    ;; (if-let [var-name (get mappings type)]
    ;;   (return var-name)
    ;;   (exec
    ;;     [=interval (&util/with-field :types
    ;;                  (&type/deref-var type))
    ;;      :let [[=top =bottom] (match =interval
    ;;                             [::&type/interval =top =bottom]
    ;;                             [=top =bottom])]]
    ;;     (prettify-type mappings =top)))

    [::&type/object ?class ?params]
    (exec [=params (map-m (partial prettify-type mappings) ?params)]
      (return [::&type/object ?class =params]))

    [::&type/union ?types]
    (exec [=types (map-m (partial prettify-type mappings) ?types)]
      (&util/with-field :types
        (&type/$or =types)))

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

(defn ->pretty [type]
  (prn '->pretty type)
  (match type
    [::&type/ref _]
    (exec [=type (&util/with-field :types
                   (&type/get-ref type))
           :let [_ (prn '=type =type)]]
      (->pretty =type))

    [::&type/var _]
    (exec [=type (&util/with-field :types
                   (&type/deref-var type))]
      (->pretty =type))
    
    ;; [::&type/var _]
    ;; (exec
    ;;   [=interval (&util/with-field :types
    ;;                (&type/deref-var type))
    ;;    :let [[=top =bottom] (match =interval
    ;;                           [::&type/interval =top =bottom]
    ;;                           [=top =bottom])]]
    ;;   (->pretty =top))

    [::&type/object ?class ?params]
    (exec [=params (map-m ->pretty ?params)]
      (return [::&type/object ?class =params]))

    [::&type/union ?types]
    (exec [=types (map-m ->pretty ?types)]
      (&util/with-field :types
        (&type/$or =types)))

    [::&type/complement ?type]
    (exec [=type (->pretty ?type)]
      (return [::&type/complement =type]))

    [::&type/arity ?args ?body]
    (exec [=args (map-m ->pretty ?args)
           =body (->pretty ?body)]
      (return [::&type/arity =args =body]))

    [::&type/function ?arities]
    (exec [=arities (map-m ->pretty ?arities)]
      (return [::&type/function =arities]))
    
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
    (match arity
      [::&type/arity ?args ?body]
      (exec [body-vars (extract-holes ?body)
             :let [_ (prn 'body-vars body-vars)]
             args-vars (exec [all-holes (map-m extract-holes ?args)
                              :let [_ (prn 'args-vars/all-holes all-holes)]]
                         (return (apply merge-with + all-holes)))
             :let [_ (prn 'args-vars args-vars)]
             :let [poly-vars (merge-with + args-vars body-vars)
                   _ (prn 'poly-vars poly-vars)
                   poly-vars (sort < (for [[k cnt] poly-vars
                                           :when (> cnt 1)]
                                       (nth k 1)))
                   _ (prn 'poly-vars poly-vars)
                   used-vars (take (count poly-vars) +var-names+)
                   _ (prn 'used-vars used-vars)
                   mappings (into {} (map (fn [id name]
                                            [[::&type/hole id] name])
                                          poly-vars used-vars))
                   _ (prn 'mappings mappings)
                   rev-mappings (set/map-invert mappings)
                   _ (prn 'rev-mappings rev-mappings)]
             :let [_ (prn 'generalize-arity/arity arity)]
             _ (fn [state]
                 (prn '(get-in state [:types :heap]) (get-in state [:types :heap]))
                 (list [state nil]))
             arity* (prettify-type mappings arity)
             :let [_ (prn 'generalize-arity/arity* arity*)]
             _ (fn [state]
                 (prn '(get-in state [:types :heap]) (get-in state [:types :heap]))
                 (list [state nil]))]
        (if (empty? used-vars)
          (return arity*)
          (exec [user-vars* (map-m (fn [uv]
                                     (exec [=interval (&util/with-field :types
                                                        (&type/get-hole (get rev-mappings uv)))
                                            :let [[=top =bottom] (match =interval
                                                                   [::&type/interval =top =bottom]
                                                                   [=top =bottom])]]
                                       (return (if (= [::&type/any] =top)
                                                 uv
                                                 [uv :< =top]))))
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
                                                          (&type/parallel-combine-types (mapv #(-> % (nth 1) (nth 2)) taken))) state)]
                                     (-> taken first (nth 1) (assoc-in [2] returns)))])
                      )]
          (concat batch ((merge-arities left) state))))
      )))

(defn ^:private refine-local [types local type]
  (prn 'refine-local local type)
  (match type
    [::&type/union ?types]
    (exec [=type (return-all ?types)
           _ (&util/try-all (mapv (fn [expected]
                                    (&util/with-field :types
                                      (&type/solve expected =type)))
                                  types))
           :let [_ (prn "Setting" local "to" =type)]
           _ (&util/with-field :types
               (&type/set-ref local =type))]
      (return nil))
    
    [::&type/object 'java.lang.Boolean []]
    (exec [=type (return-all (list [::&type/literal java.lang.Boolean true]
                                   [::&type/literal java.lang.Boolean false]))
           _ (&util/with-field :types
               (&type/set-ref local =type))]
      (return nil))
    
    :else
    (return type)
    ))

(defn ^:private refine [check* types =form]
  (prn 'refine =form types)
  (exec [_ (match =form
             [::&type/ref _]
             (exec [=type (&util/with-field :types
                            (&type/get-ref =form))
                    _ (refine-local types =form =type)]
               (return true))

             :else
             (return true))]
    (return =form)))

(defn ^:private check-arity [=arity =args]
  (prn 'check-arity =arity =args)
  (match =arity
    [::&type/arity ?args ?return]
    (exec [_ (map-m
              (fn [[arg input]]
                (&util/with-field :types
                  (&type/solve arg input)))
              (map vector ?args =args))]
      (return ?return))))

(defn ^:private fn-call [=fn =args]
  (prn 'fn-call =fn =args)
  (exec [=fn (&util/with-field :types
               (exec [=fn (&type/instantiate =fn)]
                 (if (&type/type-fn? =fn)
                   (fn-call =fn =args)
                   (&type/upcast ::&type/$fn =fn))))
         :let [_ (prn 'fn-call '=fn =fn)]
         ]
    (match =fn
      [::&type/function ?arities]
      (exec [=arity (return-all (for [[_ args _ :as arity] ?arities
                                      :when (= (count args) (count =args))]
                                  arity))
             :let [_ (prn 'fn-call '=arity =arity)]
             ]
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
    (if (empty? ?value)
      (return [::&type/object 'clojure.lang.PersistentList [[::&type/nothing]]])
      (exec [=elems (map-m check* ?value)
             =elems (&util/with-field :types
                      (&type/$or (vec =elems)))]
        (return [::&type/object 'clojure.lang.PersistentList [=elems]])))
    
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
    (if (empty? ?value)
      (return [::&type/object 'clojure.lang.IPersistentSet [[::&type/nothing]]])
      (exec [=elems (map-m check* ?value)
             =elems (&util/with-field :types
                      (&type/$or (vec =elems)))]
        (return [::&type/object 'clojure.lang.IPersistentSet [=elems]])))
    
    [::&parser/symbol ?symbol]
    (if-let [ns (namespace ?symbol)]
      (exec [[class =field] (&util/with-field :types
                              (&type/member-candidates [(-> ?symbol name symbol) :static-fields]))
             :when (= class (symbol ns))]
        (return =field))
      (exec [=symbol (&util/with-field :env
                       (&env/resolve ?symbol))
             :when (not= [::&type/macro] =symbol)]
        (return =symbol)))
    
    [::&parser/do & ?forms]
    (case (count ?forms)
      0 (return [::&type/nil])
      1 (exec [?form (&parser/parse (first ?forms))]
          (check* ?form))
      ;; else
      (exec [=forms (map-m
                     (fn [?form]
                       (exec [?form (&parser/parse ?form)]
                         (check* ?form)))
                     ?forms)
             =body (&type/sequentially-combine-types =forms)]
        (return =body)))

    [::&parser/let ([[?label ?value] & ?bindings] :seq) ?body]
    (exec [=value (check* ?value)
           [?label =value] (match ?label
                             [::&parser/symbol ?local]
                             (exec [_ (&util/with-field :types
                                        (&type/solve [::&type/any] =value))]
                               (return [?local =value])))
           =binding (&util/with-field :types
                      (&type/create-ref =value))]
      (with-env {?label =binding}
        (if (empty? ?bindings)
          (check* ?body)
          (check* [::&parser/let ?bindings ?body]))))

    [::&parser/if ?test ?then ?else]
    (exec [=test (check* ?test)
           :let [_ (prn ::&parser/if '=test =test)]
           =test (refine check* [&type/+truthy+ &type/+falsey+ [::&type/any]] =test)
           :let [_ (prn ::&parser/if '=test =test)]]
      (&util/try-all [(exec [_ (&util/with-field :types
                                 (&type/solve &type/+truthy+ =test))
                             =then (check* ?then)]
                        (return =then))
                      (exec [_ (&util/with-field :types
                                 (&type/solve &type/+falsey+ =test))
                             =else (check* ?else)]
                        (return =else))
                      (exec [_ (&util/with-field :types
                                 (&type/solve [::&type/any] =test))
                             =then (check* ?then)
                             =else (check* ?else)]
                        (&util/with-field :types
                          (&type/parallel-combine-types [=then =else])))
                      ]))

    [::&parser/case ?value ?clauses ?default]
    (exec [=branches* (map-m
                       (fn [[?test ?form]]
                         (exec [=test (if (seq? ?test)
                                        (exec [?parts (map-m check* ?test)]
                                          (&util/with-field :types
                                            (&type/$or (vec ?parts))))
                                        (check* ?test))]
                           (return [=test ?form])))
                       ?clauses)
           =value (check* ?value)
           =value (refine check* (mapv first =branches*) =value)
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
    (exec [=locals (map-m
                    (fn [[label value]]
                      (exec [=value (&util/with-field :env
                                      (&env/resolve value))]
                        (return [label =value])))
                    ?locals)
           locals-pre (map-m
                       #(exec [=bound (&util/with-field :env
                                        (&env/resolve %))]
                          (&util/with-field :types
                            (&type/get-ref =bound)))
                       (mapv first =locals))
           _ (with-env (into {::recur (mapv first =locals)}
                             =locals)
               (check* ?body))
           locals-post (map-m
                        #(exec [=bound (&util/with-field :env
                                         (&env/resolve %))]
                           (&util/with-field :types
                             (&type/get-ref =bound)))
                        (mapv first =locals))]
      (with-env (into {::recur (mapv first =locals)}
                      =locals)
        (check* ?body)))

    [::&parser/recur ?args]
    (exec [=recur (&util/with-field :env
                    (&env/resolve ::recur))
           =recur (map-m
                   #(&util/with-field :env
                      (&env/resolve %))
                   =recur)
           _ (if (= (count =recur) (count ?args))
               (return nil)
               zero)
           =args (map-m check* ?args)
           _ (map-m
              (fn [[=e =a]]
                (exec [=wider (&util/with-field :types
                                (exec [_ (&type/solve =a =e)
                                       =e (&type/get-ref =e)]
                                  (&type/$or [=e =a])))]
                  (&util/with-field :types
                    (&type/set-ref =e =wider))))
              (map vector =recur =args))]
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
           =all-returning (&type/parallel-combine-types (cons =clean-body =catches))]
      (&type/sequentially-combine-types [=finally =all-returning]))

    [::&parser/catch ?class ?label ?body]
    (with-env {?label [::&type/object ?class []]}
      (check* ?body))
    
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
    (exec [worlds (&util/collect (exec [=fn (&util/with-field :types
                                              &type/fresh-hole)
                                        =args (map-m (fn [_]
                                                       (&util/with-field :types
                                                         &type/fresh-hole))
                                                     ?args)
                                        =return (with-env {?local-name =fn}
                                                  (with-env (into {} (map vector ?args =args))
                                                    (check* ?body)))]
                                   (generalize-arity [::&type/arity =args =return])))]
      (case (count worlds)
        0 zero
        1 (exec [=arity (&util/spread worlds)]
            (return [::&type/function (list =arity)]))
        ;; else
        (exec [=arities (&util/collect (merge-arities worlds))]
          (return [::&type/function (map second =arities)]))))

    [::&parser/ann ?var ?type]
    (exec [_ (&util/with-field :env
               (&env/intern ?var ?type))]
      (return [::&type/nil]))

    [::&parser/ann-class ?class ?parents ?fields+methods]
    (exec [=class (&util/with-field :types
                    (&type/define-class ?class ?parents))
           all-categories+members (map-m
                                   (fn [[category members]]
                                     (if (= :ctor category)
                                       (exec [=ctor (&parser/parse-type-def {} members)]
                                         (return [:ctor =ctor]))
                                       (exec [all-members+types (map-m
                                                                 (fn [[name type]]
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
             :let [_ (prn '=fn =fn)]
             =args (map-m check* ?args)
             :let [_ (prn '=args =args)]
             =fn (match =fn
                   [::&type/hole _]
                   (&util/with-field :types
                     (exec [=fn* (&type/get-hole =fn)
                            :let [_ (prn '=fn* =fn*)]
                            =fn-type (fresh-poly-fn (count =args))
                            :let [_ (prn '=fn-type =fn-type)]
                            ;; =fn-type (&type/instantiate =fn-type)
                            ;; :let [_ (prn '=fn-type =fn-type)]
                            _ (&type/solve =fn-type =fn)]
                       (return =fn-type)))
                   
                   :else
                   (return =fn))
             :let [_ (prn '=fn =fn)]
             =return (fn-call =fn =args)
             :let [_ (prn '=return =return)]]
        (return =return)))
    ))

;; [Interface]
;; Contants
(def +init+ (Context. &env/+init+ &type/+init+))

;; Functions
(defn check [form]
  #(let [results ((exec [raw (check* form)]
                    (->pretty raw))
                  %)]
     (case (count results)
       0 '()
       1 (list [% (-> results first (nth 1))])
       ;; else
       ((&util/with-field :types
          (&type/parallel-combine-types (mapv second results)))
        %)
       )))
