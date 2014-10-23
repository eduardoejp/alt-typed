(ns system
  (:require [clojure.set :as set]
            [clojure.template :refer [do-template]]
            [clojure.core.match :refer [match]]))

(defprotocol Monad
  (bind [monad m-value step])
  (return [monad value]))

(def zero (fn [state] (list)))

(def state-seq-m
  (reify Monad
    (bind [self m-value step]
      #(do ;; (prn 'm-value m-value 'step step)
           (for [[state* datum] (m-value %)
                 result ((step datum) state*)]
             result)))
    (return [self value]
      #(list [% value]))))

(def state-m
  (reify Monad
    (bind [self m-value step]
      #(let [[state* datum] (m-value %)
             result ((step datum) state*)]
         result))
    (return [self value]
      #(vector % value))))

(def maybe-m
  (reify Monad
    (bind [self m-value step]
      (if (nil? m-value)
        nil
        (step m-value)))
    (return [self value]
      value)))

(defn return-all [data]
  #(for [datum data]
     [% datum]))

(defmacro exec [monad steps return]
  (assert (not= 0 (count steps)) "The steps can't be empty!")
  (assert (= 0 (rem (count steps) 2)) "The number of steps must be even!")
  (reduce (fn [inner [label computation]]
            (case label
              :let `(let ~computation ~inner)
              ;; else
              `(bind ~monad ~computation (fn [~label] ~inner))))
          `(return ~monad ~return)
          (reverse (partition 2 steps))))

(def fresh-type-var
  (fn [state]
    (let [id (:counter/type-vars state)]
      (list [(-> state
                 (update-in [:counter/type-vars] inc)
                 (assoc-in [:mapping/type-vars id] (list [:any] [:nothing])))
             [:var id]]))))


(defn bind-local [local type]
  (fn [state]
    (let [id (:counter/locals state)]
      (list [(-> state
                 (update-in [:counter/locals] inc)
                 (assoc-in [:mapping/locals id] type)
                 (update-in [:env/locals] conj {local id}))
             id]))))

(def ^:private unbind-local
  #(let [mapped (-> % :env/locals first vals)]
     (list [(-> %
                (update-in [:env/locals] rest)
                (update-in [:mapping/locals] (fn [mappings] (reduce dissoc mappings mapped))))
            nil])))

(def get-state
  #(list [% %]))

(defn annotate [var-sym type]
  #(if (get-in % [:type/anns var-sym])
     (zero nil)
     (list [(assoc-in % [:type/anns var-sym] type) nil])))

(defn learn-type [name =type]
  #(list [(assoc-in % [:type/types name] =type) nil]))

(defmacro cond-let [binding then & clauses]
  `(if-let ~binding
     ~then
     ~(case (count clauses)
        0 nil
        1 (first clauses)
        ;; else
        `(cond-let ~@clauses))))

(defn parallel [steps]
  (fn [state]
    (some identity (map #(seq (% state)) steps))))

(defn collect [step]
  #(list [% (step %)]))

(defn spread [returns]
  (fn [state] returns))

(defn resolve-var [symbol]
  #(if-let [=type (get-in % [:type/anns symbol])]
     (list [% =type])
     (zero nil)))

(defn resolve-symbol [symbol]
  #(if-let [$local (do ;; (prn 'resolve-symbol symbol (->> % :env/locals (some symbol)) (:env/locals %))
                       (->> % :env/locals (some symbol)))]
     (list [% [:bound $local]])
     ((resolve-var symbol) %)))

(defn deref-local [$local]
  #(if-let [=type (get-in % [:mapping/locals $local])]
     (list [% =type])
     (zero nil)))

(defn deref-type-var [$var]
  #(if-let [top+bottom (get-in % [:mapping/type-vars $var])]
     (list [% top+bottom])
     (zero nil)))

(defn update-local [$local type]
  #(list [(assoc-in % [:mapping/locals $local] type) true]))

(defn update-type-var [$var top bottom]
  #(list [(assoc-in % [:mapping/type-vars $var] [top bottom]) true]))

(defn map-m [monad f inputs]
  (if (empty? inputs)
    (return monad '())
    (exec monad
      [output (f (first inputs))
       outputs (map-m monad f (rest inputs))]
      (conj outputs output))))

(defn reduce-m [monad f init inputs]
  (if (empty? inputs)
    (return monad init)
    (exec monad
      [next (f init (first inputs))
       end (reduce-m monad f next (rest inputs))]
      end)))

(defn ^:private clean-env [to-clean type]
  (match type
    [:bound ?local]
    (exec state-seq-m
      [=type (deref-local ?local)
       =type (clean-env to-clean =type)
       _ (update-local ?local =type)]
      (if (contains? to-clean ?local)
        =type
        type))

    [:var ?id]
    (exec state-seq-m
      [[=top =bottom] (deref-type-var ?id)
       =top (clean-env to-clean =top)
       =bottom (clean-env to-clean =bottom)
       _ (update-type-var ?id =top =bottom)]
      type)

    [:object ?class ?params]
    (exec state-seq-m
      [=params (map-m state-seq-m (partial clean-env to-clean) ?params)]
      [:object ?class =params])

    
    [:union ?types]
    (exec state-seq-m
      [=types (map-m state-seq-m (partial clean-env to-clean) ?types)]
      [:union =types])

    
    [:complement ?type]
    (exec state-seq-m
      [=type (clean-env to-clean ?type)]
      [:complement =type])
    
    :else
    (return state-seq-m type)))

(defn exit-env [type]
  (exec state-seq-m
    [state get-state
     =type (clean-env (-> state :env/locals first vals set) type)
     _ unbind-local]
    =type))

(def +falsey+ [:union (list [:nil] [:literal 'java.lang.Boolean false])])
(def +truthy+ [:complement +falsey+])
(def ^:private +ambiguous+ [:any])

(defn unify [expected actual]
  (prn 'unify expected actual)
  (match [expected actual]
    [_ [:bound ?id]]
    (exec state-seq-m
      [=type (deref-local ?id)
       _ (unify expected =type)]
      true)

    [_ [:var ?id]]
    (exec state-seq-m
      [[=top =bottom] (deref-type-var ?id)
       _ (parallel [(unify expected =top)
                    (exec state-seq-m
                      [_ (unify =top expected)
                       _ (update-type-var ?id expected =bottom)]
                      true)])]
      true)

    [[:any] _]
    (return state-seq-m true)

    [_ [:nothing]]
    (return state-seq-m true)

    [[:nil] [:nil]]
    (return state-seq-m true)

    [[:literal ?e-class ?e-value] [:literal ?a-class ?a-value]]
    (do (prn '[[:literal _ _] [:literal _ _]] [expected actual]
             `(~'= ~?e-class ~?a-class) (.equals ?e-class ?a-class)
             `(~'= ~?e-value ~?a-value) (= ?e-value ?a-value)
             (and (= ?e-class ?a-class)
                  (= ?e-value ?a-value)))
      (if (and (= ?e-class ?a-class)
               (= ?e-value ?a-value))
        (return state-seq-m true)
        zero))

    [[:object ?class _] [:literal ?lit-class _]]
    (if (= ?class ?lit-class)
      (return state-seq-m true)
      zero)

    [[:object ?e-class ?e-params] [:object ?a-class ?a-params]]
    (if (= ?e-class ?a-class)
      (exec state-seq-m
        [_ (map-m state-seq-m
                  (fn [[e a]] (unify e a))
                  (map vector ?e-params ?a-params))]
        true)
      zero)

    [[:union ?types] _]
    (exec state-seq-m
      [=type (return-all ?types)
       _ (unify =type actual)]
      true)

    [[:complement ?type] _]
    (fn [state]
      (prn '[[:complement ?type] actual]
           [[:complement ?type] actual]
           (count ((unify ?type actual) state)))
      (let [;; results-1 ((unify ?type actual) state)
            ;; results-2 ((unify actual ?type) state)
            ]
        ;; (prn '[[:complement ?type] _] 'results results)
        (if (and (empty? ((unify ?type actual) state))
                 (empty? ((unify actual ?type) state)))
          (list [state true])
          (zero nil))))

    :else
    zero
    ))

(defn refine-local [local type]
  ;; (prn 'refine-local local type)
  (match type
    [:union ?types]
    (exec state-seq-m
      [=type (return-all ?types)
       _ (parallel [(unify +truthy+ =type)
                    (unify +falsey+ =type)
                    (unify +ambiguous+ =type)])
       _ (update-local local =type)]
      =type)
    
    [:object 'java.lang.Boolean []]
    (exec state-seq-m
      [=type (return-all (list [:literal java.lang.Boolean true]
                               [:literal java.lang.Boolean false]))
       _ (update-local local =type)]
      =type)

    :else
    (return state-seq-m type)
    ))

(defn refine [type-check form]
  (prn 'refine form)
  (exec state-seq-m
    [=form (type-check form)
     state get-state
     :let [_ (prn 'refine/=form =form 'state state)]
     =form (match =form
             [:bound local]
             (exec state-seq-m
               [=type (deref-local local)
                ;; :let [_ (prn '(deref-local local) =form)]
                =type (refine-local local =type)
                ;; :let [_ (prn '(refine-local local =form) =type)]
                ]
               =form)

             :else
             (return state-seq-m =form))]
    =form))

(defn clean [type]
  (match type
    [:bound ?local]
    (exec state-seq-m
      [=type (deref-local ?local)
       ;; :let [_ (prn 'clean type ?local =type)]
       =type (clean =type)]
      =type)

    [:var ?id]
    (exec state-seq-m
      [[=top =bottom] (deref-type-var ?id)
       ;; :let [_ (prn '[=top =bottom] [=top =bottom])]
       =top (clean =top)]
      =top)
    
    :else
    (return state-seq-m type)))

(defn type-check-arity [=arity =args]
  ;; (prn 'type-check-arity =arity =args)
  (match =arity
    [:arity ?args ?return]
    (exec state-seq-m
      [_ (map-m state-seq-m (partial apply unify) (map vector ?args =args))]
      ?return)))

(defn fn-call [=fn =args]
  ;; (prn 'fn-call =fn =args)
  (match =fn
    [:function ?arities]
    (exec state-seq-m
      [=arity (return-all (for [[_ args _ :as arity] ?arities
                                :when (= (count args) (count =args))]
                            arity))
       =return (type-check-arity =arity =args)]
      =return)
    ))

(defn extract-vars [type]
  (match type
    [:bound ?local]
    (exec state-seq-m
      [=type (deref-local ?local)
       vars (extract-vars =type)]
      vars)
    
    [:var ?id]
    (return state-seq-m (list ?id))

    [:object _ ?params]
    (map-m state-seq-m extract-vars ?params)

    [:union ?types]
    (map-m state-seq-m extract-vars ?types)

    [:complement ?type]
    (extract-vars ?type)
    
    :else
    (return state-seq-m '())))

(defn prettify-type [mappings type]
  (match type
    [:bound ?local]
    (exec state-seq-m
      [=type (deref-local ?local)
       =type (prettify-type mappings =type)]
      =type)
    
    [:var ?id]
    (if-let [var-name (get mappings ?id)]
      (return state-seq-m var-name)
      (exec state-seq-m
        [[=top =bottom] (deref-type-var ?id)
         =top (prettify-type mappings =top)]
        =top))

    [:object ?class ?params]
    (exec state-seq-m
      [=params (map-m state-seq-m (partial prettify-type mappings) ?params)]
      [:object ?class =params])

    [:union ?types]
    (exec state-seq-m
      [=types (map-m state-seq-m (partial prettify-type mappings) ?types)]
      [:union =types])

    [:complement ?type]
    (exec state-seq-m
      [=type (prettify-type mappings ?type)]
      [:complement =type])

    [:arity ?args ?body]
    (exec state-seq-m
      [=args (map-m state-seq-m (partial prettify-type mappings) ?args)
       =body (prettify-type mappings ?body)]
      [:arity =args =body])
    
    :else
    (return state-seq-m type)))

(let [+var-names+ (for [idx (iterate inc 1)
                        alphabet "abcdefghijklmnopqrstuvwxyz"]
                    (if (= 1 idx)
                      (symbol (str alphabet))
                      (symbol (str alphabet idx))))]
  (defn generalize-arity [arity]
    ;; (prn 'generalize-arity arity)
    (match arity
      [:arity ?args ?body]
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
        (if (empty? used-vars)
          arity*
          [:all (vec used-vars) arity*]))
      )))

(defn classify [worlds]
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
                              (list [% [:union (map second take)]]))]
         (concat classification ((classify leave) %))))))

;; (defn classify [refinements outputs]
;;   (if (empty? refinements)
;;     zero
;;     (let [[[state [_ ?id] :as ref1] & others] refinements
;;           [take leave] (reduce (fn [[take leave] [state* _ :as pair]]
;;                                  (if (= (update-in state [:mapping/locals] dissoc ?id)
;;                                         (update-in state* [:mapping/locals] dissoc ?id))
;;                                    [(conj take pair) leave]
;;                                    [take (conj leave pair)]))
;;                                [[] []]
;;                                others)
;;           all-to-take (cons ref1 take)
;;           ;; _ (prn 'all-to-take all-to-take)
;;           [taken-pairs left-pairs] (reduce (fn [[take leave] [state* =output :as pair]]
;;                                              (if (some (partial = state) (map first all-to-take))
;;                                                [(conj take pair) leave]
;;                                                [take (conj leave pair)]))
;;                                            [[] []]
;;                                            outputs)
;;           clean-comp (exec state-seq-m
;;                        [=type (spread taken-pairs)
;;                         =type (clean-env #{?id} =type)]
;;                        =type)
;;           ;; _ (prn 'taken-pairs taken-pairs)
;;           ;; _ (prn 'left-pairs left-pairs)
;;           ;; _ (prn '(clean-comp %) (clean-comp state))
;;           ]
;;       (parallel [#(if-let [types (seq (map second (clean-comp %)))]
;;                     (list [% [:union types]])
;;                     (zero nil))
;;                  (classify leave left-pairs)]))))

(defn merge-arities [worlds]
  (if (empty? worlds)
    zero
    (let [[[state arity :as world] & others] worlds
          [taken left] (reduce (fn [[taken left] [state* arity* :as world*]]
                                 (match [arity arity*]
                                   [[:arity ?args ?body] [:arity ?args* ?body*]]
                                   (if (= ?args ?args*)
                                     [(conj taken world*) left]
                                     [taken (conj left world*)])))
                               [[world] []]
                               others)]
      (fn [state]
        (let [batch (if (= 1 (count taken))
                      (list [state (-> taken first (nth 1))])
                      (list [state (let [returns [:union (map #(-> % (nth 1) (nth 2)) taken)]]
                                     (-> taken first (nth 1) (assoc-in [2] returns)))]))]
          (concat batch ((merge-arities left) state))))
      )))

(defn type-check [form]
  ;; (prn 'type-check form)
  (match form
    [:form/#nil]
    (return state-seq-m [:nil])
    
    [:form/#boolean ?value]
    (return state-seq-m [:literal 'java.lang.Boolean ?value])

    [:form/#integer ?value]
    (return state-seq-m [:literal 'java.lang.Long ?value])

    [:form/#real ?value]
    (return state-seq-m [:literal 'java.lang.Double ?value])

    [:form/#big-int ?value]
    (return state-seq-m [:literal 'clojure.lang.BigInt ?value])

    [:form/#big-decimal ?value]
    (return state-seq-m [:literal 'java.math.BigDecimal ?value])

    [:form/#ratio ?value]
    (return state-seq-m [:literal 'clojure.lang.Ratio ?value])

    [:form/#character ?value]
    (return state-seq-m [:literal 'java.lang.Character ?value])

    [:form/#string ?value]
    (return state-seq-m [:literal 'java.lang.String ?value])

    [:form/#regex ?value]
    (return state-seq-m [:literal 'java.util.regex.Pattern ?value])

    [:form/#keyword ?value]
    (return state-seq-m [:literal 'clojure.lang.Keyword ?value])

    [:form/#vector ?value]
    (if (empty? ?value)
      (return state-seq-m [:object 'clojure.lang.IPersistentVector [[:nothing]]])
      (exec state-seq-m
        [=members (map-m state-seq-m type-check ?value)]
        [:object 'clojure.lang.IPersistentVector [[:union =members]]]))

    [:form/#map ?value]
    (if (empty? ?value)
      (return state-seq-m [:object 'clojure.lang.IPersistentMap [[:nothing] [:nothing]]])
      (exec state-seq-m
        [=members (map-m state-seq-m type-check (seq ?value))
         :let [[=k =v] (reduce (fn [[ks vs] [k v]]
                                 [(conj ks k) (conj vs v)])
                               [[] []]
                               (partition 2 =members))]]
        [:object 'clojure.lang.IPersistentMap [[:union =k] [:union =v]]]))

    [:form/#set ?value]
    (if (empty? ?value)
      (return state-seq-m [:object 'clojure.lang.IPersistentSet [[:nothing]]])
      (exec state-seq-m
        [=members (map-m state-seq-m type-check ?value)]
        [:object 'clojure.lang.IPersistentSet [[:union =members]]]))
    
    [:form/symbol ?symbol]
    (resolve-symbol ?symbol)

    [:form/do & ?forms]
    (case (count ?forms)
      0 (return state-seq-m [:nil])
      1 (type-check (first ?forms))
      ;; else
      (exec state-seq-m
        [=forms (map-m state-seq-m type-check ?forms)]
        (last =forms)))
    
    [:form/let ([[?label ?value] & ?bindings] :seq) ?body]
    (exec state-seq-m
      [=value (type-check ?value)
       $value (bind-local ?label =value)
       =body (if (empty? ?bindings)
               (type-check ?body)
               (type-check [:form/let ?bindings ?body]))
       =body (exit-env =body)]
      =body)

    [:form/if ?test ?then ?else]
    (exec state-seq-m
      [=test (refine type-check ?test)
       =output (parallel [(exec state-seq-m
                            [_ (unify +truthy+ =test)
                             =then (type-check ?then)
                             ;; :let [_ (prn ':form/if '=then =then)]
                             ]
                            =then)
                          (exec state-seq-m
                            [_ (unify +falsey+ =test)
                             =else (type-check ?else)
                             ;; :let [_ (prn ':form/if '=else =else)]
                             ]
                            =else)
                          (exec state-seq-m
                            [_ (unify +ambiguous+ =test)
                             =then (type-check ?then)
                             =else (type-check ?else)
                             ;; :let [_ (prn ':form/if '=then =then '=else =else)]
                             ]
                            [:union (list =then =else)])])]
      =output)
    ;; (exec state-seq-m
    ;;   [;; =test (refine type-check ?test)
    ;;    refinements (collect (refine type-check ?test))
    ;;    outputs (collect (exec state-seq-m
    ;;                       [=test (spread refinements)
    ;;                        =output (parallel [(exec state-seq-m
    ;;                                             [_ (unify +truthy+ =test)
    ;;                                              =then (type-check ?then)
    ;;                                              ;; :let [_ (prn ':form/if '=then =then)]
    ;;                                              ]
    ;;                                             =then)
    ;;                                           (exec state-seq-m
    ;;                                             [_ (unify +falsey+ =test)
    ;;                                              =else (type-check ?else)
    ;;                                              ;; :let [_ (prn ':form/if '=else =else)]
    ;;                                              ]
    ;;                                             =else)
    ;;                                           (exec state-seq-m
    ;;                                             [_ (unify +ambiguous+ =test)
    ;;                                              =then (type-check ?then)
    ;;                                              =else (type-check ?else)
    ;;                                              ;; :let [_ (prn ':form/if '=then =then '=else =else)]
    ;;                                              ]
    ;;                                             [:union (list =then =else)])])
    ;;                        :let [_ (prn '=output =output)]]
    ;;                       =output))
    ;;    ;; :let [_ (prn 'refinements refinements)
    ;;    ;;       _ (prn 'outputs outputs)
    ;;    ;;       _ (prn '(classify refinements outputs) (classify refinements outputs))]
    ;;    =output (classify refinements outputs)]
    ;;   =output)

    [:form/def ?var]
    (exec state-seq-m
      [=value (return state-seq-m [:nothing])
       _ (annotate ?var =value)]
      [:object 'clojure.lang.Var [=value]])

    [:form/def ?var ?value]
    (exec state-seq-m
      [=value (type-check ?value)
       _ (annotate ?var =value)]
      [:object 'clojure.lang.Var [=value]])

    [:form/var ?var]
    (exec state-seq-m
      [=var (resolve-var ?var)]
      [:object 'clojure.lang.Var [=var]])


    [:form/fn ?local-name ?args ?body]
    (exec state-seq-m
      [worlds (collect (exec state-seq-m
                         [=fn fresh-type-var
                          $fn (bind-local ?local-name =fn)
                          =args (map-m state-seq-m
                                       (fn [arg]
                                         (exec state-seq-m
                                           [=arg fresh-type-var
                                            $arg (bind-local arg =arg)]
                                           =arg))
                                       ?args)
                          ;; all-returns (collect (type-check `[:form/do ~@?body]))
                          =body (type-check `[:form/do ~@?body]) ;; (classify all-returns)
                          :let [_ (prn '=body =body)]
                          =body (reduce-m state-seq-m
                                          (fn [=body =args]
                                            (exec state-seq-m
                                              [=clean (exit-env =body)]
                                              =clean))
                                          =body
                                          =args)
                          :let [_ (prn '(exit-env =body) =body)]
                          ;; _ (map-m state-seq-m (fn [_] unbind-local) =args)
                          =body (exit-env =body)
                          =arity (generalize-arity [:arity =args =body])]
                         =arity))
       =fn (case (count worlds)
             0 zero
             1 (spread worlds)
             ;; else
             (exec state-seq-m
               [arities (collect (merge-arities worlds))]
               [:function (map second arities)]))]
      =fn)
    ;; (if (= :all (first =arity))
    ;;   (let [[_ ?vars ?body] =arity]
    ;;     [:all ?vars [:function (list ?body)]])
    ;;   [:function (list =arity)])

    ;; (exec state-seq-m
    ;;   [;; =test (refine type-check ?test)
    ;;    refinements (collect (refine type-check ?test))
    ;;    outputs (collect (exec state-seq-m
    ;;                       [=test (spread refinements)
    ;;                        =output (parallel [(exec state-seq-m
    ;;                                             [_ (unify +truthy+ =test)
    ;;                                              =then (type-check ?then)
    ;;                                              ;; :let [_ (prn ':form/if '=then =then)]
    ;;                                              ]
    ;;                                             =then)
    ;;                                           (exec state-seq-m
    ;;                                             [_ (unify +falsey+ =test)
    ;;                                              =else (type-check ?else)
    ;;                                              ;; :let [_ (prn ':form/if '=else =else)]
    ;;                                              ]
    ;;                                             =else)
    ;;                                           (exec state-seq-m
    ;;                                             [_ (unify +ambiguous+ =test)
    ;;                                              =then (type-check ?then)
    ;;                                              =else (type-check ?else)
    ;;                                              ;; :let [_ (prn ':form/if '=then =then '=else =else)]
    ;;                                              ]
    ;;                                             [:union (list =then =else)])])
    ;;                        :let [_ (prn '=output =output)]]
    ;;                       =output))
    ;;    ;; :let [_ (prn 'refinements refinements)
    ;;    ;;       _ (prn 'outputs outputs)
    ;;    ;;       _ (prn '(classify refinements outputs) (classify refinements outputs))]
    ;;    =output (classify refinements outputs)]
    ;;   =output)

    [:form/ann ?var ?type]
    (annotate ?var ?type)

    [:form/defalias ?name ?params ?type-def]
    (let [=type (if (empty? ?params)
                  [:alias ?name ?type-def]
                  [:type-ctor ?params [:alias ?name ?type-def]])]
      (exec state-seq-m
        [_ (learn-type ?name =type)]
        [:nil]))

    [:form/fn-call ?fn ?args]
    (exec state-seq-m
      [=fn (type-check ?fn)
       =args (map-m state-seq-m type-check ?args)
       =return (fn [state]
                 (let [returns ((fn-call =fn =args) state)]
                   (prn 'returns returns)
                   returns))]
      =return)
    ))

(defn type-check-full [form]
  (fn [state]
    (let [results ((type-check form) state)]
      (case (count results)
        0 '()
        1 (list [state (-> results first (nth 1))])
        ;; else
        (list [state [:union (map second ((type-check form) state))]])
        ))
    ))

(defn ^:private parse-arity [parse-type-def type-def]
  (match type-def
    [& ?parts]
    (let [[args [_ return]] (split-with (partial not= '->) ?parts)]
      [:arity (map parse-type-def args) (parse-type-def return)])))

(defn parse-type-def [type-def]
  (match type-def
    nil
    [:nil]

    (?value :guard (partial instance? java.lang.Boolean))
    [:literal 'java.lang.Boolean ?value]

    (?value :guard (partial instance? clojure.lang.BigInt))
    [:literal 'clojure.lang.BigInt ?value]

    (?value :guard (partial instance? java.math.BigDecimal))
    [:literal 'java.math.BigDecimal ?value]

    (?value :guard integer?)
    [:literal 'java.lang.Long ?value]

    (?value :guard float?)
    [:literal 'java.lang.Double ?value]

    (?value :guard ratio?)
    [:literal 'clojure.lang.Ratio ?value]
    
    (?value :guard (partial instance? java.lang.Character))
    [:literal 'java.lang.Character ?value]

    (?value :guard string?)
    [:literal 'java.lang.String ?value]

    (?value :guard (partial instance? java.util.regex.Pattern))
    [:literal 'java.util.regex.Pattern ?value]

    (?value :guard keyword?)
    [:literal 'clojure.lang.Keyword ?value]
    
    (['Or & ?params] :seq)
    `[:union ~(mapv parse-type-def ?params)]

    (['Not ?inner] :seq)
    [:complement (parse-type-def ?inner)]
    
    (?name :guard symbol?)
    [:object ?name []]
    
    [& ?parts]
    [:function (list (parse-arity parse-type-def type-def))]

    (['Fn & ?arities] :seq)
    [:function (map (partial parse-arity parse-type-def) ?arities)]
    ))

(defn type-ctor? [x]
  (or (symbol? x)
      (and (seq? x)
           (>= (count x) 2))))

(defn parse [code]
  ;; (prn 'parse code)
  (match code
    nil
    [:form/#nil]
    
    (?value :guard (partial instance? java.lang.Boolean))
    [:form/#boolean ?value]

    (?value :guard (partial instance? clojure.lang.BigInt))
    [:form/#big-int ?value]

    (?value :guard (partial instance? java.math.BigDecimal))
    [:form/#big-decimal ?value]

    (?value :guard integer?)
    [:form/#integer ?value]

    (?value :guard float?)
    [:form/#real ?value]

    (?value :guard ratio?)
    [:form/#ratio ?value]
    
    (?value :guard (partial instance? java.lang.Character))
    [:form/#character ?value]

    (?value :guard string?)
    [:form/#string ?value]

    (?value :guard (partial instance? java.util.regex.Pattern))
    [:form/#regex ?value]

    (?value :guard keyword?)
    [:form/#keyword ?value]

    (?value :guard symbol?)
    [:form/symbol ?value]

    (?value :guard vector?)
    [:form/#vector (mapv parse ?value)]
    
    (?value :guard map?)
    [:form/#map (into {} (for [[k v] ?value] [(parse k) (parse v)]))]
    
    (?value :guard set?)
    [:form/#set (set (map parse ?value))]

    (['do & ?forms] :seq)
    `[:form/do ~@(map parse ?forms)]

    (['let (?bindings :guard vector?) & ?body] :seq)
    (do (assert (even? (count ?bindings)) "LET must have an even number of elements.")
      (let [bindings* (for [[?label ?value] (partition 2 ?bindings)]
                        [?label (parse ?value)])]
        [:form/let bindings* `[:form/do ~@(map parse ?body)]]))

    (['if ?test ?then & [?else]] :seq)
    [:form/if (parse ?test) (parse ?then) (parse ?else)]

    (['def (?var :guard symbol?)] :seq)
    [:form/def ?var]
    
    (['def (?var :guard symbol?) ?value] :seq)
    [:form/def ?var (parse ?value)]

    (['var (?var :guard symbol?)] :seq)
    [:form/var ?var]

    (['ann (?var :guard symbol?) ?type-def] :seq)
    [:form/ann ?var (parse-type-def ?type-def)]

    (['defalias (?ctor :guard type-ctor?) ?type-def] :seq)
    (let [[name args] (if (symbol? ?ctor)
                        [?ctor []]
                        [(first ?ctor) (rest ?ctor)])]
      [:form/defalias name args (parse-type-def ?type-def)])

    (['fn ?local-name (?args :guard vector?) & ?body] :seq)
    [:form/fn ?local-name ?args (map parse ?body)]

    ([?fn & ?args] :seq)
    [:form/fn-call (parse ?fn) (map parse ?args)]
    ))

(def +default-context+ {:counter/locals 0
                        :mapping/locals {}
                        :counter/type-vars 0
                        :mapping/type-vars {}
                        :type/types {'String [:object 'String []]
                                     'Long   [:object 'Long []]}
                        :type/anns {}
                        :env/locals '()})

(defn type->code [type]
  (match type
    [:any] 'Any
    [:nothing] 'Nothing
    [:nil] nil
    [:literal _ ?value] ?value
    [:object ?class ?params] (if (empty? ?params)
                               ?class
                               `(~?class ~@(map type->code ?params)))
    [:union ?types] `(~'Or ~@(map type->code ?types))
    [:complement ?tyoe] `(~'Not ~(type->code ?tyoe))
    [:arity ?args ?return] `[~@(map type->code ?args) ~'-> ~(type->code ?return)]
    [:function ?arities] (if (= 1 (count ?arities))
                           (type->code (first ?arities))
                           `(~'Fn ~@(map type->code ?arities)))
    [:all ?vars ?poly] `(~'All ~(vec ?vars) ~(type->code ?poly))
    (?type-var :guard symbol?) ?type-var
    ))

(comment
  (defn run-type-checker [code]
    ((type-check code) +default-context+))

  (parse true)
  (parse '(let [foo true] false))

  (run-type-checker '(do (ann parse-int [String -> (Or nil Long)])
                       (parse-int "1234")))

  
  
  (time (do (defonce _init_
              (do (alter-var-root #'clojure.core/prn
                                  (constantly #(.println System/out (apply pr-str %&))))))
          
          (defn run-type-checker [code]
            (for [[_ type] ((-> code parse type-check-full) +default-context+)]
              (doto (type->code type)
                (->> pr-str (println "Type:")))))
          
          (do-template [<type> <form>]
            (assert (= '(<type>) (run-type-checker '<form>)))
            
            nil
            nil

            true
            true

            10
            10

            10.0
            10.0

            \a
            \a

            :lol
            :lol

            10N
            10N

            10M
            10M

            1/2
            1/2

            nil
            (do nil)
            
            (clojure.lang.Var Nothing)
            (def foo)

            (clojure.lang.Var nil)
            (def foo (do nil))

            nil
            (let [foo nil]
              nil)

            10
            (let [foo 10]
              foo)

            nil
            (do (def foo nil)
              foo)

            (clojure.lang.Var 10)
            (do (def foo 10)
              #'foo)

            (Or nil java.lang.Long)
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (parse-int "1234"))

            nil
            (defalias (Maybe x) (Or nil x))

            (Or "YOLO" java.lang.Long)
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (let [result (parse-int "1234")]
                (if result
                  result
                  "YOLO")))

            (All [a] [a -> a])
            (fn foo [x] x)

            (clojure.lang.IPersistentVector Nothing)
            []

            (clojure.lang.IPersistentMap Nothing Nothing)
            {}

            (clojure.lang.IPersistentSet Nothing)
            #{}

            (clojure.lang.IPersistentVector (Or :klk "YOLO"))
            [:klk "YOLO"]
            
            [java.lang.String -> (Or nil java.lang.Long)]
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (fn foo [x]
                (parse-int x)))

            [java.lang.String -> (Or "YOLO" java.lang.Long)]
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (fn foo [x]
                (let [result (parse-int x)]
                  (if result
                    result
                    "YOLO"))))

            (Fn [clojure.lang.IPersistentMap -> :klk]
                [(Not clojure.lang.IPersistentMap) -> "manito"])
            (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                              [(Not clojure.lang.IPersistentMap) -> false]))
              (fn foo [x]
                (if (map? x)
                  :klk
                  "manito")))
            
            (Fn [clojure.lang.IPersistentMap -> :yolo]
                [(Not clojure.lang.IPersistentMap) -> "lol"])
            (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                              [(Not clojure.lang.IPersistentMap) -> false]))
              (fn foo [x]
                (let [? (map? x)]
                  (if ?
                    :yolo
                    "lol"))))

            (Fn [clojure.lang.IPersistentMap -> "manito"]
                [(Not clojure.lang.IPersistentMap) -> :klk])
            (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                              [(Not clojure.lang.IPersistentMap) -> false]))
              (fn foo [x]
                (let [x (if (map? x)
                          "manito"
                          :klk)]
                  x)))
            )
          ))

  ;; MISSING: quote
  ;; MISSING: throw, try, catch, finally
  ;; MISSING: loop, recur
  ;; MISSING: def(protocol|type|record)
  ;; MISSING: class hierarchies
  ;; MISSING: multimethods
  ;; MISSING: records & tuples
  ;; MISSING: gen-class
  ;; MISSING: Java interop
  ;; MISSING: binding
  ;; MISSING: monitor-enter & monitor-leave
  ;; MISSING: proxy & reify
  ;; MISSING: case
  ;; MISSING: ns management
  ;; MISSING: treating objects as IFn (like keywords & maps)

  ;; The one below is not supposed to type-check due to lack of
  ;; coverage of type possibilities.
  (run-type-checker '(do (ann get-object [-> java.lang.Object])
                       (ann use-case (Fn [String -> :yolo]
                                         [Integer -> :lol]
                                         [Boolean -> :meme]))
                       (fn foo []
                         (use-case (get-object)))))

  ;; This is a valid way of implementing letfn using a macro...
  ;; (let [odd* (fn [odd even]
  ;;              (fn [x]
  ;;                (if (= 0 x)
  ;;                  false
  ;;                  ((even odd even) (dec x)))))
  ;;       even* (fn [odd even]
  ;;               (fn [x]
  ;;                 (if (= 0 x)
  ;;                   true
  ;;                   ((odd odd even) (dec x)))))
  ;;       odd (odd* odd* even*)
  ;;       even (even* odd* even*)]
  ;;   (odd 21))
  
  ;; (def (** base exp)
  ;;   (reduce * 1 (repeat base exp)))

  ;; (class **
  ;;   (execute [base exp]
  ;;     (reduce * 1 (repeat base exp))))
  
  ;; (reify Function
  ;;   (apply [self base]
  ;;     (reify Function
  ;;       (apply [self exp]
  ;;         (.execute ** base exp)))))
  
  ;; (defprotocol Function
  ;;   (apply [self x]))

  ;; ($math 10 < x < (20 ** 5))

  
  )
