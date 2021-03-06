(ns system.type-checker
  (:require [clojure.set :as set]
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [exec
                                            map-m reduce-m
                                            zero fail return return-all]]
                    [env :as &env]
                    [type :as &type]
                    [parser :as &parser]))
  (:import (system.env Env)))

;; [Data]
(defrecord Context [env types])

;; [Utils]
(defn with-env [env inner]
  (exec [:let [bound-ids (-> env vals set)]
         _ (&util/with-field :env
             (&env/enter env))
         =type* inner
         =type (&util/with-field :types
                 (&type/clean-env bound-ids =type*))
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

(let [+var-names+ (for [idx (iterate inc 1)
                        alphabet "abcdefghijklmnopqrstuvwxyz"]
                    (if (= 1 idx)
                      (symbol (str alphabet))
                      (symbol (str alphabet idx))))]
  (defn ^:private generalize-arity [arity]
    ;; (prn 'generalize-arity arity)
    (match arity
      [::&type/arity ?args ?body]
      (exec [body-vars (&util/with-field :types
                         (&type/holes ?body))
             ;; :let [_ (prn 'body-vars body-vars)]
             args-vars (exec [all-holes (&util/with-field :types
                                          (map-m &type/holes ?args))]
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
             arity* (&util/with-field :types
                      (&type/prettify mappings arity))]
        (if (empty? used-vars)
          (return arity*)
          (exec [user-vars* (map-m (fn [uv]
                                     (exec [[=top =bottom] (&util/with-field :types
                                                             (&type/get-hole (get rev-mappings uv)))]
                                       (return [uv (if (and (= &type/+any+ =top)
                                                            (not= &type/+nothing+ =bottom))
                                                     =bottom
                                                     =top)])))
                                   used-vars)]
            (return [::&type/all {} (vec user-vars*) arity*])))
        ))))

(defn generalize-function [type]
  (match type
    [::&type/function ?arities]
    (exec [=arities (map-m generalize-arity ?arities)]
      (return [::&type/function =arities]))))

(defn separate [pred seq]
  [(filter pred seq)
   (filter (complement pred) seq)])

(defn ^:private merge-arities [worlds]
  ;; (prn 'merge-arities (map second worlds))
  (if (empty? worlds)
    (return '())
    (let [[[_ arity :as world] & others] worlds
          [taken* left] (separate (fn [[_ arity*]]
                                    (match [arity arity*]
                                      [[::&type/all {} ?vars [::&type/arity ?args ?body]]
                                       [::&type/all {} ?vars* [::&type/arity ?args* ?body*]]]
                                      (and (= ?vars ?vars*) (= ?args ?args*))

                                      [[::&type/arity ?args ?body] [::&type/arity ?args* ?body*]]
                                      (= ?args ?args*)

                                      :else
                                      false))
                                  others)
          taken (conj taken* world)
          ;; _ (prn 'merge-arities/taken (map second taken))
          ]
      (exec [=current (if (= 1 (count taken))
                        (return (-> taken first second))
                        (exec [=returns (&util/with-field :types
                                          (reduce-m &type/parallel &type/+nothing+ (map #(-> % second (nth 2)) taken)))]
                          (return (-> taken first second (assoc-in [2] =returns)))))
             =left (merge-arities left)]
        (return (conj =left =current))))
    ))

(defn check* [form]
  ;; (prn 'check* form)
  (match form
    [::&parser/#nil]
    (return &type/+nil+)
    
    [::&parser/#boolean ?value]
    (&type/$literal ?value)
    
    [::&parser/#integer ?value]
    (&type/$literal ?value)

    [::&parser/#real ?value]
    (&type/$literal ?value)

    [::&parser/#big-int ?value]
    (&type/$literal ?value)

    [::&parser/#big-decimal ?value]
    (&type/$literal ?value)

    [::&parser/#ratio ?value]
    (&type/$literal ?value)

    [::&parser/#character ?value]
    (&type/$literal ?value)

    [::&parser/#string ?value]
    (&type/$literal ?value)

    [::&parser/#regex ?value]
    (&type/$literal ?value)

    [::&parser/#keyword ?value]
    (&type/$literal ?value)

    [::&parser/#symbol ?value]
    (&type/$literal ?value)

    [::&parser/#list ?value]
    (exec [=elems (map-m check* ?value)
           =elems (&util/with-field :types
                    (reduce-m &type/$or &type/+nothing+ =elems))]
      (&util/with-field :types
        (&type/instantiate* 'clojure.lang.PersistentList [=elems])))

    [::&parser/#set ?value]
    (exec [=elems (map-m check* ?value)
           =elems (&util/with-field :types
                    (reduce-m &type/$or &type/+nothing+ =elems))]
      (&util/with-field :types
        (&type/instantiate* 'clojure.lang.IPersistentSet [=elems])))
    
    [::&parser/#vector ?value]
    (exec [=elems (map-m check* ?value)]
      (&util/with-field :types
        (&type/$tuple =elems)))

    [::&parser/#map ?value]
    (exec [=elems (map-m (fn [[?k ?v]]
                           (exec [=k (check* ?k)
                                  =v (check* ?v)]
                             (return [=k =v])))
                         (seq ?value))]
      (&util/with-field :types
        (&type/$record (into {} =elems))))

    [::&parser/symbol ?symbol]
    (if-let [ns (namespace ?symbol)]
      (exec [[class =field] (&util/with-field :types
                              (&type/member-candidates [(-> ?symbol name symbol) :static-fields]))
             :when (= class (symbol ns))]
        (return =field))
      (&util/try-all [(exec [=symbol (&util/with-field :env
                                       (&env/resolve ?symbol))]
                        (if (not= &type/+macro+ =symbol)
                          (return =symbol)
                          (fail (str "Can't get value of a macro. [" ?symbol "]"))))
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
        (reduce-m &type/sequential &type/+nil+ =forms)))

    [::&parser/let ([[?label ?value] & ?bindings] :seq) ?body]
    (exec [=value (check* ?value)
           [?label =value] (match ?label
                             [::&parser/symbol ?local]
                             (return [?local =value]))
           ;; :let [_ (prn ::&parser/let '[?label =value] [?label =value])]
           =binding (&util/with-field :types
                      (exec [=hole (&type/fresh-var ?label)
                             _ (&type/narrow-hole =hole =value &type/+nothing+)]
                        (return =hole)))
           ;; :let [_ (prn ::&parser/let '=binding =binding)]
           ]
      (with-env {?label =binding}
        (if (empty? ?bindings)
          (check* ?body)
          (check* [::&parser/let ?bindings ?body]))))

    [::&parser/if ?test ?then ?else]
    (exec [=test (check* ?test)
           ;; :let [_ (prn ::&parser/if ?test =test)]
           ]
      (&util/try-all [(&util/parallel [(exec [_ (&util/with-field :types
                                                  (&type/solve &type/+truthy+ =test))
                                              =test* (if (&type/type-var? =test)
                                                       (exec [[=top =bottom] (&util/with-field :types
                                                                               (&type/get-hole =test))]
                                                         (return =top))
                                                       (return =test))
                                              :when (and (not= =test* &type/+nothing+)
                                                         (not= =test* &type/+boolean+))
                                              ;; :let [_ (prn 'THEN ?then)]
                                              ]
                                         (check* ?then))
                                       (exec [_ (&util/with-field :types
                                                  (&type/solve &type/+falsey+ =test))
                                              =test* (if (&type/type-var? =test)
                                                       (exec [[=top =bottom] (&util/with-field :types
                                                                               (&type/get-hole =test))]
                                                         (return =top))
                                                       (return =test))
                                              :when (and (not= =test* &type/+nothing+)
                                                         (not= =test* &type/+boolean+))
                                              ;; :let [_ (prn 'ELSE ?else)]
                                              ]
                                         (check* ?else))])
                      (exec [_ (&util/with-field :types
                                 (&type/solve &type/+ambiguous+ =test))
                             =then (check* ?then)
                             =else (check* ?else)
                             ;; :let [_ (prn 'THEN-ELSE =then =else)]
                             =then+else (&util/with-field :types
                                          (&type/parallel =then =else))
                             ;; :let [_ (prn 'THEN+ELSE =then+else)]
                             ]
                        (return =then+else))
                      ]))
    
    [::&parser/case ?value ?clauses ?default]
    (exec [=branches* (map-m
                       (fn [[?test ?form]]
                         (exec [=test (if (seq? ?test)
                                        (exec [?parts (map-m check* ?test)]
                                          (&util/with-field :types
                                            (reduce-m &type/$or &type/+nothing+ ?parts)))
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
                                                  _ (&type/narrow-hole =hole &type/+any+ =top)
                                                  ;; [=top* =bottom*] (&type/get-hole =hole)
                                                  ;; :let [_ (prn ::&parser/loop =hole [=top* =bottom*])]
                                                  ]
                                             (return =hole)))]
                              (return [label =hole])))
                          ?locals)
           =body (with-env (into {::recur (mapv second =locals)}
                                 =locals)
                   (check* ?body))
           ;; :let [_ (prn 'loop/=body =body)]
           ]
      ;; (clean-holes (into #{} (map second =locals)) =body)
      (return =body))

    [::&parser/recur ?args]
    (exec [=recur (&util/with-field :env
                    (&env/resolve ::recur))
           _ (&util/assert! (= (count =recur) (count ?args)) (str "Mismatch in recur arguments. Expected: " (count =recur) " Actual: " (count ?args)))
           =args (map-m check* ?args)
           _ (&util/with-field :types
               (map-m (fn [[=e =a]] (&type/solve =a =e))
                      (map vector =recur =args)))]
      (return &type/+nothing+))

    [::&parser/set! ?target ?value]
    (exec [=value (check* ?value)
           =target (check* ?target)
           _ (&util/with-field :types
               (&type/solve =target =value))]
      (return =value))

    [::&parser/assert ?test ?message]
    (exec [=message (check* ?message)
           _ (&util/with-field :types
               (&type/solve &type/+any+ =message))
           =test (check* ?test)
           _ (&util/with-field :types
               (&util/try-all [(&type/solve &type/+truthy+ =test)
                               (if (= &type/+boolean+ =test)
                                 (return true)
                                 zero)]))]
      (return &type/+nil+))
    
    [::&parser/def ?var ?value]
    (exec [=value (if ?value
                    (check* ?value)
                    (return &type/+nothing+))
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
               (exec [=throwable (&type/instantiate* 'java.lang.Throwable)]
                 (&type/solve =throwable =ex)))]
      (&util/try-all [(&util/parallel [(&util/with-field :types
                                         (exec [=throwable (&type/instantiate* 'java.lang.Throwable)
                                                =error (&type/instantiate* 'java.lang.Error)
                                                =run-ex (&type/instantiate* 'java.lang.RuntimeException)
                                                =!error (&type/$not =error)
                                                =!run-ex (&type/$not =run-ex)
                                                =showable (reduce-m &type/$and =throwable [=!error =!run-ex])
                                                ;; :let [_ (prn '=showable =showable)]
                                                _ (&type/solve =showable =ex)]
                                           (return [::&type/eff &type/+nothing+ {:try =ex}])))
                                       (&util/with-field :types
                                         (exec [=error (&type/instantiate* 'java.lang.Error)
                                                =run-ex (&type/instantiate* 'java.lang.RuntimeException)
                                                =showable (reduce-m &type/$or =error [=run-ex])
                                                ;; :let [_ (prn '=showable =showable)]
                                                _ (&type/solve =showable =ex)]
                                           (if (&type/type-var? =ex)
                                             (exec [[=top =bottom :as =ex*] (&type/get-hole =ex)]
                                               (fn [state]
                                                 (if (not (&util/failed? ((&type/solve &type/+nothing+ =top) state)))
                                                   (&util/fail* (str "Can't match this exception... [" =ex "]"))
                                                   (&util/send-ok state &type/+nothing+))))
                                             (fn [state]
                                               (if (not (&util/failed? ((&type/solve &type/+nothing+ =ex) state)))
                                                 (&util/fail* (str "Can't match this exception... [" =ex "]"))
                                                 (&util/send-ok state &type/+nothing+))))
                                           
                                           ;; (&util/try-all [(exec [_ (&type/solve &type/+nothing+ =ex)]
                                           ;;                   (fail (str "Can't match this exception... [" =ex "]")))
                                           ;;                 (return &type/+nothing+)])
                                           ))])
                      (&util/with-field :types
                        (exec [=showable (&type/instantiate* 'java.lang.Exception)
                               _ (&type/solve =showable =ex)]
                          (return [::&type/eff &type/+nothing+ {:try =ex}])))
                      (fail (str "Can't match this exception... [" =ex "]"))]))
    
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
                            (reduce-m &type/parallel &type/+nothing+ (cons =clean-body =catches)))]
      (&util/with-field :types
        (&type/sequential =finally =all-returning)))

    [::&parser/catch ?class ?label ?body]
    (exec [=ex (&util/with-field :types
                 (&type/instantiate* ?class))]
      (with-env {?label =ex}
        (check* ?body)))
    
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
           _ (&util/assert! (&type/multi-fn? =multi-fn) (str ?name " is not a multimethod."))]
      (match =multi-fn
        [::&type/multi-fn ?dispatch-fn ?methods]
        (exec [=args (&util/with-field :types
                       (map-m (constantly &type/fresh-hole) ?args))
               ;; :let [_ (prn "#2")]
               =dispatch-val (check* ?dispatch-val)
               ;; :let [_ (prn '=dispatch-val =dispatch-val)
               ;;       _ (prn '?dispatch-fn ?dispatch-fn)]
               ;; :let [_ (prn "#3")]
               =return (&util/with-field :types
                         (&type/fn-call ?dispatch-fn =args))
               ;; :let [_ (prn "#4")]
               ;; :let [_ (prn '=return =return)]
               _ (&util/with-field :types
                   (&type/solve =return =dispatch-val))
               ;; =return* (&util/with-field :types
               ;;            (&type/prettify nil =return))
               ;; :let [_ (prn '=return* =return* '=dispatch-val =dispatch-val)]
               ;; =args* (&util/with-field :types
               ;;          (map-m (partial &type/prettify nil) =args))
               ;; :let [_ (prn '=args =args =args*)]
               ;; :let [_ (prn "#5" =return =dispatch-val =args)]
               worlds (&util/collect (exec [=return (with-env* (into {} (map vector ?args =args))
                                                      (check* ?body))]
                                       (generalize-arity [::&type/arity =args =return])))
               ;; :let [_ (prn "#6")]
               =new-multi-fn (exec [=arities (merge-arities (&util/results worlds))
                                    :let [=new-multi-fn [::&type/multi-fn ?dispatch-fn (into ?methods =arities)]]
                                    _ (&util/with-field :env
                                        (&env/intern ?name =new-multi-fn))]
                               (return =new-multi-fn))
               ;; :let [_ (prn "#7")]
               ]
          (return =new-multi-fn))))
    
    [::&parser/monitor-enter ?object]
    (exec [;; :let [_ (prn [::&parser/monitor-enter ?object])]
           =object (check* ?object)
           ;; :let [_ (prn '=object =object)]
           _ (&util/with-field :types
               (exec [=limit (&type/$not &type/+nil+)
                      ;; :let [_ (prn '=limit =limit)]
                      ]
                 (&type/solve =limit =object)))
           ;; :let [_ (prn 'DONE)]
           ]
      (return &type/+nil+))

    [::&parser/monitor-exit ?object]
    (exec [=object (check* ?object)
           _ (&util/with-field :types
               (exec [=limit (&type/$not &type/+nil+)]
                 (&type/solve =limit =object)))]
      (return &type/+nil+))

    [::&parser/binding ?bindings ?body]
    (exec [_ (map-m (fn [[label value]]
                      (match label
                        [::&parser/symbol ?label]
                        (exec [=var (&util/with-field :env
                                      (&env/resolve-var ?label))
                               =value (check* value)]
                          (&util/with-field :types
                            (&type/solve =var =value)))
                        
                        :else
                        (fail "The left side of a binding MUST be a symbol.")))
                    ?bindings)]
      (check* ?body))
    
    [::&parser/fn ?local-name ?args ?body]
    (let [[pre-post ?body] (match ?body
                             [::&parser/do & ?forms]
                             (if (and (map? (first ?forms))
                                      (or (contains? (first ?forms) :pre)
                                          (contains? (first ?forms) :post)))
                               [(first ?forms) `[::&parser/do ~@(rest ?forms)]]
                               [nil ?body]))]
      (exec [all-pre (map-m #(&parser/parse `(~'assert ~%)) (:pre pre-post))
             ;; state &util/get-state
             ;; :let [_ (prn 'all-pre all-pre 'state state)]
             all-post (map-m #(&parser/parse `(~'assert ~%)) (:post pre-post))
             ;; state &util/get-state
             ;; :let [_ (prn 'all-post all-post 'state state)]
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
                                          _ (&util/with-field :types
                                              (if-let [tag (-> ?local-name meta :tag)]
                                                (exec [=return-limit (&type/instantiate* tag)
                                                       _ (&type/solve =return-limit =return)]
                                                  (return nil))
                                                (return nil)))
                                          _ (with-env* {'% =return}
                                              (map-m check* all-post))
                                          ;; :let [_ (prn 'fn/=return =return)]
                                          ;; :let [_ (println "#2")]
                                          ]
                                     (generalize-arity [::&type/arity =args =return])))
             ;; :let [_ (prn ::&parser/fn 'worlds worlds)]
             ]
        (exec [=arities (merge-arities (&util/results worlds))]
          (return [::&type/function =arities]))))
    
    [::&parser/ann ?var ?type]
    (exec [_ (&util/with-field :env
               (&env/intern ?var ?type))]
      (return &type/+nil+))

    [::&parser/ann-class ?class ?parents ?fields+methods]
    (exec [;; :let [_ (prn 'CHECK ::&parser/ann-class 0)]
           =class (&util/with-field :types
                    (&type/define-class ?class ?parents))
           ;; :let [_ (prn 'CHECK ::&parser/ann-class 1)]
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
           ;; :let [_ (prn 'CHECK ::&parser/ann-class 2)]
           _ (&util/with-field :types
               (&type/define-class-members (nth ?class 0) (into {} all-categories+members)))
           ;; :let [_ (prn 'CHECK ::&parser/ann-class 3)]
           ]
      (return &type/+nil+))
    
    [::&parser/defalias ?name ?type-def]
    (exec [_ (&util/with-field :types
               (&type/define-type ?name ?type-def))]
      (return &type/+nil+))

    [::&parser/field-access ?field ?obj]
    (exec [=obj (check* ?obj)
           [class =field] (&util/with-field :types
                            (&type/member-candidates [?field :fields]))]
      (&util/with-field :types
        (&type/fn-call =field (list =obj))))
    
    [::&parser/method-call ?method ?obj ?args]
    (exec [=obj (check* ?obj)
           ;; :let [_ (prn '=obj =obj)]
           =args (map-m check* ?args)
           ;; :let [_ (prn '=args =args)]
           [class =method] (&util/with-field :types
                             (&type/member-candidates [?method :methods]))
           ;; :let [_ (prn '[class =method] [class =method])]
           _ (&util/with-field :types
               (exec [=object (&type/instantiate* class [])]
                 (&type/solve =object =obj)))
           =method (&util/with-field :types
                     (&type/fn-call =method (list =obj)))
           ;; :let [_ (prn '=method =method)]
           ]
      (&util/with-field :types
        (&type/fn-call =method =args)))

    [::&parser/new ?class ?args]
    (exec [=args (map-m check* ?args)
           [_ =ctor] (&util/with-field :types
                       (&type/member-candidates [?class :ctor]))]
      (&util/with-field :types
        (&type/fn-call =ctor =args)))

    [::&parser/protocol ?var ?methods]
    (exec [=methods (map-m (fn [method]
                             (match method
                               [::&parser/pmethod ?name ?arities]
                               (exec [=fn (&util/with-field :types
                                            (&type/poly-fn* (first ?arities)))
                                      =fn (generalize-function =fn)]
                                 (return [?name =fn]))))
                           ?methods)
           _ (&util/with-field :env
               (&env/intern ?var [::&type/protocol ?var (into {} =methods)]))]
      (&type/$literal ?var))

    [::&parser/deftype ?class ?args ?impls]
    (exec [=args (&util/with-field :types
                   (map-m &type/fresh-var ?args))
           :let [global-env (into {} (map vector ?args =args))]
           =impls (with-env* global-env
                    (map-m (fn [[protocol methods]]
                             (exec [=protocol (&util/with-field :env
                                                (&env/resolve protocol))
                                    =signatures (match =protocol
                                                  [::&type/protocol _ ?signatures]
                                                  (return ?signatures)
                                                  
                                                  :else
                                                  zero)
                                    :when (= (set (keys =signatures)) (set (keys methods)))
                                    =methods (map-m (fn [[f-name [[f-args f-body]]]]
                                                      (exec [=f-type (check* [::&parser/fn f-name f-args `[::&parser/do ~@f-body]])]
                                                        (return [f-name =f-type])))
                                                    methods)
                                    :let [=methods (into {} =methods)]]
                               (return [protocol =methods])))
                           ?impls))
           :let [=impls (into {} =impls)]
           ;; :let [_ (println "#1")]
           _ (check* [::&parser/ann-class [?class [] []] [] []])
           ;; :let [_ (println "#2")]
           ]
      (check* [::&parser/symbol ?class]))

    [::&parser/defrecord ?class ?args ?impls]
    (check* [::&parser/deftype ?class ?args ?impls])

    [::&parser/reify ?impls]
    (exec [=impls (map-m (fn [[protocol methods]]
                           (exec [=protocol (&util/with-field :env
                                              (&env/resolve protocol))
                                  =signatures (match =protocol
                                                [::&type/protocol _ ?signatures]
                                                (return ?signatures)
                                                
                                                :else
                                                zero)
                                  :when (= (set (keys =signatures)) (set (keys methods)))
                                  =methods (map-m (fn [[f-name [[f-args f-body]]]]
                                                    (exec [=f-type (check* [::&parser/fn f-name f-args `[::&parser/do ~@f-body]])]
                                                      (return [f-name =f-type])))
                                                  methods)
                                  :let [=methods (into {} =methods)]]
                             (return [protocol =methods])))
                         ?impls)]
      (return [::&type/reify =impls]))

    [::&parser/extend ?class ?impls]
    (exec [=impls (map-m (fn [[protocol methods]]
                           (exec [=protocol (&util/with-field :env
                                              (&env/resolve protocol))
                                  =signatures (match =protocol
                                                [::&type/protocol _ ?signatures]
                                                (return ?signatures)
                                                
                                                :else
                                                zero)
                                  :when (= (set (keys =signatures)) (set (keys methods)))
                                  =methods (map-m (fn [[f-name fn-code]]
                                                    (exec [*fn-code (&parser/parse fn-code)
                                                           =f-type (check* *fn-code)]
                                                      (return [f-name =f-type])))
                                                  methods)
                                  :let [=methods (into {} =methods)]]
                             (return [protocol =methods])))
                         ?impls)
           :let [=impls (into {} =impls)
                 ;; _ (prn '=impls =impls)
                 ]]
      (return &type/+nil+))
    
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
        (&util/with-field :types
          (&type/fn-call =method =args)))
      (exec [=fn (check* ?fn)
             =args (map-m check* ?args)
             =fn (if (&type/type-var? =fn)
                   (&util/with-field :types
                     (exec [=fn-type (&type/poly-fn (count =args))
                            _ (&type/solve =fn-type =fn)]
                       (return =fn-type)))
                   (return =fn))
             =return (&util/with-field :types
                       (&type/fn-call =fn =args))]
        (return =return)))
    ))

;; [Interface]
;; Contants
(def +init+ (Context. &env/+init+ &type/+init+))

;; Functions
(defn check [form]
  (exec [worlds (&util/collect (exec [;; state &util/get-state
                                      ;; :let [_ (prn 'check/form form (class state) state)]
                                      =type (check* form)
                                      ;; :let [_ (prn '=type =type)]
                                      ;; state &util/get-state
                                      ;; :let [_ (prn '=type+state =type (class state) state)]
                                      ]
                                 (&util/with-field :types
                                   (&type/prettify nil =type))))
         ;; :let [_ (prn 'check/worlds worlds)]
         ]
    (&util/with-field :types
      (reduce-m &type/parallel &type/+nothing+ (map second (&util/results worlds))))))
