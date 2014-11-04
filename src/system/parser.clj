(ns system.parser
  (:require [clojure.set :as set]
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]]
                    [type :as &types])))

;; [Utils]
(def ^:private atom?
  (some-fn (partial instance? java.lang.Boolean)
           (partial instance? clojure.lang.BigInt)
           (partial instance? java.math.BigDecimal)
           integer?
           float?
           ratio?
           string?
           (partial instance? java.util.regex.Pattern)
           keyword?
           nil?))

(defn ^:private type-ctor? [x]
  (or (symbol? x)
      (and (seq? x)
           (>= (count x) 2))))

(defn ^:private parse-type-ctor [ctor]
  (if (symbol? ctor)
    [ctor []]
    [(first ctor) (mapv parse-type-ctor (rest ctor))]))

(defn ^:private parse-arity [parse-type-def type-def]
  ;; (prn 'parse-arity type-def)
  (match type-def
    [& ?parts]
    (let [[args [_ return]] (split-with (partial not= '->) ?parts)]
      (exec state-seq-m
        [;; :let [_ (prn '[args return] [args return])]
         *args (map-m state-seq-m parse-type-def args)
         ;; :let [_ (prn '*args *args)]
         *return (parse-type-def return)
         ;; :let [_ (prn '*return *return)]
         ]
        (&util/return state-seq-m [::&types/arity *args *return])))))

(defn test-effects [*effs]
  (exec state-seq-m
    [_ (if (not (empty? *effs))
         (return state-seq-m nil)
         zero)
     _ (if (set/superset? #{:try :io} (set (keys *effs)))
         (return state-seq-m nil)
         zero)
     _ (if-let [ex (:try *effs)]
         (&util/with-field* :types
           (&types/solve [::&types/object 'java.lang.Exception []] ex))
         (return state-seq-m nil))
     _ (if-let [io (:io *effs)]
         (&util/with-field* :types
           (&types/solve [::&types/io] io))
         (return state-seq-m nil))]
    (return state-seq-m nil)))

(defn ^:private parse-type-def [type-def]
  ;; (prn 'parse-type-def type-def)
  (match type-def
    nil
    (return state-seq-m [::&types/nil])

    (?value :guard (partial instance? java.lang.Boolean))
    (return state-seq-m [::&types/literal 'java.lang.Boolean ?value])

    (?value :guard (partial instance? clojure.lang.BigInt))
    (return state-seq-m [::&types/literal 'clojure.lang.BigInt ?value])

    (?value :guard (partial instance? java.math.BigDecimal))
    (return state-seq-m [::&types/literal 'java.math.BigDecimal ?value])

    (?value :guard integer?)
    (return state-seq-m [::&types/literal 'java.lang.Long ?value])

    (?value :guard float?)
    (return state-seq-m [::&types/literal 'java.lang.Double ?value])

    (?value :guard ratio?)
    (return state-seq-m [::&types/literal 'clojure.lang.Ratio ?value])
    
    (?value :guard (partial instance? java.lang.Character))
    (return state-seq-m [::&types/literal 'java.lang.Character ?value])

    (?value :guard string?)
    (return state-seq-m [::&types/literal 'java.lang.String ?value])

    (?value :guard (partial instance? java.util.regex.Pattern))
    (return state-seq-m [::&types/literal 'java.util.regex.Pattern ?value])

    (?value :guard keyword?)
    (return state-seq-m [::&types/literal 'clojure.lang.Keyword ?value])

    'IO
    (return state-seq-m [::&types/io])

    'Macro
    (return state-seq-m [::&types/macro])
    
    (['Or & ?params] :seq)
    (exec state-seq-m
      [*types (map-m state-seq-m parse-type-def ?params)]
      (return state-seq-m [::&types/union (vec *types)]))

    (['Not ?inner] :seq)
    (exec state-seq-m
      [*inner (parse-type-def ?inner)]
      (return state-seq-m [::&types/complement *inner]))

    (['Eff ?data ?effs] :seq)
    (exec state-seq-m
      [*data (parse-type-def ?data)
       *effs (map-m state-seq-m
                    (fn [[k e]]
                      (exec state-seq-m
                        [=e (parse-type-def e)]
                        (return state-seq-m [k =e])))
                    ?effs)
       :let [*effs (into {} *effs)]
       _ (test-effects *effs)]
      (return state-seq-m [::&types/eff *data *effs]))
    
    (?name :guard symbol?)
    (do ;; (prn '(?name :guard symbol?) `(~?name :guard ~'symbol?))
        (&util/with-field* :types
          (&types/resolve ?name)))
    
    [& ?parts]
    (do ;; (prn '[& ?parts])
        (exec state-seq-m
          [=arity (parse-arity parse-type-def type-def)
           ;; :let [_ (prn '=arity =arity)]
           ]
          (return state-seq-m [::&types/function (list =arity)])))

    (['Fn & ?arities] :seq)
    (exec state-seq-m
      [=arities (map-m state-seq-m (partial parse-arity parse-type-def) ?arities)]
      (return state-seq-m [::&types/function (vec =arities)]))

    ([?fn & ?params] :seq)
    (do ;; (prn '[?fn & ?params] [?fn ?params])
        (exec state-seq-m
          [=type-fn (do (prn '?fn ?fn)
                      (&util/with-field* :types
                        (&types/resolve ?fn)))
           ;; :let [_ (prn '=type-fn =type-fn)]
           =params (map-m state-seq-m parse-type-def ?params)
           ;; :let [_ (prn '=params =params)]
           ]
          (&types/fn-call =type-fn =params)))
    
    ;; :else
    ;; (do (prn 'parse-type-def/else)
    ;;   zero)
    ))

;; Functions
(defn parse [code]
  ;; (prn 'parse code)
  (match code
    nil
    (return state-seq-m [::#nil])
    
    (?value :guard (partial instance? java.lang.Boolean))
    (return state-seq-m [::#boolean ?value])

    (?value :guard (partial instance? clojure.lang.BigInt))
    (return state-seq-m [::#big-int ?value])

    (?value :guard (partial instance? java.math.BigDecimal))
    (return state-seq-m [::#big-decimal ?value])

    (?value :guard integer?)
    (return state-seq-m [::#integer ?value])

    (?value :guard float?)
    (return state-seq-m [::#real ?value])

    (?value :guard ratio?)
    (return state-seq-m [::#ratio ?value])
    
    (?value :guard (partial instance? java.lang.Character))
    (return state-seq-m [::#character ?value])

    (?value :guard string?)
    (return state-seq-m [::#string ?value])

    (?value :guard (partial instance? java.util.regex.Pattern))
    (return state-seq-m [::#regex ?value])

    (?value :guard keyword?)
    (return state-seq-m [::#keyword ?value])

    (?value :guard symbol?)
    (return state-seq-m [::symbol ?value])

    (?value :guard vector?)
    (exec state-seq-m
      [*value (map-m state-seq-m parse ?value)]
      (return state-seq-m [::#vector (vec *value)]))
    
    (?value :guard map?)
    (exec state-seq-m
      [*key (map-m state-seq-m parse (keys ?value))
       *value (map-m state-seq-m parse (vals ?value))]
      (return state-seq-m [::#map (into {} (map vector *key *value))]))
    
    (?value :guard set?)
    (exec state-seq-m
      [*value (map-m state-seq-m parse ?value)]
      (return state-seq-m [::#set (set *value)]))

    (['quote ?quoted] :seq)
    (do (prn '?quoted ?quoted (seq? ?quoted) (atom? ?quoted))
      (cond (symbol? ?quoted)
            (return state-seq-m [::#symbol ?quoted])

            (atom? ?quoted)
            (parse ?quoted)

            (seq? ?quoted)
            (exec state-seq-m
              [*elems (map-m state-seq-m parse (map (fn [x] `(quote ~x)) ?quoted))]
              (return state-seq-m [::#list *elems]))
            
            (vector? ?quoted)
            (parse (mapv (fn [x] `(quote ~x)) ?quoted))

            (map? ?quoted)
            (parse (into {} (map (fn [[k v]] [`(quote ~k) `(quote ~v)]) ?quoted)))

            (set? ?quoted)
            (parse (seq (map (fn [x] `(quote ~x)) ?quoted)))))
    
    (['do & ?forms] :seq)
    (exec state-seq-m
      [*forms (map-m state-seq-m parse ?forms)]
      (return state-seq-m `[::do ~@*forms]))

    (['let (?bindings :guard vector?) & ?body] :seq)
    (do (assert (even? (count ?bindings)) "LET must have an even number of elements.")
      (exec state-seq-m
        [*bindings (map-m state-seq-m
                          (fn [[?label ?value]]
                            (exec state-seq-m
                              [*value (parse ?value)]
                              (return state-seq-m [?label *value])))
                          (partition 2 ?bindings))
         *body (map-m state-seq-m parse ?body)]
        (return state-seq-m [::let *bindings `[::do ~@*body]])))

    (['if ?test ?then & &?else] :seq)
    (exec state-seq-m
      [*test (parse ?test)
       *then (parse ?then)
       *else (parse (first &?else))]
      (return state-seq-m [::if *test *then *else]))

    (['case ?value & ?clauses] :seq)
    (exec state-seq-m
      [*value (parse ?value)
       :let [[?clauses ?default] [(partition 2 ?clauses) (if (even? (count ?clauses))
                                                           nil
                                                           (last ?clauses))]
             _ (prn '[?clauses ?default] [?clauses ?default])]
       *clauses (map-m state-seq-m
                       (fn [[?value ?form]]
                         (exec state-seq-m
                           [*value (if (seq? ?value)
                                     (map-m state-seq-m parse ?value)
                                     (parse ?value))
                            *form (parse ?form)]
                           (return state-seq-m [*value *form])))
                       ?clauses)
       *default (if ?default
                  (parse ?default)
                  (return state-seq-m nil))]
      (return state-seq-m [::case *value *clauses *default]))

    (['loop ?bindings & ?body] :seq)
    (exec state-seq-m
      [:let [locals (map (fn [pair]
                           (let [label (first pair)]
                             [label label]))
                         (partition 2 ?bindings))]
       *bindings (map-m state-seq-m
                        (fn [[?label ?value]]
                          (exec state-seq-m
                            [*value (parse ?value)]
                            (return state-seq-m [?label *value])))
                        (partition 2 ?bindings))
       *body (map-m state-seq-m parse ?body)]
      (return state-seq-m [::let *bindings [::loop locals `[::do ~@*body]]]))

    (['recur & ?args] :seq)
    (exec state-seq-m
      [*args (map-m state-seq-m parse ?args)]
      (return state-seq-m [::recur (vec *args)]))

    (['assert ?test & &?message] :seq)
    (exec state-seq-m
      [*test (parse ?test)
       *message (parse (first &?message))]
      (return state-seq-m [::assert *test *message]))
    
    (['def (?var :guard symbol?)] :seq)
    (return state-seq-m [::def ?var nil])
    
    (['def (?var :guard symbol?) ?value] :seq)
    (exec state-seq-m
      [*value (parse ?value)]
      (return state-seq-m [::def ?var *value]))

    (['var (?var :guard symbol?)] :seq)
    (return state-seq-m [::var ?var])

    (['throw ?ex] :seq)
    (exec state-seq-m
      [*ex (parse ?ex)]
      (return state-seq-m [::throw *ex]))

    (['try & ?sub-exprs] :seq)
    (let [[?body ?sub-exprs] (split-with (fn [expr]
                                           (not (and (seq? expr)
                                                     (or (-> expr first (= 'catch))
                                                         (-> expr first (= 'finally))))))
                                         ?sub-exprs)
          [?catches [?finally]] (split-with (fn [expr]
                                              (not (and (seq? expr)
                                                        (-> expr first (= 'finally)))))
                                            ?sub-exprs)]
      (exec state-seq-m
        [*body (map-m state-seq-m parse ?body)
         *catches (map-m state-seq-m parse ?catches)
         *finally (exec state-seq-m
                    [*finally (map-m state-seq-m parse (rest ?finally))]
                    (return state-seq-m `[::do ~@*finally]))]
        (return state-seq-m [::try `[::do ~@*body] (vec *catches) *finally])))

    (['catch (?class :guard symbol?) (?var :guard symbol?) & ?body] :seq)
    (exec state-seq-m
      [*body (map-m state-seq-m parse ?body)]
      (return state-seq-m [::catch ?class ?var `[::do ~@*body]]))

    (['monitor-enter ?object] :seq)
    (exec state-seq-m
      [*object (parse ?object)]
      (return state-seq-m [::monitor-enter *object]))

    (['monitor-exit ?object] :seq)
    (exec state-seq-m
      [*object (parse ?object)]
      (return state-seq-m [::monitor-exit *object]))

    (['binding ?bindings & ?body] :seq)
    (exec state-seq-m
      [*bindings (map-m state-seq-m
                        (fn [[label value]]
                          (exec state-seq-m
                            [*label (parse label)
                             *value (parse value)]
                            (return state-seq-m [*label *value])))
                        (partition 2 ?bindings))
       *body (map-m state-seq-m parse ?body)]
      (return state-seq-m [::binding *bindings `[::do ~@*body]]))
    
    (['ann (?var :guard symbol?) ?type-def] :seq)
    (do ;; (prn `[~'ann ~?var ~?type-def])
        (exec state-seq-m
          [*type-def (parse-type-def ?type-def)
           ;; :let [_ (prn '*type-def *type-def)]
           ]
          (return state-seq-m [::ann ?var *type-def])))

    (['ann-class (?class :guard type-ctor?) (?parents :guard (every-pred vector? (partial every? type-ctor?)))] :seq)
    (exec state-seq-m
      [:let [*type-ctor (parse-type-ctor ?class)
             ;; _ (prn '*type-ctor *type-ctor)
             *parents (map parse-type-ctor ?parents)
             ;; _ (prn '*parents *parents)
             ]]
      (return state-seq-m [::ann-class *type-ctor (vec *parents)]))

    (['defalias (?ctor :guard type-ctor?) ?type-def] :seq)
    (let [[name args] (if (symbol? ?ctor)
                        [?ctor []]
                        [(first ?ctor) (rest ?ctor)])]
      (return state-seq-m [::defalias name args (parse-type-def ?type-def)]))

    (['fn ?local-name (?args :guard vector?) & ?body] :seq)
    (exec state-seq-m
      [*body (map-m state-seq-m parse ?body)]
      (return state-seq-m [::fn ?local-name ?args `[::do ~@*body]]))

    ([?fn & ?args] :seq)
    (exec state-seq-m
      [*fn (parse ?fn)
       *args (map-m state-seq-m parse ?args)]
      (return state-seq-m [::fn-call *fn *args]))
    ))
