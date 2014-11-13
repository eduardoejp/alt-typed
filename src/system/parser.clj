(ns system.parser
  (:require [clojure.set :as set]
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [exec
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
    [(first ctor) (vec (rest ctor))]))

(defn ^:private parse-arity [parse-type-def type-def]
  (match type-def
    [& ?parts]
    (let [[args [_ return]] (split-with (partial not= '->) ?parts)]
      (exec [*args (map-m parse-type-def args)
             *return (parse-type-def return)]
        (&util/return [::&types/arity *args *return])))))

(defn test-effects [*effs]
  (exec [_ (if (not (empty? *effs))
             (return nil)
             zero)
         _ (if (set/superset? #{:try :io} (set (keys *effs)))
             (return nil)
             zero)
         _ (if-let [ex (:try *effs)]
             (&util/with-field :types
               (&types/solve [::&types/object 'java.lang.Exception []] ex))
             (return nil))
         _ (if-let [io (:io *effs)]
             (&util/with-field :types
               (&types/solve [::&types/io] io))
             (return nil))]
    (return nil)))

(defn parse-type-def [local-syms type-def]
  (match type-def
    nil
    (return [::&types/nil])

    (?value :guard (partial instance? java.lang.Boolean))
    (return [::&types/literal 'java.lang.Boolean ?value])

    (?value :guard (partial instance? clojure.lang.BigInt))
    (return [::&types/literal 'clojure.lang.BigInt ?value])

    (?value :guard (partial instance? java.math.BigDecimal))
    (return [::&types/literal 'java.math.BigDecimal ?value])

    (?value :guard integer?)
    (return [::&types/literal 'java.lang.Long ?value])

    (?value :guard float?)
    (return [::&types/literal 'java.lang.Double ?value])

    (?value :guard ratio?)
    (return [::&types/literal 'clojure.lang.Ratio ?value])
    
    (?value :guard (partial instance? java.lang.Character))
    (return [::&types/literal 'java.lang.Character ?value])

    (?value :guard string?)
    (return [::&types/literal 'java.lang.String ?value])

    (?value :guard (partial instance? java.util.regex.Pattern))
    (return [::&types/literal 'java.util.regex.Pattern ?value])

    (?value :guard keyword?)
    (return [::&types/literal 'clojure.lang.Keyword ?value])

    (['quote (?value :guard symbol?)] :seq)
    (return [::&types/literal 'clojure.lang.Symbol ?value])

    'Any
    (return [::&types/any])

    'Nothing
    (return [::&types/nothing])

    'IO
    (return [::&types/io])

    'Macro
    (return [::&types/macro])
    
    (['Or ?param & ?params] :seq)
    (exec [[*type & *types] (map-m (partial parse-type-def local-syms) (cons ?param ?params))]
      (&util/with-field :types
        (reduce-m &types/$or *type *types)))

    (['And ?param & ?params] :seq)
    (exec [[*type & *types] (map-m (partial parse-type-def local-syms) (cons ?param ?params))]
      (&util/with-field :types
        (reduce-m &types/$and *type *types)))
    
    (['Not ?inner] :seq)
    (exec [*inner (parse-type-def local-syms ?inner)]
      (return [::&types/complement *inner]))

    (['Eff ?data ?effs] :seq)
    (exec [*data (parse-type-def local-syms ?data)
           *effs (map-m
                  (fn [[k e]]
                    (exec [=e (parse-type-def local-syms e)]
                      (return [k =e])))
                  ?effs)
           :let [*effs (into {} *effs)]
           _ (test-effects *effs)]
      (return [::&types/eff *data *effs]))
    
    (?name :guard symbol?)
    (&util/try-all [;; (case (get local-syms ?name)
                    ;;   :var
                    ;;   (return ?name)

                    ;;   ;; :rec
                    ;;   ;; (return [::&types/rec ?name])

                    ;;   nil
                    ;;   zero)
                    (exec [state (&util/with-field :types
                                   &util/get-state)]
                      (&util/with-field :types
                        (&types/resolve ?name)))
                    (return ?name)])
    
    (['quote [& ?elems]] :seq)
    (exec [=elems (map-m (partial parse-type-def local-syms) ?elems)]
      (return [::&types/tuple (vec =elems)]))

    (['quote (?record :guard map?)] :seq)
    (exec [=kvs (map-m
                 (fn [[k v]]
                   (exec [=k (parse-type-def local-syms k)
                          =v (parse-type-def local-syms v)]
                     (return [=k =v])))
                 (seq ?record))]
      (return [::&types/record (into {} =kvs)]))

    [& ?arity]
    (exec [=arity (parse-arity (partial parse-type-def local-syms) ?arity)]
      (return [::&types/function (list =arity)]))
    
    (['Fn & ?arities] :seq)
    (exec [=arities (map-m (partial parse-arity (partial parse-type-def local-syms)) ?arities)]
      (return [::&types/function =arities]))

    (['All ?params ?def] :seq)
    (exec [*params (map-m #(match %
                             (?open :guard symbol?)
                             (return ?open)
                             
                             [?bounded '< ?top]
                             (exec [=top (parse-type-def local-syms ?top)]
                               (return [?bounded '< =top])))
                          ?params)
           *def (parse-type-def (into local-syms (for [p ?params]
                                                   (match p
                                                     (?open :guard symbol?)
                                                     [?open :var]
                                                     [?bounded '< ?top]
                                                     [?bounded :var])))
                                ?def)]
      (return [::&types/all {} *params *def]))

    ([?fn & ?params] :seq)
    (exec [=type-fn (parse-type-def local-syms ?fn)
           =params (map-m (partial parse-type-def local-syms) ?params)]
      (&types/apply =type-fn =params))
    ))

;; Functions
(defn parse [code]
  (match code
    nil
    (return [::#nil])
    
    (?value :guard (partial instance? java.lang.Boolean))
    (return [::#boolean ?value])

    (?value :guard (partial instance? clojure.lang.BigInt))
    (return [::#big-int ?value])

    (?value :guard (partial instance? java.math.BigDecimal))
    (return [::#big-decimal ?value])

    (?value :guard integer?)
    (return [::#integer ?value])

    (?value :guard float?)
    (return [::#real ?value])

    (?value :guard ratio?)
    (return [::#ratio ?value])
    
    (?value :guard (partial instance? java.lang.Character))
    (return [::#character ?value])

    (?value :guard string?)
    (return [::#string ?value])

    (?value :guard (partial instance? java.util.regex.Pattern))
    (return [::#regex ?value])

    (?value :guard keyword?)
    (return [::#keyword ?value])

    (?value :guard symbol?)
    (return [::symbol ?value])

    (?value :guard vector?)
    (exec [*value (map-m parse ?value)]
      (return [::#vector (vec *value)]))
    
    (?value :guard map?)
    (exec [*key (map-m parse (keys ?value))
           *value (map-m parse (vals ?value))]
      (return [::#map (into {} (map vector *key *value))]))
    
    (?value :guard set?)
    (exec [*value (map-m parse ?value)]
      (return [::#set (set *value)]))

    (['quote ?quoted] :seq)
    (cond (symbol? ?quoted)
          (return [::#symbol ?quoted])

          (atom? ?quoted)
          (parse ?quoted)

          (seq? ?quoted)
          (exec [*elems (map-m parse (map (fn [x] `(quote ~x)) ?quoted))]
            (return [::#list *elems]))
          
          (vector? ?quoted)
          (parse (mapv (fn [x] `(quote ~x)) ?quoted))

          (map? ?quoted)
          (parse (into {} (map (fn [[k v]] [`(quote ~k) `(quote ~v)]) ?quoted)))

          (set? ?quoted)
          (parse (seq (map (fn [x] `(quote ~x)) ?quoted))))
    
    (['do & ?forms] :seq)
    (return `[::do ~@?forms])

    (['let (?bindings :guard vector?) & ?body] :seq)
    (do (assert (even? (count ?bindings)) "LET must have an even number of elements.")
      (exec [*bindings (map-m
                        (fn [[?label ?value]]
                          (exec [*label (parse ?label)
                                 *value (parse ?value)]
                            (return [*label *value])))
                        (partition 2 ?bindings))
             *body (parse `(do ~@ ?body))]
        (return [::let *bindings *body])))

    (['if ?test ?then & &?else] :seq)
    (exec [*test (parse ?test)
           *then (parse ?then)
           *else (parse (first &?else))]
      (return [::if *test *then *else]))

    (['case ?value & ?clauses] :seq)
    (exec [*value (parse ?value)
           :let [[?clauses ?default] [(partition 2 ?clauses) (if (even? (count ?clauses))
                                                               nil
                                                               (last ?clauses))]]
           *clauses (map-m
                     (fn [[?value ?form]]
                       (exec [*value (if (seq? ?value)
                                       (map-m parse ?value)
                                       (parse ?value))
                              *form (parse ?form)]
                         (return [*value *form])))
                     ?clauses)
           *default (if ?default
                      (parse ?default)
                      (return nil))]
      (return [::case *value *clauses *default]))

    (['loop ?bindings & ?body] :seq)
    (exec [:let [locals (map (fn [pair]
                               (let [label (first pair)]
                                 [label label]))
                             (partition 2 ?bindings))]
           *bindings (map-m
                      (fn [[?label ?value]]
                        (exec [*label (parse ?label)
                               *value (parse ?value)]
                          (return [*label *value])))
                      (partition 2 ?bindings))
           *body (parse `(do ~@ ?body))]
      (return [::let *bindings [::loop locals *body]]))

    (['recur & ?args] :seq)
    (exec [*args (map-m parse ?args)]
      (return [::recur (vec *args)]))

    (['assert ?test & &?message] :seq)
    (exec [*test (parse ?test)
           *message (parse (first &?message))]
      (return [::assert *test *message]))
    
    (['def (?var :guard symbol?)] :seq)
    (return [::def ?var nil])
    
    (['def (?var :guard symbol?) ?value] :seq)
    (exec [*value (parse ?value)]
      (return [::def ?var *value]))

    (['var (?var :guard symbol?)] :seq)
    (return [::var ?var])

    (['throw ?ex] :seq)
    (exec [*ex (parse ?ex)]
      (return [::throw *ex]))

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
      (exec [*body (parse `(do ~@ ?body))
             *catches (map-m parse ?catches)
             *finally (exec [*finally (parse `(do ~@(rest ?finally)))]
                        (return *finally))]
        (return [::try *body (vec *catches) *finally])))

    (['catch (?class :guard symbol?) (?var :guard symbol?) & ?body] :seq)
    (exec [*body (parse `(do ~@ ?body))]
      (return [::catch ?class ?var *body]))

    (['monitor-enter ?object] :seq)
    (exec [*object (parse ?object)]
      (return [::monitor-enter *object]))

    (['monitor-exit ?object] :seq)
    (exec [*object (parse ?object)]
      (return [::monitor-exit *object]))

    (['binding ?bindings & ?body] :seq)
    (exec [*bindings (map-m
                      (fn [[label value]]
                        (exec [*label (parse label)
                               *value (parse value)]
                          (return [*label *value])))
                      (partition 2 ?bindings))
           *body (parse `(do ~@?body))]
      (return [::binding *bindings *body]))

    (['. ?obj ([(?method :guard symbol?) & ?args] :seq)] :seq)
    (exec [*obj (parse ?obj)
           *args (map-m parse ?args)]
      (return [::method-call ?method *obj *args]))

    (['. ?obj (?field :guard symbol?)] :seq)
    (exec [*obj (parse ?obj)]
      (return [::field-access ?field *obj]))

    (['new (?class :guard symbol?) & ?args] :seq)
    (exec [*args (map-m parse ?args)]
      (return [::new ?class (vec *args)]))
    
    (['ann (?var :guard symbol?) ?type-def] :seq)
    (exec [*type-def (parse-type-def {} ?type-def)]
      (return [::ann ?var *type-def]))

    (['ann-class (?class :guard type-ctor?)
      (?parents :guard (every-pred vector? (partial every? type-ctor?)))
      & ?fields+methods] :seq)
    (exec [:let [[_ params :as *type-ctor] (parse-type-ctor ?class)]
           *parents (map-m (partial parse-type-def (into {} (for [p params] [p :var]))) ?parents)]
      (return [::ann-class *type-ctor (vec *parents) ?fields+methods]))

    (['defalias (?ctor :guard type-ctor?) ?type-def] :seq)
    (let [[name args] (if (symbol? ?ctor)
                        [?ctor []]
                        [(first ?ctor) (vec (rest ?ctor))])]
      (exec [*type-def (if (empty? args)
                         (parse-type-def {name :rec} ?type-def)
                         (parse-type-def (into {name :rec} (for [p args] [p :var]))
                                         ?type-def))
             :let [*type-def (if (empty? args)
                               [::&types/alias name *type-def]
                               [::&types/all {} (vec args) [::&types/alias name *type-def]])]]
        (return [::defalias name *type-def])))

    (['fn ?local-name (?args :guard vector?) & ?body] :seq)
    (exec [*body (parse `(do ~@ ?body))]
      (return [::fn ?local-name ?args *body]))

    ([?fn & ?args] :seq)
    (exec [*fn (parse ?fn)
           *args (map-m parse ?args)]
      (return [::fn-call *fn *args]))
    ))
