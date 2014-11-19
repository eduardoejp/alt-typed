(ns system.parser
  (:require [clojure.set :as set]
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [exec
                                            zero return return-all fail
                                            map-m reduce-m]]
                    [type :as &types])))

;; [Utils]
(def ^:private atom?
  (some-fn (partial instance? java.lang.Boolean)
           (partial instance? clojure.lang.BigInt)
           (partial instance? java.math.BigDecimal)
           integer?
           float?
           ratio?
           (partial instance? java.lang.Character)
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

(defn test-effects [*effs]
  (exec [_ (&util/assert! (not (empty? *effs)) "The effects can't be empty!")
         _ (&util/assert! (set/superset? #{:try :io} (set (keys *effs))) "Effects can only be either :try or :io")
         _ (if-let [ex (:try *effs)]
             (&util/with-field :types
               (&types/solve [::&types/object 'java.lang.Exception []] ex))
             (return nil))
         _ (if-let [io (:io *effs)]
             (&util/with-field :types
               (&types/solve [::&types/io] io))
             (return nil))]
    (return nil)))

(defn ^:private parse-poly-args [parse-type-def local-syms args]
  (map-m #(match %
            (?open :guard symbol?)
            (return [?open [::&types/any]])
            
            [?bounded '< ?top]
            (exec [=top (parse-type-def local-syms ?top)]
              (return [?bounded =top])))
         args))

(defn parse-type-def [local-syms type-def]
  ;; (prn 'parse-type-def local-syms type-def)
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

    'boolean
    (&types/$primitive :boolean)

    'byte
    (&types/$primitive :byte)

    'short
    (&types/$primitive :short)

    'int
    (&types/$primitive :int)

    'long
    (&types/$primitive :long)

    'float
    (&types/$primitive :float)

    'double
    (&types/$primitive :double)

    'char
    (&types/$primitive :char)

    'Any
    (return [::&types/any])

    'Nothing
    (return [::&types/nothing])

    'IO
    (return [::&types/io])

    'Macro
    (return [::&types/macro])

    (['Array ?type] :seq)
    (exec [*type (parse-type-def local-syms ?type)]
      (&types/$array *type))
    
    (['Or ?param & ?params] :seq)
    (exec [[*type & *types] (map-m (partial parse-type-def local-syms) (cons ?param ?params))]
      (&util/with-field :types
        (reduce-m &types/$or *type *types)))

    (['Xor ?param & ?params] :seq)
    (exec [[*type & *types] (map-m (partial parse-type-def local-syms) (cons ?param ?params))]
      (&util/with-field :types
        (reduce-m &types/$xor *type *types)))

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
    (do ;; (prn '(get local-syms ?name) ?name (get local-syms ?name) local-syms)
        (case (get local-syms ?name)
          (:var :rec)
          (return ?name)

          nil
          (&util/with-field :types
            (&types/resolve ?name))))
    
    (['quote [& ?elems]] :seq)
    (exec [=elems (map-m (partial parse-type-def local-syms) ?elems)]
      (return [::&types/tuple (vec =elems)]))

    (['quote (?record :guard map?)] :seq)
    (exec [=kvs (map-m (fn [[k v]]
                         (exec [=k (parse-type-def local-syms k)
                                =v (parse-type-def local-syms v)]
                           (return [=k =v])))
                       (seq ?record))]
      (return [::&types/record (into {} =kvs)]))

    [& ?arity]
    (match ?arity
      [& ?parts]
      (let [[args [_ return]] (split-with (partial not= '->) ?parts)]
        (exec [*args (map-m (partial parse-type-def local-syms) args)
               *return (parse-type-def local-syms return)]
          (&util/return [::&types/arity *args *return]))))
    
    (['Fn & ?arities] :seq)
    (exec [=arities (map-m (partial parse-type-def local-syms) ?arities)]
      (return [::&types/function =arities]))

    (['All ?params ?def] :seq)
    (exec [*params (parse-poly-args parse-type-def local-syms ?params)
           *def (parse-type-def (into local-syms (for [p ?params]
                                                   (match p
                                                     (?open :guard symbol?)
                                                     [?open :var]
                                                     [?bounded '< ?top]
                                                     [?bounded :var])))
                                ?def)]
      (return [::&types/all {} *params *def]))

    (['Rec (?local-name :guard vector?) ?def] :seq)
    (if (and (= 1 (count ?local-name))
             (symbol? (first ?local-name)))
      (let [[?local-name] ?local-name
            ;; _ (prn '?local-name ?local-name)
            ]
        (exec [=def (parse-type-def (assoc local-syms ?local-name :rec) ?def)
               ;; :let [_ (prn '=def =def)]
               ]
          (return [::&types/rec ?local-name =def])))
      (fail "Recursive types must have an args-vector containing only 1 symbol!"))
    
    ([?fn & ?params] :seq)
    (exec [=params (map-m (partial parse-type-def local-syms) ?params)
           ;; :let [_ (prn '?fn ?fn '?params ?params =params)]
           ]
      (if (= :rec (get local-syms ?fn))
        (return [::&types/rec-call ?fn {} =params])
        (exec [=type-fn (parse-type-def local-syms ?fn)
               ;; :let [_ (prn '=type-fn =type-fn)]
               ]
          (&types/apply =type-fn =params))))
    ))

(defn ^:private parse-method [code]
  ;; (prn 'parse-method code)
  (match code
    ([(?name :guard symbol?) & arities+doc] :seq)
    (let [arities (if (string? (last arities+doc))
                    (butlast arities+doc)
                    arities+doc)]
      (assert (= 1 (count arities)))
      (return [::pmethod ?name arities]))
    
    :else
    (fail "Correct method syntax is (name args-list+ doc-string?) -- example: (foo [bar baz] [bar baz quux] \"Just an example\")")))

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

    (['set! ?target ?value] :seq)
    (exec [*target (parse ?target)
           *value (parse ?value)]
      (return [::set! *target *value]))

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

    (['defmulti (?name :guard symbol?) ?dispatch-fn] :seq)
    (exec [*dispatch-fn (parse ?dispatch-fn)]
      (return [::defmulti ?name *dispatch-fn]))

    (['defmethod (?name :guard symbol?) ?dispatch-val ?args & ?body] :seq)
    (exec [*dispatch-val (parse ?dispatch-val)
           *args (map-m parse ?args)
           *body (parse `(do ~@ ?body))]
      (return [::defmethod ?name *dispatch-val ?args *body]))

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
           *params (parse-poly-args parse-type-def {} params)
           :let [*locals (into {} (for [p params]
                                    (match p
                                      (?open :guard symbol?)
                                      [?open :var]
                                      [?bounded '< ?top]
                                      [?bounded :var])))]
           *parents (map-m (partial parse-type-def *locals) ?parents)]
      (return [::ann-class (conj *type-ctor *params) (vec *parents) ?fields+methods]))

    (['defalias (?ctor :guard type-ctor?) ?type-def] :seq)
    (let [[name args] (if (symbol? ?ctor)
                        [?ctor []]
                        [(first ?ctor) (vec (rest ?ctor))])]
      (exec [*type-def (if (empty? args)
                         (parse-type-def {} ?type-def)
                         (parse-type-def (into {} (for [p args] [p :var]))
                                         ?type-def))
             :let [*type-def (if (empty? args)
                               [::&types/alias name *type-def]
                               [::&types/all {} (vec args) [::&types/alias name *type-def]])]]
        (return [::defalias name *type-def])))

    (['fn (?local-name :guard symbol?) (?args :guard vector?) & ?body] :seq)
    (exec [*body (parse `(do ~@ ?body))]
      (return [::fn ?local-name ?args *body]))

    (['fn (?args :guard vector?) & ?body] :seq)
    (exec [*body (parse `(do ~@ ?body))]
      (return [::fn nil ?args *body]))

    (['defprotocol ?name & ?extra] :seq)
    (let [[_ methods] (if (string? (first ?extra))
                        [(first ?extra) (rest ?extra)]
                        [nil ?extra])]
      (exec [*methods (map-m parse-method ?extra)]
        (return [::protocol ?name *methods])))

    (['deftype ?name (?args :guard vector?) & ?impls] :seq)
    (let [*impls (reduce (fn [[context impls] token]
                           ;; (prn 'token token (class token))
                           (if (symbol? token)
                             [token impls]
                             (let [[?name ?args & ?forms] token]
                               [context (update-in impls [context ?name] conj [?args ?forms])])))
                         [nil {}]
                         ?impls)]
      (return [::deftype ?name ?args (nth *impls 1)]))

    (['defrecord ?name (?args :guard vector?) & ?impls] :seq)
    (let [*impls (reduce (fn [[context impls] token]
                           ;; (prn 'token token (class token))
                           (if (symbol? token)
                             [token impls]
                             (let [[?name ?args & ?forms] token]
                               [context (update-in impls [context ?name] conj [?args ?forms])])))
                         [nil {}]
                         ?impls)]
      (return [::defrecord ?name ?args (nth *impls 1)]))

    (['reify & ?impls] :seq)
    (let [*impls (reduce (fn [[context impls] token]
                           ;; (prn 'token token (class token))
                           (if (symbol? token)
                             [token impls]
                             (let [[?name ?args & ?forms] token]
                               [context (update-in impls [context ?name] conj [?args ?forms])])))
                         [nil {}]
                         ?impls)]
      (return [::reify (nth *impls 1)]))

    (['extend ?class & ?impls] :seq)
    (let [*class (parse ?class)
          *impls (reduce (fn [impls [context methods]]
                           (reduce (fn [impls [name fn-code]]
                                     (assoc-in impls [context (-> name clojure.core/name symbol)] fn-code))
                                   impls
                                   methods))
                         {}
                         (apply hash-map ?impls))]
      (return [::extend ?class *impls]))

    ([?fn & ?args] :seq)
    (exec [*fn (parse ?fn)
           *args (map-m parse ?args)]
      (return [::fn-call *fn *args]))
    ))
