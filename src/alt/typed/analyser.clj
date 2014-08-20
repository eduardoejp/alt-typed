(ns alt.typed.analyser
  (:require (alt.typed [util :as &util]
                       [context :as &context]
                       [type :as &type]
                       [ann :as &ann]
                       [translator :as &translator]
                       [solver :as &solver])
            (alt.typed.context [ns :as &ns]
                               [library :as &library]
                               [graph :as &graph])
            (alt.typed.syntax [parser :as &parser]
                              [interpreter :as &interpreter]))
  (:import (alt.typed.type LiteralType
                           TupleType
                           ArityType
                           FnType
                           AliasType
                           TypeVar)))

(declare analyse)

;; [Utils]
(defn ^:private lib-spec? [form]
  (and (sequential? form)
       (odd? (count form))
       (keyword? (nth form 1))))

(defn ^:private normalize-lib-spec [x]
  (cond (lib-spec? x)
        [x]

        (symbol? x)
        [(list x)]

        (sequential? x)
        (let [[prefix & specs] x
              add-prefix #(->> % name (symbol (name prefix)))]
          (map #(update-in % [0] add-prefix) specs))

        (keyword? x)
        []

        :else
        (throw (ex-info "Invalid format for libspec." {:form x}))))

(defn ^:private normalize-import [x]
  (cond (symbol? x)
        (list (name x))
        
        (sequential? x)
        (let [[package & classes] x]
          (map #(str (name package) "." (name %)) classes))

        :else
        (throw (ex-info "Invalid format for import." {:form x}))))

(defn ^:private parse-refer [[ns & {:keys [only exclude rename]}]]
  {:ns      ns
   :alias   nil
   :only    (if only (set only))
   :exclude (if exclude (set exclude) #{})
   :rename  (if rename
              (into {} (for [[k v] rename] [(name v) (name k)]))
              {})
   })

(defn ^:private parse-require [[ns & {:keys [as refer]}]]
  {:ns      ns
   :alias   as
   :only    (if (= :all refer) nil (set refer))
   :exclude #{}
   :rename  {}
   })

(defn ^:private normalize-fn [[_ ?name & fn-def :as form]]
  (let [[?name fn-def] (if (symbol? ?name)
                         [?name fn-def]
                         [nil (cons ?name fn-def)])
        arities (if (vector? (first fn-def))
                  (list fn-def)
                  fn-def)]
    {:fn-name ?name
     :arities arities}))

(defn ^:private analyse-all [context [e & exprs]]
  (for [[context $e] (analyse context e)
        [context $es] (if (empty? exprs)
                        (list [context '()])
                        (analyse-all context exprs))]
    [context (cons $e $es)]))

(defn ^:private add-tuple [context tuple]
  {:pre [(and (vector? tuple)
              (not (empty? tuple))
              (every? symbol? tuple)
              (every? (partial not= '&) tuple))]}
  (let [tuple-length (count tuple)
        [context $members] (reduce (fn [[c $vs] v]
                                     (let [[c $v] (&graph/add-var c v &type/Any)]
                                       [c (conj $vs $v)]))
                                   [context []]
                                   tuple)
        =members (mapv (partial &graph/get-var context) $members)
        [context $tuple] (&graph/add-var context (gensym "tuple_") (TupleType. =members))
        frame (into (hash-map) (map vector tuple $members))]
    [context frame $tuple]))

(defn ^:private init-frame [context args]
  (reduce (fn [[context frame $args] arg]
            (cond (symbol? arg)
                  (let [[context $arg] (&graph/add-var context arg &type/Any)]
                    [context (assoc frame arg $arg) (conj $args $arg)])

                  (vector? arg)
                  (let [[context tuple-frame $tuple] (add-tuple context arg)]
                    [context (merge frame tuple-frame) (conj $args $tuple)])

                  :else
                  (throw (ex-info "Unrecognized arg form." {:form arg, :args args}))))
          [context {} []]
          args))

(defn ^:private analyse-arity [context =fn [frame & body :as form]]
  (prn 'analyse ::arity (keys frame) body)
  ;; (prn 'analyse ::arity %args 'PRE
  ;;      (get-in context [:_graph :_local])
  ;;      (get-in context [:_graph :_global]))
  (let [[invariants-map body] (if (map? (first body))
                                [(first body) (rest body)]
                                [nil body])]
    (assert (nil? invariants-map) "Can't handle invariants ({:pre ... :post ...}) yet!")
    (let [;; [context =args frame] (init-args context %args)
          context (&graph/push context frame)
          ;; _ (prn 'analyse ::arity %args 'POST
          ;;        (get-in context [:_graph :_local])
          ;;        (get-in context [:_graph :_global]))
          ]
      (for [[context $body] (analyse context `(do ~@body))
            :let [context (&graph/pop context)]]
        [context $body]))))

(defn ^:private analyse-arities [context =fn [arity & arities]]
  (for [[context =arity] (analyse-arity context =fn arity)
        [context =arities] (if (empty?  arities)
                             (list [context '()])
                             (analyse-arities context =fn arities))]
    [context (cons =arity =arities)]))

(defn ^:private analyse-let [context [[left right] & bindings] do-body]
  (for [[context $right] (analyse context right)
        :let [context (&graph/push context {left $right})]
        [context $remaining] (if (empty? bindings)
                               (analyse context do-body)
                               (analyse-let context bindings do-body))
        :let [_ (prn 'analyse-let/context (empty? bindings) do-body)
              context (&graph/pop context)]]
    [context $remaining]))

(defn ^:private fn-call [context ^FnType =fn =args]
  (let [num-args (count =args)
        all-arities (.-arities =fn)
        applicable-arities (filter #(= num-args (count (.-normal-args ^ArityType %))) all-arities)]
    (seq (for [^ArityType =arity applicable-arities
               :let [context (&solver/solve-all context (.-normal-args =arity) =args)]
               :when context
               :let [=return (.-return =arity)]]
           (do (println "POST-solving:" (&translator/translate =arity context))
             (println "POST-solving [return]:" (&translator/translate =return context))
             [context =return])))))

(defn ^:private min-fn-type [context =args]
  (let [[context =return] (&graph/add-var context (gensym "return_") &type/Any)
        =arity (&type/arity-type (vec =args) =return)]
    [context (&type/fn-type [=arity])]))

;; [Functions]
;; (ann analyse-dispatcher [Any -> Keyword])
(defn ^:private analyse-dispatcher [context form]
  (cond (nil? form)
        ::nil

        (symbol? form)
        ::symbol

        (&util/atom? form)
        ::value

        (vector? form)
        ::vector

        (map? form)
        ::map

        (set? form)
        ::set

        (and (list? form)
             (empty? form))
        ::empty-list

        (seq? form)
        (first form)
        
        :else
        (throw (ex-info "Unknown form" {:form form}))))

(defmulti analyse analyse-dispatcher :default ::default)

(defmethod analyse ::nil [context _]
  (list [context &type/Nil]))

(defmethod analyse ::value [context val]
  (prn 'analyse ::value val)
  (list [context (LiteralType. val)]))

(defmethod analyse ::symbol [context form]
  (prn 'analyse ::symbol form)
  (if-let [$form (or (&graph/find context form)
                     (if-let [resolved (&ns/resolve context form)]
                       (&graph/find context resolved)))]
    (if (&graph/id? $form)
      (do (prn 'analyse ::symbol '$form (&translator/translate (&graph/get-type context $form) context))
        (list [context $form]))
      (let [[context $form] (if (&type/type-fn? $form)
                              (let [[context =form] (&graph/instance context $form)]
                                (&graph/add-type context =form))
                              (&graph/add-type context $form))]
        (prn 'analyse ::symbol '$form (&translator/translate (&graph/get-type context $form) context))
        (list [context $form])))
    (throw (ex-info "Unrecognized symbol." {:symbol form}))))

(defmethod analyse 'def [context [_ var-name & extra :as form]]
  (assert (<= (count extra) 1))
  (prn 'analyse 'def form)
  (let [context* (if (empty? extra)
                   context
                   (analyse context (first extra)))]
    (prn 'def/context* context*)
    context*)
  (assert false))

(defmethod analyse 'do [context [_ & exprs :as form]]
  (prn 'analyse 'do form)
  (let [outcomes (case (count exprs)
                   0
                   (list [context &type/Nil])
                   
                   1
                   (analyse context (first exprs))

                   ;; Else
                   (for [[context $exprs] (analyse-all context exprs)]
                     [context (last $exprs)]))]
    (prn 'analyse/do (count exprs) (count outcomes) (mapv class outcomes) form)
    outcomes))

(defmethod analyse 'if [context [_ %test %then %else :as form]]
  (prn 'analyse 'if form)
  (let [branches (doall (for [[context $test] (let [universes (analyse context %test)]
                                                (when (> (count universes) 1)
                                                  (prn 'if/universe (count universes)))
                                                universes)
                              :let [_ (prn 'if/test (&translator/translate $test context))]
                              [context $branch] (concat (if-let [[then-context $test] (&solver/narrow context $test (&library/lookup context 'alt.typed/Truthy))]
                                                          (do (println "THEN:" (&translator/translate $test context))
                                                            (let [then-context (if (and (symbol? %test) (nil? (namespace %test)))
                                                                                 (&graph/push then-context {%test $test})
                                                                                 then-context)]
                                                              (analyse then-context %then))))
                                                        (if-let [[else-context $test] (&solver/narrow context $test (&library/lookup context 'alt.typed/Falsey))]
                                                          (do (println "ELSE:" (&translator/translate $test context))
                                                            (let [else-context (if (and (symbol? %test) (nil? (namespace %test)))
                                                                                 (&graph/push else-context {%test $test})
                                                                                 else-context)]
                                                              (analyse else-context %else)))))]
                          [context $branch]))]
    (prn 'analyse/if (count branches) (mapv class branches) form)
    branches))

(defmethod analyse 'clojure.core/let [context [_ bindings & body :as form]]
  (prn 'analyse 'clojure.core/let form)
  (assert (even? (count bindings)) "Let must have an even number of bindings.")
  (analyse-let context (partition 2 bindings) `(do ~@body)))

(defmethod analyse 'clojure.core/fn [context form]
  (prn 'analyse 'clojure.core/fn form)
  (let [{:keys [fn-name arities]} (normalize-fn form)
        [context packs] (reduce (fn [[context packs] arity]
                                  (let [[context frame $args] (init-frame context (first arity))]
                                    [context (conj packs [frame $args])]))
                                [context []]
                                arities)
        [context =arities] (reduce (fn [[context =arities] [_ $args]]
                                     (let [[context $var] (&graph/add-var context (gensym "return_") &type/Any)]
                                       [context (conj =arities (&type/arity-type (mapv (partial &graph/get-type context) $args)
                                                                                 (&graph/get-type context $var)))]))
                                   [context []]
                                   packs)
        =fn (&type/fn-type =arities)
        context (if fn-name
                  (let [context (&graph/push context {fn-name =fn})]
                    (prn "Function has a name:" fn-name)
                    (prn (&graph/find context fn-name))
                    context)
                  context)
        arities (for [[[frame] [_ & body]] (map vector packs arities)]
                  (conj body frame))
        universes (doall (for [[context =return] (analyse-arities context =fn arities)
                               :let [context (if fn-name (&graph/pop context) context)]]
                           [context =return]))]
    (prn 'analyse/fn (count universes))
    (assert false)))

(defmethod analyse 'clojure.core/defn [context [_ fn-name & body :as form]]
  (prn 'analyse 'clojure.core/defn form)
  (analyse context `(def ~fn-name (fn ~fn-name ~@body))))

(let [prefix-adder (fn [prefix]
                     #(->> % name (symbol (name prefix))))
      referrer (fn [ctx {:keys [ns alias only exclude rename]}]
                 (&ns/refer ctx ns alias only exclude rename))
      importer (fn [ctx class-name]
                 (&ns/import ctx class-name))]
  (defmethod analyse 'clojure.core/ns [context [_ ns-name & references :as form]]
    (assert (and (symbol? ns-name)
                 (nil? (namespace ns-name))))
    (prn 'analyse 'clojure.core/ns ns-name form)
    (let [[doc-string references] (if (string? (first references))
                                    [(first references) (rest references)]
                                    [nil references])
          [metadata references] (if (map? (first references))
                                  [(first references) (rest references)]
                                  [nil references])
          groupings (reduce (fn [total [op & batch]]
                              (case op
                                :require (update-in total [:refers] into (map parse-require (mapcat normalize-lib-spec batch)))
                                :import (update-in total [:imports] concat (mapcat normalize-import batch))
                                :refer-clojure (update-in total [:refers] into (map parse-refer (normalize-lib-spec (cons 'clojure.core batch))))
                                (:use :gen-class) (assert false)
                                ))
                            {:refers []
                             :imports '()}
                            references)
          context (reduce importer
                          (reduce referrer
                                  (&context/enter-ns context ns-name)
                                  (:refers groupings))
                          (:imports groupings))]
      ;; (prn 'groupings groupings)
      (list [context &type/Nil]))))

(defmethod analyse 'alt.typed/defalias [context [_ ctor doc-string type-def :as form]]
  (prn 'analyse 'alt.typed/defalias form)
  (let [type-def (or type-def doc-string)]
    (-> context
        (&ann/defalias* ctor type-def)
        (vector &type/Nil)
        list)))

(defmethod analyse 'alt.typed/ann [context [_ var-name type-def :as form]]
  (prn 'analyse 'alt.typed/ann var-name type-def)
  (let [full-var-name (if (nil? (namespace var-name))
                        (symbol (-> context &context/current-ns &ns/ns-name name) (name var-name))
                        (throw (ex-info "You can't annotate foreign variables." {:var var-name
                                                                                 :type type-def})))
        _ (assert (nil? (&library/lookup context full-var-name)))
        type (-> type-def (&parser/parse context) (&interpreter/eval context))]
    (prn 'ann/type type)
    (-> context
        (&library/save full-var-name type)
        (vector &type/Nil)
        list)))

(defmethod analyse ::fn-call [context [%fn & %args :as form]]
  (prn 'analyse ::fn-call form)
  (or (seq (for [[context $fn-inst] (analyse context %fn)
                 [context $args] (analyse-all context %args)
                 :let [_ (do (prn '%fn form)
                           (prn '$fn-inst (&translator/translate $fn-inst context))
                           (prn '$args (mapv (&util/partial* &translator/translate context) $args)))
                       _ (prn '$fn-inst (&translator/translate $fn-inst context))
                       =fn-inst (&graph/get-var context $fn-inst)
                       [context $fn-inst] (cond (&type/fn? =fn-inst)
                                                [context $fn-inst]

                                                (instance? TypeVar =fn-inst)
                                                (let [[context =min-fn] (min-fn-type context (mapv (partial &graph/get-var context) $args))]
                                                  (if-let [context (&solver/solve context (&graph/get-var context (.-id =fn-inst)) =min-fn)]
                                                    [context $fn-inst]
                                                    (assert false)))

                                                :else
                                                (assert (&type/fn? =fn-inst) "Must call a Fn type."))]
                 [context $return] (fn-call context =fn-inst $args)]
             [context $return]))
      (throw (ex-info "Function can't be applied to args." {:form form, :fn %fn, :args (vec %args)}))))

(defmethod analyse ::macro [context form]
  (prn 'analyse ::macro (&ns/ns-name context) form)
  (let [expansion (binding [*ns* (find-ns (&ns/ns-name context))]
                    (macroexpand-1 form))]
    (analyse context expansion)))

(def ^:private +native-clojure-forms+ #{'do 'def 'let* 'if 'fn* 'case* 'loop*})
(defmethod analyse ::default [context [op :as form]]
  (prn 'analyse ::default op form)
  (cond (not (symbol? op))
        ((get-method analyse ::fn-call) context form)

        (contains? +native-clojure-forms+ op)
        ((get-method analyse op) context form)

        :else
        (if-let [resolved-sym (&ns/resolve context op)]
          (let [impl (get-method analyse resolved-sym)]
            (if (not= impl (get-method analyse ::default))
              (impl context form)
              (if-let [$type (&graph/find context resolved-sym)]
                (do (prn 'default/$type (&translator/translate $type context))
                  (cond (&type/macro? $type)
                        ((get-method analyse ::macro) context form)

                        :else
                        ((get-method analyse ::fn-call) context form)))
                (throw (ex-info "Unknown form" {:form form})))))
          ((get-method analyse ::fn-call) context form))))
