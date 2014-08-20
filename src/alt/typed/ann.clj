(ns alt.typed.ann
  (:require (alt.typed [type :as &type]
                       [context :as &context]
                       [translator :as &translator])
            (alt.typed.context [ns :as &ns]
                               [library :as &library]
                               [env :as &env])
            (alt.typed.syntax [parser :as &parser]
                              [interpreter :as &interpreter]))
  (:import (alt.typed.type TypeOp
                           AliasType
                           ClassType
                           ClassTypeCtor
                           TypeCtor)))

;; [Utils]
(defn ^:private qualify-symbol [context sym]
  (symbol (name (&ns/ns-name context)) (name sym)))

;; [Functions]
(defn ann* [&context var-name type]
  {:pre [(and (symbol? var-name)
              (not (namespace var-name)))]}
  ;; (prn 'ann-var* var-name type)
  (let [=var (-> type (&parser/parse &context) (&interpreter/eval &context))
        &context (&ns/intern &context var-name)
        full-var-name (&ns/resolve &context var-name)]
    ;; (prn 'full-var-name full-var-name)
    (&env/ann &context full-var-name =var)))

(defn ann-macro* [&context var-name]
  {:pre [(and (symbol? var-name)
              (not (namespace var-name)))]}
  (let [&context (&ns/intern &context var-name)
        full-var-name (&ns/resolve &context var-name)]
    (&env/ann &context full-var-name &type/OpaqueMacro)))

(defn ann-class* [context class-ctor supers]
  {:pre [(vector? supers)]}
  ;; (prn 'ann-class* class-ctor supers)
  (let [[class-name params] (if (symbol? class-ctor)
                              [class-ctor []]
                              [(first class-ctor) (vec (rest class-ctor))])
        full-class-name (if (.contains (name class-name) ".")
                          class-name
                          (&ns/resolve context class-name))
        ;; _ (prn 'ann-class*/full-class-name full-class-name class-name)
        class-type (if (empty? params)
                     (ClassType. full-class-name [])
                     (ClassTypeCtor. full-class-name params))]
    (assert full-class-name (str "Class hasn't been imported: " class-name))
    ;; (prn 'ann-class* full-class-name (mapv #(&parser/parse % context) supers))
    ;; (prn 'class-type class-type)
    (&library/save context full-class-name class-type)))

(defn ann-static* [context member-type member type]
  (assert false))

(defn ann-member* [context member-type member type]
  (assert false))

(defn defop* [context op-name op-args op-fn]
  (assert (not (namespace op-name)))
  (let [full-name (qualify-symbol context op-name)]
    ;; (prn 'defop*/full-name full-name)
    (-> context
        (&library/save full-name (TypeOp. op-name op-args op-fn))
        (&ns/intern op-name))))

(defn defalias* [context ctor type-def]
  (prn 'defalias* ctor type-def)
  (let [[t-name t-args] (if (seq? ctor)
                          [(first ctor) (vec (rest ctor))]
                          [ctor []])]
    (assert (nil? (&ns/resolve context t-name))
            "Can't redefine a symbol in a namespace.")
    (let [full-type-name (qualify-symbol context t-name)
          alias-type (if (empty? t-args)
                       (let [type-expr (if-let [parsed-def (&parser/parse type-def context)]
                                         (&interpreter/eval parsed-def context)
                                         (throw (ex-info "Type definition can't be parsed." {:def type-def})))]
                         (AliasType. ctor [] type-expr))
                       (let [uq-type-ctor (if-let [parsed-def (&parser/parse `(~'alt.typed/All ~t-args ~type-def) context)]
                                            (&interpreter/eval parsed-def context)
                                            (throw (ex-info "Type definition can't be parsed." {:def type-def})))]
                         (assoc uq-type-ctor :alias full-type-name)))]
      (println "Saving:" full-type-name "- Interning:" t-name)
      (-> context
          (&library/save full-type-name alias-type)
          (&ns/intern t-name)))))

;; [Syntax]
(defmacro ann [context var-name type]
  `(ann* ~context '~var-name '~type))

(defmacro ann-macro [context var-name]
  `(ann-macro* ~context '~var-name))

(defmacro ann-class [context class-ctor supers]
  `(ann-class* ~context '~class-ctor '~supers))

(defmacro ann-static [context member-type member type]
  `(ann-static* ~context '~member-type '~member '~type))

(defmacro ann-member [context member-type member type]
  `(ann-member* ~context '~member-type '~member '~type))

(defmacro defop [context op-name op-args & op-def]
  `(defop* ~context '~op-name '~op-args (fn [~'&context ~'&env ~op-args] ~@op-def)))

(defmacro defalias [context ctor type-def]
  `(defalias* ~context '~ctor '~type-def))
