(ns alt.typed.type
  (:refer-clojure :exclude [fn? supers])
  (:require [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.template :refer [do-template]]
            [alt.typed.util :as &util]))

;; [Protocols]
(defprotocol Type
  (realize [type env]))

(defprotocol $TypeFn
  (params [type-fn])
  (match-arity? [type-fn args])
  (apply-fn [type-fn args])
  )

;; [Records]
(defrecord ArgInfo [name type])

;; [Types]
(defrecord EnvLookup [name]
  Type
  (realize [type &env]
    (or (get &env name)
        (throw (ex-info "Unbound type var." {:var name, :env &env})))))

(defrecord ClassType [name params]
  Type
  (realize [self &env]
    (update-in self [:params] (partial mapv (&util/partial* realize &env)))))

(defrecord AliasType [ctor args real]
  Type
  (realize [self &env]
    ;; (prn 'AliasType/realize ctor args real &env)
    (-> self
        (update-in [:args] (partial mapv (&util/partial* realize &env)))
        (update-in [:real] realize &env))))

(defrecord ArityType [normal-args rest-arg return]
  Type
  (realize [self &env]
    (-> self
        (update-in [:normal-args] (partial mapv (&util/partial* realize &env)))
        (update-in [:return] realize &env))))

(defrecord FnType [arities]
  Type
  (realize [self &env]
    (-> self
        (update-in [:arities] (partial mapv (&util/partial* realize &env))))))

(defrecord TupleType [members]
  Type
  (realize [self &env]
    (-> self
        (update-in [:members] (partial mapv (&util/partial* realize &env))))))

(do-template [<var> <type>]
  (do (defrecord <type> []
        Type
        (realize [self &env]
          self))
    (def <var> (new <type>)))

  Any         AnyType
  Nothing     NothingType
  Nil         NilType
  OpaqueMacro OpaqueMacroType
  )

(defrecord ClassTypeCtor [class args]
  $TypeFn
  (params [self]
    args)
  (match-arity? [self args]
    (= (count (.-args self))
       (count args)))
  (apply-fn [self args]
    {:pre [(match-arity? self args)]}
    (ClassType. class args))
  )

(defrecord TypeCtor [alias args type-def]
  $TypeFn
  (params [self]
    args)
  (match-arity? [self args]
    (= (count (.-args self))
       (count args)))
  (apply-fn [self args]
    {:pre [(match-arity? self args)]}
    ;; (prn 'TypeCtor/apply-fn 'self self)
    ;; (prn 'TypeCtor/apply-fn 'args args)
    (let [env (into (hash-map) (map vector (map :name (.-args self)) args))
          type-def* (realize type-def env)]
      (if alias
        (AliasType. alias args type-def*)
        type-def*)
      ;; (assert false)
      ))
  )

(defrecord TypeOp [op-name op-args op-fn])

(defrecord OrType [types]
  Type
  (realize [self &env]
    (update-in self [:types] (partial mapv (&util/partial* realize &env)))))

(defrecord NotType [type]
  Type
  (realize [self &env]
    (update-in self [:type] realize &env)))

(defrecord LiteralType [value]
  Type
  (realize [self &env]
    self))

(defrecord TypeVar [id name]
  Type
  (realize [self &env]
    (if-let [bound-type (get &env (.-name self))]
      bound-type
      (throw (ex-info "Unbound type var." {:var (.-name self)
                                           :env (set (keys &env))})))))

(defrecord RecToken [rec-type env]
  Type
  (realize [self &env]
    self))

(defrecord RecType [name type]
  Type
  (realize [self &env]
    (realize type (assoc &env name (RecToken. self &env)))))

;; ;; Regular
;; (defrecord ObjectType [class params]
;;   Type)

;; ;; Special
;; (defrecord ArrayType [class]
;;   Type)

;; (defrecord IntersectionType [types]
;;   Type)

;; ;; Inference
;; (defrecord DottedTypeVar [id name filled? types]
;;   Type)

;; [Functions]
(do-template [<name> <fn> <super>]
  (defn <name> [x]
    (<fn> <super> x))

  type?    satisfies? Type
  type-fn? satisfies? $TypeFn
  type-op? instance?  TypeOp
  macro?   instance?  OpaqueMacroType
  fn?      instance?  FnType)

(defn literal [value]
  {:pre [(&util/atom? value)]}
  (LiteralType. value))

(defn arity-type [args return]
  {:pre [(and (vector? args)
              (every? (partial satisfies? Type) args))
         (satisfies? Type return)]}
  (ArityType. args nil return))

(defn fn-type [arities]
  {:pre [(and (vector? arities)
              (every? (partial instance? ArityType) arities))]}
  (FnType. arities))

(defn or-type [types]
  {:pre [(and (vector? types)
              (every? (partial satisfies? Type) types))]}
  (OrType. types))

(defn not-type [type]
  {:pre [(satisfies? Type type)]}
  (NotType. type))

(defn apply-op [^TypeOp type-op context parsing-context args]
  ((.-op-fn type-op) context parsing-context args))

;; (def Falsey (AliasType. 'alt.typed/Falsey [] (or-type [Nil (LiteralType. false)])))
;; (def Truthy (AliasType. 'alt.typed/Truthy [] (not-type Falsey)))

;; (defmulti subsumes? (fn [expected actual] [(class expected) (class actual)])
;;   :default ::default
;;   :hierarchy #'*types-hierarchy*)

;; (defmethod subsumes? [       AnyType ::bounded-type] [expected actual] true)
;; (defmethod subsumes? [::bounded-type        AnyType] [expected actual] false)
;; (defmethod subsumes? [       AnyType        AnyType] [expected actual] true)

;; (defmethod subsumes? [::open-type NothingType] [expected actual] true)
;; (defmethod subsumes? [NothingType ::open-type] [expected actual] false)
;; (defmethod subsumes? [NothingType NothingType] [expected actual] false)

;; (defmethod subsumes? [NilType NilType] [expected actual]
;;   true)

;; (defmethod subsumes? [LiteralType LiteralType] [expected actual]
;;   (= expected actual))

;; (defmethod subsumes? [NotType ::simple-type] [^NotType expected actual]
;;   (not (subsumes? (.-type expected) actual)))

;; (defmethod subsumes? [OrType ::simple-type] [^OrType expected actual]
;;   (boolean (some (&util/partial* subsumes? actual) (.-types expected))))

;; (defmethod subsumes? [AliasType ::real-type] [^AliasType expected actual]
;;   (subsumes? (.-real expected) actual))

;; (defmethod subsumes? [::type AliasType] [expected ^AliasType actual]
;;   (subsumes? expected (.-real actual)))

;; ;; (defmethod subsumes? [::simple-type ::simple-type] [expected actual]
;; ;;   false)

;; (defmethod subsumes? [ClassType ClassType] [expected actual]
;;   (and (= (.-name expected) (.-name actual))
;;        (every? identity
;;                (map subsumes? (.-params expected) (.-params actual)))))

;; (defmethod subsumes? ::default [expected actual]
;;   (prn 'subsumes? ::default [(class expected) (class actual)])
;;   (prn 'subsumes? ::default expected actual)
;;   ;; (assert false)
;;   false
;;   )

;; (comment
;;   (ann while (All [x]
;;                   [x [x -> Boolean] [x -> x] -> x]))
;;   (defn while [init test body]
;;     (if (test init)
;;       (recur (body init) test body)
;;       init))

;;   (defalias Person (Rec [self]
;;                         {::name    String
;;                          ::age     Int
;;                          ::parents {::father (Maybe self)
;;                                     ::mother (Maybe self)}}))

;;   (defalias Employee {::company     String
;;                       ::employee-id String
;;                       & Person})

;;   (ann-record Person (Rec [self]
;;                           (Record {::name String
;;                                    ::age  Int
;;                                    ::parents '[(Maybe self) (Maybe self)]})))
;;   (defrecord Person [name age parents])

;;   (ann-record Employee (Record {::company String
;;                                 ::employee-id String
;;                                 & Person}))
;;   (defrecord Employee [name age parents company employee-id])

;;   (ann assoc (All [r k v]
;;                   (Fn [{& r} k v -> {k v & r}]
;;                       [{k Any & r} k v -> {k v & r}]
;;                       [(Map k v) k v & (k v) -> (Map k v)])
;;                   ))

;;   (! nil)
;;   (| String Number)
;;   (& Foo Bar)
;;   (% Object int float boolean)

;;   (ann assoc (All [r k v]
;;                   (Fn [{& r} k v -> {k v & r}]
;;                       [{k Any & r} k v -> {k v & r}]
;;                       [(Map k v) k v & (k v) -> (Map k v)])
;;                   ))

;;   (ann assoc (All [r k v & (ks vs)]
;;                   [{& r} k v & ~@(ks vs) -> {k v ~@ks ~@vs & r}]
;;                   ))

;;   (ann dissoc (All [r k & ks]
;;                    (Fn[(Record {k Any ~@ks Any & r}) k & ~@ks -> {& r}]
;;                       [{k Any ~@ks Any & r} k & ~@ks -> {& r}])))

;;   (ann map (All [ret l & ls]
;;                 [[l ~@ls -> ret] l ~@(Seq ls) -> (List ret)]))

  
  
;;   (def person {::name "Eduardo"
;;                ::$say-hello (fn [o hello] (str hello " " (::name o)))})

;;   (defalias Person
;;     (Rec [self]
;;          {::name String
;;           ::$say-hello [self String -> String]}))

;;   ((::$say-hello person) person)

;;   (ann call (All [ret r msg & args]
;;                  (Fn [(Rec [full-obj]
;;                            {msg [full-obj ~@args -> ret] & r})
;;                       msg
;;                       ~@args
;;                       ret])))
;;   (defn call [object message-type & params]
;;     ((message-type object) object params))

;;   (call person ::$say-hello "Hola")

;;   (ann apply (All [ret args]
;;                   [[~@args -> ret] ~@args -> ret]))
;;   (apply + '(1 2 3 4 5))

;;   '[Integer Integer & Integer]

;;   (ann + (All [[n < (Xor AnyInteger AnyFloat Number)]]
;;               (Fn [-> 0]
;;                   [n -> n]
;;                   [& n -> n])))

;;   x < (Or Long Double) => Number

;;   (ann assoc (All [k v]
;;                   (Let [[r < {}]
;;                         [m < (Xor {k Any & r} {& r})]]
;;                        (Fn [m k v -> {k v & r}]
;;                            [(Map k v) k v -> (Map k v)]))
;;                   ))

;;   (ann assoc (All [k v]
;;                   (Let [[r < {}]
;;                         [m < (Xor (Record {k Any & r}) {(? k) Any & r})]]
;;                        (Fn [m k v -> {k v & r}]
;;                            [(Map k v) k v -> (Map k v)]))
;;                   ))

;;   (-> {:a 1}
;;       (with-meta {::type :record})
;;       (assoc :b 2)
;;       (merge {:c 3})
;;       meta)

;;   (ann number? (Fn [Number       -> true]
;;                    [(Not Number) -> false]))

;;   (ann number [Any -> Boolean :filters {:then (is 0 Number),
;;                                         :else (! 0 Number)}])

;;   (ann assoc (All [r k v]
;;                   (Fn [{(? k) Any & r} k v -> {k v & r}]
;;                       [(Record {k v & r}) k v -> {k v & r}]
;;                       [(Map k v) k v -> (Map k v)])
;;                   ))

;;   (let* [vec__2910 p__2905
;;          x (nth vec__2910 0 nil)
;;          y (nth vec__2910 1 nil)
;;          zs (nthnext vec__2910 2)]
;;         [x y zs])

;;   ((fn [& [x y & zs]] `[~x ~y ~@zs])
;;    1 2 3 4 5)
;;   =>
;;   [1 2 3 4 5]

;;   (All [& ts]
;;        [[~@ts -> '[~@ts]]])

;;   (Rec [elem]
;;        '[Keyword (? (Map Keyword Any)) (* elem)])

;;   )
