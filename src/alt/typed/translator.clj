(ns alt.typed.translator
  (:require (alt.typed [util :as &util]
                       [type :as &type]
                       [context :as &context])
            (alt.typed.context [ns :as &ns]
                               [store :as &store]))
  (:import (alt.typed.type LiteralType
                           EnvLookup
                           ClassType
                           AliasType
                           ArityType
                           FnType
                           TupleType
                           OrType
                           NotType
                           RecType
                           RecToken
                           TypeCtor
                           TypeVar
                           AnyType
                           NothingType
                           NilType
                           OpaqueMacroType)))

;; [Utils]
(defn ^:private nickname-symbol [sym &context]
  ;; (prn 'nickname-symbol sym)
  (or (if (namespace sym)
        (&ns/common-name &context sym)
        (&ns/ns-import &context sym))
      sym))

;; [Protocols]
(defprotocol ITranslate
  (translate [type context]))

;; [Implementations]
(extend-protocol ITranslate
  AnyType
  (translate [self &context]
    (nickname-symbol 'alt.typed/Any &context))

  NothingType
  (translate [self &context]
    (nickname-symbol 'alt.typed/Nothing &context))
  
  NilType
  (translate [self &context]
    nil)

  OpaqueMacroType
  (translate [self &context]
    'OpaqueMacro)
  
  EnvLookup
  (translate [self &context]
    (.-name self))
  
  ClassType
  (translate [self &context]
    (if-let [params (seq (.-params self))]
      (cons (nickname-symbol (.-name self) &context)
            (map (&util/partial* translate &context) params))
      (nickname-symbol (.-name self) &context)))

  AliasType
  (translate [self &context]
    ;; (prn 'AliasType/translate (.-ctor self))
    (if-let [params (seq (.-args self))]
      (cons (nickname-symbol (.-ctor self) &context)
            (map (&util/partial* translate &context) params))
      (nickname-symbol (.-ctor self) &context)))

  ArityType
  (translate [self &context]
    (let [translate* (&util/partial* translate &context)]
      (if-let [rest-arg (.-rest-arg self)]
        `[~@(map translate* (.-normal-args self)) ~'& ~(translate rest-arg &context) ~'-> ~(translate (.-return self) &context)]
        `[~@(map translate* (.-normal-args self)) ~'-> ~(translate (.-return self) &context)])))

  FnType
  (translate [self &context]
    (let [arities (.-arities self)]
      (if (= 1 (count arities))
        (translate (first arities) &context)
        (cons (nickname-symbol `&type/Fn &context)
              (map (&util/partial* translate &context) arities)))))

  ;; TupleType
  ;; (translate [self &context]
  ;;   `'[~@(map (&util/partial* translate &context) (.-members self))])

  OrType
  (translate [self &context]
    (cons (nickname-symbol `&type/Or &context)
          (map (&util/partial* translate &context) (.-types self))))

  NotType
  (translate [self &context]
    (list (nickname-symbol `&type/Not &context) (translate (.-type self) &context)))

  LiteralType
  (translate [self &context]
    (.-value self))

  RecType
  (translate [self &context]
    (list (nickname-symbol `&type/Rec &context)
          [(.-name self)]
          (translate (.-type self) &context)))

  RecToken
  (translate [self &context]
    (-> self ^RecType (.-rec-type) .-name))

  TypeCtor
  (translate [self &context]
    ;; (prn 'TypeCtor/translate (.-alias self))
    (if-let [alias (.-alias self)]
      `(~(nickname-symbol alias &context) ~(mapv :name (.-args self)))
      `(~(nickname-symbol `alt.typed/All &context) ~(mapv :name (.-args self)) ~(translate (.-type-def self) &context))))

  TypeVar
  (translate [^TypeVar self &context]
    (symbol (str "⟨" (.-name self) ":" (translate (&store/retrieve &context self) &context) "⟩")))
  )
