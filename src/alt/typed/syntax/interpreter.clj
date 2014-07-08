(ns alt.typed.syntax.interpreter
  (:refer-clojure :exclude [eval])
  (:require (alt.typed [util :as &util]
                       [type :as &type]
                       [context :as &context])
            (alt.typed.context [library :as &library])
            [alt.typed.syntax.representation :as &repr])
  (:import (alt.typed.syntax.representation Literal
                                            Identifier
                                            TypeVar
                                            TypeCtorCall
                                            All
                                            Rec)
           (alt.typed.type TypeCtor
                           RecType
                           RecToken
                           ArgInfo
                           EnvLookup)))

;; [Protocols]
(defprotocol IEval
  (eval* [type-repr context &env]))

;; [Implementations]
(extend-protocol IEval
  Literal
  (eval* [self context &env]
    (&type/literal (.-value self)))
  
  Identifier
  (eval* [self context &env]
    ;; (prn 'Identifier/eval* (class context) (class &env))
    (let [id-name (.-name self)]
      (or (if (contains? &env id-name)
            (EnvLookup. id-name)
            (&library/lookup context id-name))
          (throw (ex-info "Unbound type." {:type id-name
                                           :env &env})))))

  TypeCtorCall
  (eval* [self context &env]
    (let [ctor (.-ctor self)]
      (if-let [=ctor (&library/lookup context ctor)]
        (let [=args (mapv #(eval* % context &env) (.-args self))]
          (&type/apply-fn =ctor =args))
        (throw (ex-info "Unbound type constructor." {:ctor ctor})))))

  All
  (eval* [self context &env]
    (let [params (mapv (fn [^TypeVar v]
                         (ArgInfo. (.-name v) (eval* (.-type v) context &env)))
                       (.-vars self))
          =type (eval* (.-type self) context (into &env (map :name (.-vars self))))]
      (TypeCtor. nil params =type)))

  Rec
  (eval* [self &context &env]
    (let [self-ref (.-self self)]
      (RecType. self-ref (eval* (.-type self) &context (conj &env self-ref)))))
  
  ;; RecursiveDefinition
  ;; (eval* [self env context]
  ;;   )
  )

(defn eval [repr context]
  (eval* repr context #{}))

;; (defrecord RecursiveDefinition [self type])
