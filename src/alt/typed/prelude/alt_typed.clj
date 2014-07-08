(ns alt.typed.prelude.alt-typed
  (:require (alt.typed [context :as &context]
                       [type :as &type]
                       [ann :as &ann :refer [ann ann-class defop defalias]])
            (alt.typed.context [library :as &library]
                               [ns :as &ns])
            (alt.typed.syntax representation
                              [parser :as &parser]
                              [interpreter :as &interpreter :refer [eval*]]))
  (:import (alt.typed.syntax.representation Arity
                                            Fn
                                            Or
                                            Not
                                            All
                                            Rec)))

;; [Utils]
(defn ^:private helper-eval* [context env]
  #(eval* % context env))

;; [Functions]
(defn define-ops [context]
  (-> context
      (defop Fn [arity & arities*]
        (let [arities (conj arities* arity)
              parsed-arities (mapv #(&parser/parse-arity % &context &env) arities)]
          ;; (prn 'arities '== arities)
          ;; (prn 'arities '=> parsed-arities)
          (Fn. parsed-arities)))
      (defop All [args type-def]
        (let [args* (mapv (partial &parser/parse-type-var &context &env) args)
              parsed-def (&parser/parse type-def &context (into &env (map :name args*)))]
          (All. args* parsed-def)))
      (defop Rec [args type-def]
        (assert (and (vector? args)
                     (= 1 (count args))
                     (-> args first symbol?)
                     (-> args first namespace nil?)))
        (let [[arg] args
              parsed-def (&parser/parse type-def &context (conj &env arg))]
          (Rec. arg parsed-def)))
      (defop Or [t1 t2 & types*]
        (let [types (list* t1 t2 types*)
              parsed-types (mapv #(&parser/parse % &context &env) types)]
          ;; (prn 'types '== types)
          ;; (prn 'types '=> parsed-types)
          (Or. parsed-types)))
      (defop Not [type]
        (let [parsed-type (&parser/parse type &context &env)]
          (Not. parsed-type)))))

(defn init [context]
  (-> context
      (&context/enter-ns 'alt.typed)
      define-ops
      (&ns/intern 'defalias)
      (&ns/intern 'ann)
      (&library/save 'alt.typed/Any &type/Any)
      (&ns/intern 'Any)
      (&library/save 'alt.typed/Nothing &type/Nothing)
      (&ns/intern 'Nothing)
      (&library/save 'alt.typed/Nil &type/Nil)
      (&ns/intern 'Nil)
      ;; (&library/save 'alt.typed/OpaqueMacro &type/OpaqueMacro)
      ;; (&ns/intern 'OpaqueMacro)
      (defalias Falsey
        (Or nil false))
      (defalias Truthy
        (Not Falsey))
      (defalias (Maybe x)
        (Or nil x))
      (defalias (Map k v)
        (clojure.lang.IPersistentMap k v))
      ))

;; [Installation]
(extend-protocol &interpreter/IEval
  Arity
  (eval* [self context env]
    (let [helper (helper-eval* context env)]
      (&type/arity-type (mapv helper (.-args self)) (helper (.-return self)))))
  
  Fn
  (eval* [self context env]
    (&type/fn-type (mapv (helper-eval* context env) (.-arities self))))

  Or
  (eval* [self context env]
    (&type/or-type (mapv (helper-eval* context env) (.-types self))))

  Not
  (eval* [self context env]
    (&type/not-type (eval* (.-type self) context env)))
  )
