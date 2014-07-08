(ns alt.typed.syntax.parser
  (:require (alt.typed [util :as &util]
                       [context :as &context]
                       [type :as &type])
            (alt.typed.context [library :as &library]
                               [ns :as &ns])
            [alt.typed.syntax.representation :as &repr])
  (:import (alt.typed.syntax.representation Literal
                                            Identifier
                                            TypeVar
                                            TypeCtorCall
                                            Arity)))

;; [Utils]
(defn ^:private literal? [form]
  (or (&util/atom? form)
      (and (seq? form)
           (= 'quote (first form))
           (&util/atom? (second form)))))

(defn ^:private parse-literal [form]
  (if (&util/atom? form)
    (Literal. form)
    (Literal. (second form))))

(def ^:private fn-sugar? vector?)

(defn ^:private desugar-fn [form]
  `(~'alt.typed/Fn ~form))

;; [Functions]
(defn parse
  ([type-syntax context]
     (parse type-syntax context #{}))
  ([type-syntax context &env]
     (cond (nil? type-syntax)
           (Identifier. 'alt.typed/Nil)
           
           (symbol? type-syntax)
           (if (contains? &env type-syntax)
             (Identifier. type-syntax)
             (if-let [full-id (or (&ns/resolve context type-syntax)
                                  (if (&library/lookup context type-syntax)
                                    type-syntax))]
               (Identifier. full-id)
               (do (prn type-syntax context)
                 (prn (&ns/resolve context type-syntax))
                 (prn (&library/lookup context type-syntax))
                 (throw (ex-info "Unresolved symbol." {:form type-syntax})))))

           (literal? type-syntax)
           (parse-literal type-syntax)

           ;; Short function syntax
           (fn-sugar? type-syntax)
           (recur (desugar-fn type-syntax) context &env)

           (seq? type-syntax)
           (let [[op|ctor* & args*] type-syntax
                 args (vec args*)
                 op|ctor (&ns/resolve context op|ctor*)]
             (if-let [type|type-fn|op (&library/lookup context op|ctor)]
               (cond (&type/type? type|type-fn|op)
                     (throw (ex-info "Types can't be used as type constructors." {:form type-syntax}))

                     (&type/type-op? type|type-fn|op)
                     (&type/apply-op type|type-fn|op context &env args)

                     (&type/type-fn? type|type-fn|op)
                     (if (&type/match-arity? type|type-fn|op args)
                       (TypeCtorCall. op|ctor (mapv (&util/partial* parse context &env) args))
                       (throw (ex-info "Arity mismatch in type constructor." {:expected type|type-fn|op
                                                                              :actual args})))
                     
                     :else
                     (throw (ex-info "WTF is this?" {:wtf type|type-fn|op})))
               (do (prn `(~'&ns/resolve ~'context ~op|ctor*) (&ns/resolve context op|ctor*))
                 (prn 'context context)
                 (throw (ex-info "Unknown type constructor/operator." {:op op|ctor*
                                                                       :form type-syntax})))))

           :else
           (throw (ex-info "Type syntax could not be parsed." {:syntax type-syntax})))))

(defn parse-arity [arity-vector context &env]
  ;; (prn 'parse-arity (class context) (class &env))
  (let [[args* [_ return*]] (split-with (partial not= '->) arity-vector)
        helper (&util/partial* parse context &env)]
    (Arity. (mapv helper args*) (helper return*))))

(defn parse-type-var [&context &env var-syntax]
  (assert (symbol? var-syntax))
  (TypeVar. var-syntax (Identifier. 'alt.typed/Any)))
