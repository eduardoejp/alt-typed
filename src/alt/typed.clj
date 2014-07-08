(ns alt.typed
  (:require (clojure [string :as string]
                     [set :as set]
                     [walk :as walk]
                     [template :refer [do-template]]
                     [repl :as repl])
            (alt.typed [analyser :as &analyser]
                       [reader :as &reader]
                       [prelude :as &&prelude]
                       [context :as &&context]
                       [translator :as &&translator])
            ))

;; [State]
;; (def ^:private !!annotated-sources (atom {}))

;; [Syntax]
(do-template [<name> <args>]
  (defmacro <name> <args> nil)

  ann       [var-name type]
  ann-class [class supers members]
  ann-form  [form type]
  trust     [binding|expr type])

(defmacro defalias
  ([ctor type]
     `(defalias ~ctor nil ~type))
  ([ctor doc-string type]
     (let [name (if (seq? ctor)
                  (first ctor)
                  ctor)]
       `(def ~(vary-meta name update-in [:doc] #(or % doc-string))))))

;; [Types]
(do-template [<name>]
  (def <name>)

  Any Nothing Nil
  Or And Not
  Array Fn All Rec
  Seq List Vector Map Set
  Maybe
  Truthy Falsey
  AnyInteger AnyFloat)

;; [Procedures]
;; (ann check-ns (Fn [-> (Try (Maybe (Vector Exception)) Exception)]
;;                   [Namespace -> (Try (Maybe (Vector Exception)) Exception)]))
(defn check-ns
  ([]
     (check-ns *ns*))
  ([ns]
     (let [[context errors] (reduce (fn [[context errors] form]
                                      (try (let [universes (&analyser/analyse context form)
                                                 ;; [context $form]
                                                 _ (println "Number of universes:" (count universes))
                                                 ;; syntax (&&translator/translate (&&graph/get-type context $form) context)
                                                 ]
                                             ;; (println "Successfully typed form:" syntax "---" form)
                                             (assert (= 1 (count universes))
                                                     (str "Ambiguous type (" (count universes) ") for expression: " form))
                                             [(-> universes first (nth 0)) errors])
                                        (catch Exception e
                                          (if (ex-data e)
                                            (do (.printStackTrace e ^java.io.PrintWriter *out*)
                                              [context (conj errors e)])
                                            (throw e)))))
                                    [(&&prelude/init &&context/+new-context+)
                                     []]
                                    (&reader/read-ns *ns*))]
       (if (not (empty? errors))
         errors))))

(comment
  (check-ns)
  )
