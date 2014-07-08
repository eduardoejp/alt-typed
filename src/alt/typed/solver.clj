(ns alt.typed.solver
  (:require (alt.typed [type :as &type]
                       [translator :as &translator])
            (alt.typed.context [graph :as &graph]))
  (:import (alt.typed.type LiteralType
                           ClassType
                           TypeVar
                           AliasType
                           OrType
                           AliasType
                           NotType
                           AnyType
                           NothingType
                           NilType)))

;; [Functions]
(defmulti solve (fn [graph expected actual] [(class expected) (class actual)])
  :hierarchy #'&type/*types-hierarchy*)

;; (defmethod solve [::&type/type AliasType] [graph =expected ^AliasType =actual]
;;   (prn 'solve [::&type/type AliasType])
;;   (solve graph =expected (.-real =actual)))

;; (defmethod solve [AnyType ::&type/type] [graph =expected =actual]
;;   (prn 'solve '[AnyType ::&type/type])
;;   graph)

;; (defmethod solve [NilType NilType] [graph =expected =actual]
;;   (prn 'solve [NilType NilType])
;;   graph)

;; (defmethod solve [::&type/bounded-type NilType] [graph =expected =actual]
;;   (prn 'solve [::&type/bounded-type NilType])
;;   nil)

;; (defmethod solve [NotType ::&type/bounded-type] [graph =expected =actual]
;;   (prn 'solve '[NotType ::&type/bounded-type])
;;   (if (not (&type/subsumes? (.-type =expected) =actual))
;;     graph))

;; (defmethod solve [::&type/type NothingType] [graph =expected =actual]
;;   (prn 'solve '[::&type/type NothingType])
;;   graph)

;; (defmethod solve [TypeVar TypeVar] [graph ^TypeVar $expected ^TypeVar $actual]
;;   (prn 'solve [TypeVar TypeVar])
;;   (let [_ (prn 'solve '[TypeVar TypeVar] [(.-id $actual) (.-id $expected)])
;;         =actual (&graph/get-var graph (.-id $actual))
;;         =expected (&graph/get-var graph (.-id $expected))]
;;     (if-let [graph (solve graph =actual =expected)]
;;       (&graph/constrain graph (.-id $expected) (&graph/get-var graph (.-id $actual))))))

;; (defmethod solve [::&type/bounded-type TypeVar] [graph =expected ^TypeVar $actual]
;;   (prn 'solve '[ClassType TypeVar] [(class =expected) (class $actual)])
;;   (let [=actual (&graph/get-var graph (.-id $actual))
;;         _ (prn 'solve '[ClassType TypeVar] '=actual (class =actual))]
;;     (if-let [graph (solve graph =actual =expected)]
;;       (&graph/constrain graph (.-id $actual) =expected))))

;; (defmethod solve [NotType TypeVar] [graph =expected ^TypeVar $actual]
;;   (if (not (&type/subsumes? (.-type =expected) (&graph/get-var graph (.-id $actual))))
;;     (&graph/constrain graph (.-id $actual) =expected)))

;; (defmethod solve [::&type/type OrType] [graph =expected ^OrType =actual]
;;   (prn 'solve [::&type/type OrType])
;;   (reduce (fn [g =t]
;;             (if g (solve g =expected =t)))
;;           graph
;;           (.-types =actual)))

;; (defmethod solve [::&type/bounded-type ::&type/bounded-type] [graph =expected =actual]
;;   (prn 'solve [::&type/bounded-type ::&type/bounded-type])
;;   (if (&type/subsumes? =expected =actual)
;;     graph))

;; (defmethod solve [AliasType TypeVar] [graph ^AliasType =expected $$actual]
;;   (prn 'solve '[AliasType TypeVar])
;;   (solve graph (.-real =expected) $$actual))

;; (defmethod solve [AliasType AliasType] [graph ^AliasType =expected ^AliasType =actal]
;;   (prn 'solve [AliasType AliasType])
;;   (solve graph (.-real =expected) (.-real =actal)))

(defn solve-all [graph =expected =actual]
  (reduce (fn [g [e a]]
            (if g
              (if-let [outcome (do (prn 'solve
                                        (class e) (&translator/translate e graph)
                                        (class a) (&translator/translate a graph))
                                 (solve g e a))]
                outcome
                (do (println "Couldn't solve:" [(&translator/translate e graph)
                                                (&translator/translate a graph)])
                  nil))))
          graph
          (map vector =expected =actual)))

;; TODO: Rewrite 'narrow to simplify it.
;; ;; Narrowing (finding common subtypes)
(defmulti narrow (fn [context =t1 =t2] [(class =t1) (class =t2)])
  :hierarchy #'&type/*types-hierarchy*)

;; (defmethod narrow [AliasType ::&type/real-type] [context ^AliasType =target =by]
;;   (if-let [[context =real] (narrow context (.-real =target) =by)]
;;     (if (= (.-real =target) =real)
;;       [context =target]
;;       [context =real])))

;; (defmethod narrow [::&type/type AliasType] [context =target ^AliasType =by]
;;   (narrow context =target (.-real =by)))

;; (defmethod narrow [OrType NotType] [context ^OrType =target =by]
;;   (let [[context =parts] (reduce (fn [[c ts] t]
;;                                    (if-let [[c* t*] (narrow c t =by)]
;;                                      [c* (conj ts t*)]
;;                                      [c ts]))
;;                                  [context []]
;;                                  (.-types =target))]
;;     (case (count =parts)
;;       0 nil
;;       1 [context (first =parts)]
;;       ;; else
;;       [context (&type/or-type =parts)])))

;; (defmethod narrow [TypeVar NotType] [context ^TypeVar $target ^NotType =by]
;;   (if (&type/subsumes? (.-type =by) (&graph/get-var context (.-id $target)))
;;     nil
;;     [(&graph/constrain context (.-id $target) =by) $target]))

;; (defmethod narrow [OrType OrType] [context ^OrType =target ^OrType =by]
;;   (prn '[OrType OrType] '=target (&translator/translate =target context) =target)
;;   (prn '[OrType OrType] '=by (&translator/translate =by context))
;;   (let [[context =filtered] (reduce (fn [[c ts] t]
;;                                       (if-let [[c* t*] (some #(narrow c t %1) (.-types =by))]
;;                                         [c* (conj ts t*)]
;;                                         [c ts]))
;;                                     [context []]
;;                                     (.-types =target))]
;;     (case (count =filtered)
;;       0 nil
;;       1 [context (first =filtered)]
;;       ;; else
;;       [context (&type/or-type =filtered)])))

;; (defmethod narrow [::&type/bounded-type ::&type/bounded-type] [context =target =by]
;;   (if (&type/subsumes? =by =target)
;;     [context =target]
;;     nil))

;; (defmethod narrow [::&type/bounded-type NotType] [context =target ^NotType =by]
;;   (prn '(&type/subsumes? NotType NilType) (&type/subsumes? (.-type =by) =target))
;;   (cond (&type/subsumes? (.-type =by) =target)
;;         nil

;;         (&type/subsumes? =target (.-type =by))
;;         (assert false "(And =target =by)")
        
;;         :else
;;         [context =target]))

;; (defmethod narrow [TypeVar ::&type/bounded-type] [context ^TypeVar $target =by]
;;   (if (&type/subsumes? =by (&graph/get-var context (.-id $target)))
;;     [context $target]
;;     nil))

;; (defmethod narrow [LiteralType OrType] [context =target =by]
;;   (prn 'narrow '[LiteralType OrType] [(&translator/translate =target context)
;;                                       (&translator/translate =by context)])
;;   (some (partial narrow context =target) (.-types =by)))

(comment
  (Maybe t) => (Or nil t)
  Truthy => (Not Falsey) => (Not (Or nil false))

  (Or nil t) % (Not (Or nil false)) =>> (And t (Not false))
  (Or nil t) < (Or nil false) == false

  Long % (Not Number) => Nothing
  Number % (Not Long) => (And Number (Not Long))

  Long % Number => Long
  Number % Long => Long
  )
