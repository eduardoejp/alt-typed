(ns alt.typed.solver
  (:require (alt.typed [type :as &type]
                       [translator :as &translator])
            (alt.typed.context [store :as &store]))
  (:import (alt.typed.type LiteralType
                           ClassType
                           FnType
                           TypeVar
                           AliasType
                           OrType
                           AliasType
                           NotType
                           AnyType
                           NothingType
                           NilType)))

(def ^:private ^:dynamic *types-hierarchy*
  (-> (make-hierarchy)
      (derive AliasType        ::type)
      (derive ::real-type      ::type)
      (derive ::complex-type   ::real-type)
      (derive NotType          ::complex-type)
      (derive OrType           ::complex-type)
      (derive ::simple-type    ::real-type)
      (derive AnyType          ::simple-type)
      (derive ::bounded-type   ::simple-type)
      (derive NothingType      ::bounded-type)
      (derive ::unit-type      ::bounded-type)
      (derive NilType          ::unit-type)
      (derive LiteralType      ::unit-type)
      (derive ::open-type      ::bounded-type)
      (derive ClassType        ::open-type)
      (derive FnType           ::open-type)
      ))

;; [Functions]
(defmulti solve (fn [store expected actual] [(class expected) (class actual)])
  :hierarchy #'*types-hierarchy*)

;; (defmethod solve [::&type/type AliasType] [store =expected ^AliasType =actual]
;;   (prn 'solve [::&type/type AliasType])
;;   (solve store =expected (.-real =actual)))

;; (defmethod solve [AnyType ::&type/type] [store =expected =actual]
;;   (prn 'solve '[AnyType ::&type/type])
;;   store)

;; (defmethod solve [NilType NilType] [store =expected =actual]
;;   (prn 'solve [NilType NilType])
;;   store)

;; (defmethod solve [::&type/bounded-type NilType] [store =expected =actual]
;;   (prn 'solve [::&type/bounded-type NilType])
;;   nil)

;; (defmethod solve [NotType ::&type/bounded-type] [store =expected =actual]
;;   (prn 'solve '[NotType ::&type/bounded-type])
;;   (if (not (&type/subsumes? (.-type =expected) =actual))
;;     store))

;; (defmethod solve [::&type/type NothingType] [store =expected =actual]
;;   (prn 'solve '[::&type/type NothingType])
;;   store)

;; (defmethod solve [TypeVar TypeVar] [store ^TypeVar $expected ^TypeVar $actual]
;;   (prn 'solve [TypeVar TypeVar])
;;   (let [_ (prn 'solve '[TypeVar TypeVar] [(.-id $actual) (.-id $expected)])
;;         =actual (&store/get-var store (.-id $actual))
;;         =expected (&store/get-var store (.-id $expected))]
;;     (if-let [store (solve store =actual =expected)]
;;       (&store/constrain store (.-id $expected) (&store/get-var store (.-id $actual))))))

;; (defmethod solve [::&type/bounded-type TypeVar] [store =expected ^TypeVar $actual]
;;   (prn 'solve '[ClassType TypeVar] [(class =expected) (class $actual)])
;;   (let [=actual (&store/get-var store (.-id $actual))
;;         _ (prn 'solve '[ClassType TypeVar] '=actual (class =actual))]
;;     (if-let [store (solve store =actual =expected)]
;;       (&store/constrain store (.-id $actual) =expected))))

;; (defmethod solve [NotType TypeVar] [store =expected ^TypeVar $actual]
;;   (if (not (&type/subsumes? (.-type =expected) (&store/get-var store (.-id $actual))))
;;     (&store/constrain store (.-id $actual) =expected)))

;; (defmethod solve [::&type/type OrType] [store =expected ^OrType =actual]
;;   (prn 'solve [::&type/type OrType])
;;   (reduce (fn [g =t]
;;             (if g (solve g =expected =t)))
;;           store
;;           (.-types =actual)))

;; (defmethod solve [::&type/bounded-type ::&type/bounded-type] [store =expected =actual]
;;   (prn 'solve [::&type/bounded-type ::&type/bounded-type])
;;   (if (&type/subsumes? =expected =actual)
;;     store))

;; (defmethod solve [AliasType TypeVar] [store ^AliasType =expected $$actual]
;;   (prn 'solve '[AliasType TypeVar])
;;   (solve store (.-real =expected) $$actual))

;; (defmethod solve [AliasType AliasType] [store ^AliasType =expected ^AliasType =actal]
;;   (prn 'solve [AliasType AliasType])
;;   (solve store (.-real =expected) (.-real =actal)))

(defn solve-all [store =expected =actual]
  (reduce (fn [g [e a]]
            (if g
              (if-let [outcome (do (prn 'solve
                                        (class e) (&translator/translate e store)
                                        (class a) (&translator/translate a store))
                                 (solve g e a))]
                outcome
                (do (println "Couldn't solve:" [(&translator/translate e store)
                                                (&translator/translate a store)])
                  nil))))
          store
          (map vector =expected =actual)))

;; TODO: Rewrite 'narrow to simplify it.
;; ;; Narrowing (finding common subtypes)
(defmulti narrow (fn [context =t1 =t2] [(class =t1) (class =t2)])
  :hierarchy #'*types-hierarchy*)

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
;;   (if (&type/subsumes? (.-type =by) (&store/get-var context (.-id $target)))
;;     nil
;;     [(&store/constrain context (.-id $target) =by) $target]))

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
;;   (if (&type/subsumes? =by (&store/get-var context (.-id $target)))
;;     [context $target]
;;     nil))

;; (defmethod narrow [LiteralType OrType] [context =target =by]
;;   (prn 'narrow '[LiteralType OrType] [(&translator/translate =target context)
;;                                       (&translator/translate =by context)])
;;   (some (partial narrow context =target) (.-types =by)))

(comment
  (Maybe t) => (Or nil t)
  Truthy => (Not Falsey) => (Not (Or nil false))

  (Or nil t) % (Not (Or nil false)) => (And t (Not false)) && t < (Not (Or nil false))
  (Or nil t) < (Or nil false) == false

  Long % (Not Number) => Nothing
  Number % (Not Long) => (And Number (Not Long))

  Long % Number => Long
  Number % Long => Long
  )
