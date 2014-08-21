(ns alt.typed.solver
  (:require (alt.typed [type :as &type]
                       [translator :as &translator])
            (alt.typed.context [store :as &store]
                               [library :as &library]))
  (:import (alt.typed.type LiteralType
                           ClassType
                           FnType
                           TypeVar
                           TypeAlias
                           OrType
                           TypeAlias
                           NotType
                           AnyType
                           NothingType
                           NilType)))

;; [Utils]
(def ^:private +types-hierarchy+
  (-> (make-hierarchy)
      (derive TypeVar          ::solvable)
      (derive ::type           ::solvable)
      (derive AnyType          ::type)
      (derive ::bounded-type   ::type)
      (derive ::complex-type   ::bounded-type)
      (derive NotType          ::complex-type)
      (derive OrType           ::complex-type)
      (derive ::simple-type    ::bounded-type)
      (derive NothingType      ::simple-type)
      (derive ::unit-type      ::simple-type)
      (derive NilType          ::unit-type)
      (derive LiteralType      ::unit-type)
      (derive ::open-type      ::simple-type)
      (derive ClassType        ::open-type)
      (derive FnType           ::open-type)
      ))

;; [Functions]
(defmulti solve (fn [store =expected =actual] [(class =expected) (class =actual)])
  :hierarchy #'+types-hierarchy+)

(defmethod solve [TypeAlias TypeAlias] [store ^TypeAlias =expected ^TypeAlias =actual]
  (solve store (.-real =expected) (.-real =actual)))

(defmethod solve [TypeAlias ::solvable] [store ^TypeAlias =expected =actual]
  (solve store (.-real =expected) =actual))

(defmethod solve [::solvable TypeAlias] [store =expected ^TypeAlias =actual]
  (solve store =expected (.-real =actual)))

(defmethod solve [TypeVar TypeVar] [store $expected $actual]
  (if-let [store (solve store (&store/retrieve store $expected) (&store/retrieve store $actual))]
    (&store/redirect store $expected $actual)))

(defmethod solve [::type TypeVar] [store =expected $actual]
  (let [=actual (&store/retrieve store $actual)]
    (or (solve store =expected =actual)
        (if-let [store (solve store =actual =expected)]
          (&store/constrain store $actual =expected)))))

(defmethod solve [TypeVar ::type] [store $expected =actual]
  (solve store (&store/retrieve store $expected) =actual))

(defmethod solve [AnyType ::type] [store =expected =actual]
  store)

(defmethod solve [::bounded-type AnyType] [store =expected =actual]
  nil)

(defmethod solve [::simple-type NotType] [store =expected ^NotType =actual]
  (if (not (solve store (.-type =actual) =expected))
    store)
  (assert false))

;; (defmethod solve [::&type/type TypeAlias] [store =expected ^TypeAlias =actual]
;;   (prn 'solve [::&type/type TypeAlias])
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

;; (defmethod solve [TypeAlias TypeVar] [store ^TypeAlias =expected $$actual]
;;   (prn 'solve '[TypeAlias TypeVar])
;;   (solve store (.-real =expected) $$actual))

;; (defmethod solve [TypeAlias TypeAlias] [store ^TypeAlias =expected ^TypeAlias =actal]
;;   (prn 'solve [TypeAlias TypeAlias])
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

;; ;; Narrowing (finding common subtypes)
(defmulti narrow (fn [store =test truthy?] (class =test))
  :hierarchy #'+types-hierarchy+)

(defmethod narrow TypeAlias [store ^TypeAlias =test truthy?]
  (narrow store (.-real =test) truthy?))

(defmethod narrow NilType [store =test truthy?]
  (if truthy?
    nil
    [store =test]))

(defmethod narrow AnyType [store =test truthy?]
  (if truthy?
    [store (&library/lookup store 'alt.typed/Truthy)]
    [store (&library/lookup store 'alt.typed/Falsey)]))

(defmethod narrow TypeVar [store $test truthy?]
  (let [=test (&store/retrieve store $test)]
    (if-let [[store =test] (narrow store =test truthy?)]
      [(&store/constrain store $test =test)
       =test])))

(let [filterer (fn [truthy? [store types*] type]
                 (if-let [[store type*] (narrow store type truthy?)]
                   [store (conj types* type*)]
                   [store types*]))]
  (defmethod narrow OrType [store ^OrType =test truthy?]
    (prn 'narrow 'OrType =test)
    (let [[store types*] (reduce (partial filterer truthy?) [store []] (.-types =test))]
      (case (count types*)
        0 nil
        1 [store (first types*)]
        ;; else
        [store (&type/or-type types*)]))))

;; (defmethod narrow [TypeAlias ::&type/real-type] [context ^TypeAlias =target =by]
;;   (if-let [[context =real] (narrow context (.-real =target) =by)]
;;     (if (= (.-real =target) =real)
;;       [context =target]
;;       [context =real])))

;; (defmethod narrow [::&type/type TypeAlias] [context =target ^TypeAlias =by]
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
