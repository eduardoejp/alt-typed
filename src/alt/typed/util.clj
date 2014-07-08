(ns alt.typed.util)

;; [Functions]
(defn atom? [form]
  (or (instance?              Boolean form)
      (instance?                 Byte form)
      (instance?                Short form)
      (instance?              Integer form)
      (instance?                 Long form)
      (instance?                Float form)
      (instance?               Double form)
      (instance?            Character form)
      (instance?               String form)
      (instance? clojure.lang.Keyword form)
      (instance?  clojure.lang.Symbol form)
      (instance? java.math.BigDecimal form)
      (instance?  clojure.lang.BigInt form)))

(defn partial* [f & args]
  #(apply f % args))

(defn fully-qualified-class? [sym]
  (and (nil? (namespace sym))
       (.contains (name sym) ".")))
