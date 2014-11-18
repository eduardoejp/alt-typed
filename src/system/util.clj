(ns system.util
  (:require [clojure.core.match :refer [match]]))

;; [Interface]
(defn bind [m-value step]
  #(for [input (do ;; (prn 'bind/% (class %))
                 (m-value %))
         ;; :let [_ (prn 'bind/input (nth input 0))]
         result (match input
                  [::ok [state* datum]]
                  ((step datum) state*))]
     result))

(defn send-ok [state value]
  (list [::ok [state value]]))

(defn return [value]
  #(send-ok % value))

(def zero (fn [state] (list)))

;; Syntax
(defmacro exec [steps return]
  (assert (not= 0 (count steps)) "The steps can't be empty!")
  (assert (= 0 (rem (count steps) 2)) "The number of steps must be even!")
  (reduce (fn [inner [label computation]]
            (case label
              :let `(let ~computation ~inner)
              :when `(if ~computation
                       ~inner
                       zero)
              ;; else
              `(bind ~computation (fn [~label] ~inner))))
          return
          (reverse (partition 2 steps))))

;; Functions
(defn map-m [f inputs]
  (if (empty? inputs)
    (return '())
    (exec [output (f (first inputs))
           outputs (map-m f (rest inputs))]
      (return (conj outputs output)))))

(defn reduce-m [f init inputs]
  (if (empty? inputs)
    (return init)
    (exec [next (f init (first inputs))]
      (reduce-m f next (rest inputs)))))

(defn return-all [data]
  #(for [datum data]
     [::ok [% datum]]))

(def get-state
  #(send-ok % %))

(defn try-all [steps]
  (fn [state]
    (some identity (map #(seq (% state)) steps))))

(defn parallel [steps]
  (fn [state]
    (mapcat #(% state) steps)))

(defn collect [step]
  #(send-ok % (step %)))

(defn spread [returns]
  (fn [state]
    returns))

(defn with-field [field monad]
  (fn [state]
    ;; (prn 'with-field (class state))
    (for [input (monad (field state))]
      (match input
        [::ok [?inner ?return-val]]
        [::ok [(assoc state field ?inner) ?return-val]]))))
