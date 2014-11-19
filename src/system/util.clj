(ns system.util
  (:require [clojure.core.match :refer [match]]))

;; [Interface]
(defn failure? [result]
  (match result
    [::failure _]
    true

    :else
    false))

(defn ok? [result]
  (match result
    [::ok _]
    true

    :else
    false))

(defn clean-results [results]
  (cond (empty? results)
        results

        (every? failure? results)
        (-> results first list)

        :else
        (filter ok? results)))

(defn bind [m-value step]
  #(for [input (clean-results (m-value %))
         ;; :let [_ (prn 'input input)]
         result (clean-results (match input
                                 [::ok [state* datum]]
                                 ((step datum) state*)
                                 [::failure _]
                                 (list input)))]
     result))

(defn send-ok [state value]
  (list [::ok [state value]]))

(defn return [value]
  #(send-ok % value))

(defn fail [message]
  (fn [_]
    (list [::failure message])))

(defn assert! [test message]
  (if test
    (return nil)
    (fail message)))

(def zero (fn [state] (list)))

;; Syntax
(defmacro exec [steps return]
  (assert (not= 0 (count steps)) "The steps can't be empty!")
  (assert (= 0 (rem (count steps) 2)) "The number of steps must be even!")
  (reduce (fn [inner [label computation]]
            (case label
              :let `(let ~computation ~inner)
              ;; :when (assert false "Can't use :when")
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
    (if (empty? steps)
      '()
      (let [results (clean-results ((first steps) state))]
        (if (ok? (first results))
          results
          (or ((try-all (rest steps)) state)
              results))))
    ;; (some identity (map #(seq (clean-results (% state))) steps))
    ))

(defn try-all* [steps]
  (fn [state]
    (if (empty? steps)
      '()
      (or (seq (clean-results ((first steps) state)))
          ((try-all (rest steps)) state)))))

(defn parallel [steps]
  (fn [state]
    (mapcat #(clean-results (% state)) steps)))

(defn collect [step]
  #(send-ok % (clean-results (step %))))

(defn spread [returns]
  (fn [state]
    returns))

(defn with-field [field monad]
  (fn [state]
    ;; (prn 'with-field (class state))
    (let [results (monad (field state))
          ;; _ (prn 'results results)
          results (clean-results results)
          ;; _ (prn 'results results)
          ]
      (for [input results]
        (match input
          [::ok [?inner ?return-val]]
          [::ok [(assoc state field ?inner) ?return-val]]
          [::failure _]
          input)))))
