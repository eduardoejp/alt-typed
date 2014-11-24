(ns system.util
  (:require [clojure.core.match :refer [match]]))

;; [Utils]

(defn ^:private join-results [base addition]
  ;; (prn 'join-results base addition)
  (match [base addition]
    [[::ok ?old-worlds] [::ok ?new-worlds]]
    [::ok (concat ?old-worlds ?new-worlds)]
    
    [[::failure _] [::ok ?worlds]]
    addition
    
    [[::ok ?worlds] [::failure _]]
    base
    
    [[::failure _] [::failure _]]
    addition))

;; [Interface]
(defn merge-results [all-results]
  ;; (when true ;; (not (seq? all-results))
  ;;   (prn 'merge-results all-results))
  (reduce join-results [::failure "No results!"] all-results))

(defn results [output]
  (match output
    [::ok ?worlds]
    ?worlds
    
    [::failure _]
    '()))

(defn failed? [output]
  (match output
    [::ok _]
    false
    
    [::failure _]
    true))

(defn bind [m-value step]
  #(let [inputs (m-value %)]
     ;; (prn 'bind/inputs inputs)
     (match inputs
       [::ok ?worlds]
       (merge-results (for [[state* datum] ?worlds]
                        ((step datum) state*)))
       [::failure _]
       inputs)))

(defn send-ok [state value]
  [::ok (list [state value])])

(defn return [value]
  #(send-ok % value))

(defn fail* [message]
  [::failure message])

(defn fail [message]
  (fn [_]
    [::failure message]))

(defn assert! [test message]
  (if test
    (return nil)
    (fail message)))

;; (def zero (fn [state] [::ok '()]))
(def zero (fn [state] [::failure ""]))

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
  (fn [state]
    [::ok (for [datum data]
            [state datum])]))

(def get-state
  #(send-ok % %))

(defn try-all [steps]
  (fn [state]
    (let [results (for [step steps
                        :let [output (step state)]
                        :when (match output
                                [::ok ?worlds]
                                (not (empty? ?worlds))
                                :else
                                false)]
                    output)]
      (or (first results)
          [::failure "No alternative worked!"]))))

(defn parallel [steps]
  (fn [state]
    (let [all-results (map #(% state) steps)]
      ;; (prn 'parallel/all-results all-results)
      (merge-results all-results))))

(defn collect [step]
  #(match (step %)
     [::ok ?worlds]
     (send-ok % [::ok ?worlds])

     ?failure
     ?failure))

(defn spread [returns]
  (fn [state]
    returns))

(defn with-field [field monad]
  (fn [state]
    ;; (prn 'with-field (class state))
    (let [output (monad (field state))]
      ;; (prn 'with-field/output output)
      (match output
        [::ok ?results]
        [::ok (for [[?inner ?return-val] ?results]
                [(assoc state field ?inner) ?return-val])]
        ?failure
        ?failure))))
