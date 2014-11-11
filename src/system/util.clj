(ns system.util)

;; [Interface]
(defn bind [m-value step]
  #(for [[state* datum] (m-value %)
         result ((step datum) state*)]
     result))

(defn return [value]
  #(list [% value]))

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
     [% datum]))

(def get-state
  #(list [% %]))

(defn try-all [steps]
  (fn [state]
    (some identity (map #(seq (% state)) steps))))

(defn parallel [steps]
  (fn [state]
    (mapcat #(% state) steps)))

(defn collect [step]
  #(list [% (step %)]))

(defn spread [returns]
  (fn [state]
    returns))

(defn with-field [field monad]
  (fn [state]
    (for [[inner* return-val] (monad (field state))]
      [(assoc state field inner*) return-val])))
