(ns system.util)

;; [Interface]
;; Protocols
(defprotocol Monad
  (bind [monad m-value step])
  (return [monad value]))

;; Implementations
(def state-seq-m
  (reify Monad
    (bind [self m-value step]
      #(for [[state* datum] (m-value %)
             result ((step datum) state*)]
         result))
    (return [self value]
      #(list [% value]))))

(def state-maybe-m
  (reify Monad
    (bind [self m-value step]
      #(if-let [[state* datum] (m-value %)]
         ((step datum) state*)))
    (return [self value]
      #(vector % value))))

(def state-m
  (reify Monad
    (bind [self m-value step]
      #(let [[state* datum] (m-value %)]
         ((step datum) state*)))
    (return [self value]
      #(vector % value))))

(def maybe-m
  (reify Monad
    (bind [self m-value step]
      (if (nil? m-value)
        nil
        (step m-value)))
    (return [self value]
      value)))

;; Syntax
(defmacro exec [monad steps return]
  (assert (not= 0 (count steps)) "The steps can't be empty!")
  (assert (= 0 (rem (count steps) 2)) "The number of steps must be even!")
  (reduce (fn [inner [label computation]]
            (case label
              :let `(let ~computation ~inner)
              ;; else
              `(bind ~monad ~computation (fn [~label] ~inner))))
          return
          (reverse (partition 2 steps))))

;; Functions
(defn map-m [monad f inputs]
  (if (empty? inputs)
    (return monad '())
    (exec monad
      [output (f (first inputs))
       outputs (map-m monad f (rest inputs))]
      (return monad (conj outputs output)))))

(defn reduce-m [monad f init inputs]
  (if (empty? inputs)
    (return monad init)
    (exec monad
      [next (f init (first inputs))]
      (reduce-m monad f next (rest inputs)))))

;; Only for state-seq monad...
(def zero (fn [state] (list)))

(defn return-all [data]
  #(for [datum data]
     [% datum]))

(def get-state
  #(list [% %]))

(defn parallel [steps]
  (fn [state]
    (some identity (map #(seq (% state)) steps))))

(defn parallel* [steps]
  (fn [state]
    (mapcat #(% state) steps)))

(defn collect [step]
  #(list [% (step %)]))

(defn spread [returns]
  (fn [state] returns))

(defn with-field [field monad]
  (fn [state]
    (if-let [[inner* return-val] (monad (field state))]
      (list [(assoc state field inner*) return-val])
      '())))

(defn with-field* [field monad]
  (fn [state]
    (for [[inner* return-val] (monad (field state))]
      [(assoc state field inner*) return-val])))
