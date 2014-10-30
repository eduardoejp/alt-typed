(ns system.env
  (:refer-clojure :exclude [resolve])
  (:require [clojure.core.match :refer [match]]
            (system [util :as &util :refer [state-maybe-m exec
                                            map-m reduce-m
                                            zero return return-all]]
                    [type :as &type])))

;; [Data]
(defrecord Env [globals stack])

;; [Interface]
;; Monads / Globals
(defn annotate [name type]
  (fn [^Env state]
    (when (not (-> state .-globals (contains? name)))
      [(assoc-in state [:globals name] type) nil])))

;; Monads / Stack
(defn enter [bindings]
  (fn [state]
    [(update-in state [:stack] conj bindings) nil]))

(def exit
  (fn [state]
    [(update-in state [:stack] rest) nil]))

;; Monads / Symbol Resolution
(defn resolve-var [symbol]
  (fn [^Env state]
    (when-let [=type (-> state .-globals (get symbol))]
      [state =type])))

(defn resolve [symbol]
  (fn [^Env state]
    (if-let [=type (->> state .-stack (some symbol))]
      [state =type]
      ((resolve-var symbol) state))))

;; Constants
(def +init+ (Env. {} '()))
