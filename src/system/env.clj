(ns system.env
  (:require [clojure.string :as string]
            (system [util :as &util :refer [exec
                                            map-m reduce-m
                                            zero return return-all]]))
  (:refer-clojure :exclude [resolve in-ns create-ns refer import intern]))

;; [Data]
(defrecord NS [name referrals imports local-symbols all-symbols])
(defrecord Refer [namespace alias local-symbols all-symbols])
(defrecord Env [ns-current ns-others stack])

;; [Utils]
(defn ^:private fresh-ns [name]
  (NS. name {} #{} {} {}))

(defn ^:private create-ns [name]
  (fn [^Env state]
    (if (or (-> state ^NS (.-ns-current) .-name (= name))
            (-> state .-ns-others (contains? name)))
      (list [state nil])
      (list [(update-in state [:ns-others] assoc name (fresh-ns name)) nil]))))

(defn ^:private enter-ns [name]
  (fn [^Env state]
    (cond (-> state ^NS (.-ns-current) .-name (= name))
          (list [state nil])

          (-> state .-ns-others (contains? name))
          (list [(assoc state :ns-current (-> state .-ns-others (get name))) nil])

          :else
          '())
    ))

;; [Interface]
;; Monads / NS
(defn in-ns [name]
  (exec [_ (create-ns name)]
    (enter-ns name)))

(def current-ns
  (fn [^Env state]
    (list [state (-> state ^NS (.-ns-current) .-name)])))

(defn refer [^Refer referral]
  (fn [state]
    (list [(-> state
               (update-in [:ns-current :referrals (.-namespace referral)]
                          #(-> (or % referral)
                               (assoc-in [:alias] (.-alias referral))
                               (update-in [:local-symbols] merge (.-local-symbols referral))))
               (update-in [:ns-current :all-symbols]
                          #(-> %
                               (merge (.-local-symbols referral))
                               (into (let [refer-ns* (name (.-namespace referral))]
                                       (for [[sym type] (.-all-symbols referral)] [(symbol refer-ns* (name sym)) type])))
                               (into (if-let [alias (.-alias referral)]
                                       (let [refer-ns* (name alias)]
                                         (for [[sym type] (.-all-symbols referral)] [(symbol refer-ns* (name sym)) type]))
                                       '())))))
           nil])))

(defn import [class]
  (let [short-name (last (string/split (name class) #"\."))]
    (fn [state]
      (list [(update-in state [:ns-current]
                        #(-> %
                             (update-in [:imports] conj class)
                             (update-in [:all-symbols] assoc class 'YOLO short-name 'YOLO)))
             nil]))
    ))

(defn intern [symbol type]
  (if (namespace symbol)
    zero
    (fn [state]
      (list [(-> state
                 (update-in [:ns-current :local-symbols] assoc symbol type)
                 (update-in [:ns-current :all-symbols] assoc symbol type))
             nil]))))

;; Monads / Stack
(defn enter [bindings]
  (fn [state]
    (list [(update-in state [:stack] conj bindings) nil])))

(def exit
  (fn [state]
    (list [(update-in state [:stack] rest) nil])))

;; Monads / Symbol Resolution
(defn resolve-var [symbol]
  (fn [^Env state]
    (if-let [=type (-> state ^NS (.-ns-current) .-all-symbols (get symbol))]
      (list [state =type])
      '())))

(defn resolve [symbol]
  (fn [^Env state]
    (if-let [=type (->> state .-stack (some symbol))]
      (list [state =type])
      ((resolve-var symbol) state))))

;; Constants
(def +init+ (Env. (fresh-ns 'user) {} '()))
