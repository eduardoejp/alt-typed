(ns system.ns
  (:require [clojure.string :as string]
            (system [util :as &util :refer [state-maybe-m exec
                                            map-m reduce-m
                                            zero return return-all]]))
  (:refer-clojure :exclude [in-ns create-ns refer import intern]))

;; [Data]
(defrecord NS [name referrals imports symbols])
(defrecord Refer [namespace alias local-symbols all-symbols])
(defrecord AllNS [current others])

;; [Utils]
(defn ^:private create-ns [name]
  (fn [^AllNS state]
    (cond (-> state ^NS (.-current) .-name (= name))
          [state nil]

          (-> state .-others (contains? name))
          [state nil]

          :else
          [(update-in state [:others] assoc name (NS. name {} #{} {})) nil])
    ))

(defn ^:private enter-ns [name]
  (fn [^AllNS state]
    (cond (-> state ^NS (.-current) .-name (= name))
          [state nil]

          (-> state .-others (contains? name))
          [(assoc state :current (-> state .-others (get name))) nil]

          :else
          nil)
    ))

;; [Interfaces]
;; Monads
(defn in-ns [name]
  (exec state-maybe-m
    [_ (create-ns name)]
    (enter-ns name)))

(defn refer [^Refer referral]
  (fn [state]
    (-> state
        (update-in [:current :referrals (.-namespace referral)]
                   #(-> (or % referral)
                        (assoc-in [:alias] (.-alias referral))
                        (update-in [:local-symbols] merge (.-local-symbols referral))))
        (update-in [:current :symbols]
                   #(-> %
                        (merge (.-local-symbols referral))
                        (into (let [refer-ns* (name (.-namespace referral))]
                                (for [[sym type] (.-all-symbols referral)] [(symbol refer-ns* (name sym)) type])))
                        (into (if-let [alias (.-alias referral)]
                                (let [refer-ns* (name alias)]
                                  (for [[sym type] (.-all-symbols referral)] [(symbol refer-ns* (name sym)) type]))
                                '())))))))

(defn import [class]
  (let [short-name (last (string/split (name class) #"\."))]
    (fn [state]
      (update-in state [:current]
                 #(-> %
                      (update-in [:imports] conj class)
                      (update-in [:symbols] assoc class 'YOLO short-name 'YOLO))))
    ))

(defn intern [symbol type]
  (if (namespace symbol)
    zero
    (fn [state]
      (update-in state [:current :symbols] assoc symbol type))))

;; Constants
(def +init+ (AllNS. (NS. 'user {} #{} {}) {}))

;; Information I need:
;; + Current namespace.
;; + Current referrals.
;; + Current imports.
;; + Current visible external symbols and ther mapppings.
;; + Current own global symbols.
;; + Current namespace aliases.
;; + List of other namespaces and their relevant data.
