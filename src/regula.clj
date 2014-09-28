(ns regula
  (:refer-clojure :exclude [and or])
  (:require [alt.typed :as t :refer [defalias]]
            [clojure.core.logic :as logic]
            [clojure.core.logic.pldb :as logic-db]
            :reload-all)
  (:import (clojure.lang Keyword)))

;; [Types]
(defalias ValidationError
  Keyword)

(defalias Rule
  [t/Any -> (t/Maybe ValidationError)])

(defalias (RuleSet k)
  (t/Rec [$self]
         (t/Map k (t/Or Rule $self))))

(defalias (Data k)
  (t/Map k t/Any))

(defalias (Report k)
  (t/Map k ValidationError))

;; [Functions]
(t/ann clean (t/All [x] [(RuleSet x) (Data x) -> (Data x)]))
(defn clean [rules data]
  (reduce (fn [cleaned-up [k datum]]
            (if-let [rule (get rules k)]
              (cond (map? rule)
                    (if (map? datum)
                      (assoc cleaned-up k (clean rule datum))
                      cleaned-up)

                    (nil? (rule datum))
                    (assoc cleaned-up k datum)

                    :else
                    cleaned-up)
              cleaned-up))
          (hash-map)
          data))

(t/ann enforce (t/All [x] [(RuleSet x) (Data x) -> (t/Maybe (Report x))]))
(defn enforce [test datum]
  (let [result (reduce (fn [diff [rule-path rule]]
                         (if-let [data (get datum rule-path)]
                           (if (clojure.core/and (map? rule) (map? data))
                             (if-let [message (enforce rule data)]
                               (assoc diff rule-path message)
                               diff)
                             (assoc diff rule-path ::map-expected))
                           (assoc diff rule-path ::missing)))
                       (reduce (fn [total k]
                                 (if (not (contains? test k))
                                   (assoc total k ::not-in-schema)
                                   total))
                               (hash-map)
                               (keys datum))
                       test)]
    (if (not (empty? result))
      result)))

(t/ann and [& Rule -> Rule])
(defn and [& rules]
  (fn [datum]
    (some #(% datum) rules)))

(t/ann or [& Rule -> Rule])
(defn or [& rules]
  (fn [datum]
    (first (for [rule rules
                 :let [error (rule datum)]
                 :when error]
             error))))

(comment
  (time (t/check-ns))
  )
