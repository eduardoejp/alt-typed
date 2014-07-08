(ns alt.typed.context.library
  (:require [clojure.set :as set]
            (alt.typed [type :as &type])))

;; [Protocols]
(defprotocol $Library
  (save [library type-name type])
  (lookup [library type-name]))

;; [Records]
(defrecord Library [_types _ns-mappings]
  $Library
  (save [self type-name type]
    (assert (nil? (get _types type-name)))
    (let [self (assoc-in self [:_types type-name] type)]
      (if-let [ns (namespace type-name)]
        (let [var-name (name type-name)]
          (update-in self [:_ns-mappings ns] set/union #{var-name}))
        self)))
  (lookup [self type-name]
    ;; (prn 'Library/lookup type-name (set (keys _types)))
    (get _types type-name)))

;; [Constants]
(def +new-library+
  (Library. (hash-map) (hash-map)))
