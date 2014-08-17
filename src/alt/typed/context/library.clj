(ns alt.typed.context.library
  (:require [clojure.set :as set]
            (alt.typed [type :as &type]
                       [util :as &util])))

;; [Methods]
(defn lookup [self type-name]
  (get (::types self) type-name))

(defn save [self type-name type]
  (assert (or (namespace type-name)
              (&util/fully-qualified-class? type-name)))
  (assert (nil? (lookup self type-name)))
  (if (&util/fully-qualified-class? type-name)
    (assoc-in self [::types type-name] type)
    (-> self
        (assoc-in [::types type-name] type)
        (update-in [::ns-mappings (namespace type-name)] set/union #{(name type-name)}))))

;; [Functions]
(let [+defaults+ {::types (hash-map) ::ns-mappings (hash-map)}]
  (defn install [obj]
    (merge obj +defaults+)))
