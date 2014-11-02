(ns system.translator
  (:require [clojure.core.match :refer [match]]
            [system.type :as &type]))

;; Functions
(defn type->code [type]
  ;; (prn 'type->code type)
  (match type
    [::&type/any]
    'Any
    
    [::&type/nothing]
    'Nothing
    
    [::&type/nil]
    nil
    
    [::&type/literal _ ?value]
    (if (symbol? ?value)
      `'~?value
      ?value)
    
    [::&type/object ?class ?params]
    (if (empty? ?params)
      ?class
      `(~?class ~@(map type->code ?params)))
    
    [::&type/union ?types]
    `(~'Or ~@(map type->code ?types))
    
    [::&type/complement ?tyoe]
    `(~'Not ~(type->code ?tyoe))

    [::&type/try ?data ?ex]
    `(~'Try ~(type->code ?data) ~(type->code ?ex))
    
    [::&type/arity ?args ?return]
    `[~@(map type->code ?args) ~'-> ~(type->code ?return)]
    
    [::&type/function ?arities]
    (if (= 1 (count ?arities))
      (type->code (first ?arities))
      `(~'Fn ~@(map type->code ?arities)))
    
    [::&type/all ?vars ?poly]
    `(~'All ~(vec ?vars) ~(type->code ?poly))
    
    (?type-var :guard symbol?)
    ?type-var
    ))
