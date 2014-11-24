(ns system.translator
  (:require [clojure.core.match :refer [match]]
            [system.util :as &util]
            [system.type :as &type]))

;; Functions
(defn rec-name [type]
  (match type
    [::&type/object ?class ?params]
    (some rec-name ?params)
    
    [::&type/union ?types]
    (some rec-name ?types)
    
    [::&type/intersection ?types]
    (some rec-name ?types)
    
    [::&type/complement ?type]
    (rec-name ?type)

    [::&type/eff ?data ?effects]
    (or (rec-name ?data)
        (if-let [try* (:try ?effects)]
          (rec-name try*)))
    
    [::&type/array ?type]
    (rec-name ?type)
    
    [::&type/tuple ?elems]
    (some rec-name ?elems)
    
    [::&type/record ?entries]
    (some rec-name (vals ?entries))
    
    [::&type/arity ?args ?return]
    (or (some rec-name ?args)
        (rec-name ?return))
    
    [::&type/function ?arities]
    (some rec-name ?arities)

    [::&type/multi-fn ?dispatch-fn ?methods]
    (or (some rec-name ?methods)
        (rec-name ?dispatch-fn))
    
    [::&type/all ?env ?vars ?poly]
    (or (some rec-name (map second ?vars))
        (rec-name ?poly))

    [::&type/alias ?name ?type-def]
    (rec-name ?type-def)
    
    [::&type/rec-call [::&type/rec ?name ?def] ?env ?params]
    [?name (count ?params)]

    _
    nil))

(defn type->code* [type]
  ;; (prn 'type->code* type)
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
      `(~?class ~@(map type->code* ?params)))
    
    [::&type/union ?types]
    `(~'Or ~@(map type->code* ?types))

    [::&type/intersection ?types]
    `(~'And ~@(map type->code* ?types))
    
    [::&type/complement ?tyoe]
    `(~'Not ~(type->code* ?tyoe))

    [::&type/eff ?data ?effects]
    `(~'Eff ~(type->code* ?data) ~(into {} (for [[k e] ?effects] [k (type->code* e)])))

    [::&type/io]
    'IO

    [::&type/macro]
    'Macro

    [::&type/array ?type]
    `(~'Array ~(type->code* ?type))

    [::&type/tuple ?elems]
    `'~(mapv type->code* ?elems)

    [::&type/record ?entries]
    `'~(into {} (for [[k v] ?entries] [(type->code* k) (type->code* v)]))
    
    [::&type/arity ?args ?return]
    `[~@(map type->code* ?args) ~'-> ~(type->code* ?return)]
    
    [::&type/function ?arities]
    `(~'Fn ~@(map type->code* ?arities))

    [::&type/multi-fn ?dispatch-fn ?methods]
    `(~'MultiFn ~(type->code* ?dispatch-fn) ~'=>
                ~@(map type->code* ?methods))
    
    [::&type/all ?env ?vars ?poly]
    (let [vars* (mapv #(match %
                         [(?name :guard symbol?) ?top]
                         (if (= [::&type/any] ?top)
                           ?name
                           [?name '< (type->code* ?top)]))
                      ?vars)]
      `(~'All ~vars* ~(type->code* ?poly)))

    [::&type/alias ?name ?type-def]
    ?name
    
    (?type-var :guard symbol?)
    ?type-var

    [::&type/rec-call [::&type/rec ?name ?def] ?env ?params]
    `(~?name ~@(map type->code* ?params))

    [::&type/protocol ?name ?methods]
    `(~'Protocol ~?name ~(into {} (map (fn [[name type]] [name (type->code* type)])
                                       ?methods)))

    [::&type/reify ?impls]
    `(~'Reify ~(into {} (map (fn [[context members]]
                               [context (into {} (map (fn [[name type]] [name (type->code* type)]) members))])
                             ?impls)))
    ))

(let [+var-names+ (for [idx (iterate inc 1)
                        alphabet "abcdefghijklmnopqrstuvwxyz"]
                    (if (= 1 idx)
                      (symbol (str alphabet))
                      (symbol (str alphabet idx))))]
  (defn type->code [type]
    ;; (prn 'type->code* type)
    (let [inner-type (type->code* type)]
      (if-let [[rec-name args-count] (rec-name type)]
        `(~'Rec [~rec-name]
                (~'All ~(vec (take args-count +var-names+))
                       ~inner-type))
        inner-type))))
