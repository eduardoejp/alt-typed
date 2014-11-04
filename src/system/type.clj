(ns system.type
  (:refer-clojure :exclude [resolve])
  (:require (clojure [set :as set]
                     [template :refer [do-template]])
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]])))

;; [Data]
(defrecord TypeVars [counter mappings])
(defrecord BoundTypes [counter mappings])
(defrecord Types [db vars bound class-hierarchy])

;; [Utils]
(defn ^:private defined? [hierarchy class]
  (let [class (symbol "java::class" (name class))]
    (boolean (or (get-in hierarchy [:parents class])
                 (get-in hierarchy [:descendants class])))))

;; [Interface]
;; Constants
(def +falsey+ [::union (list [::nil] [::literal 'java.lang.Boolean false])])
(def +truthy+ [::complement +falsey+])

(def +init+ (Types. {} (TypeVars. 0 {}) (BoundTypes. 0 {}) (make-hierarchy)))

;; Monads / vars
(def fresh-var
  (fn [^Types state]
    (let [id (-> state ^TypeVars (.-vars) .-counter)]
      (list [(-> state
                 (update-in [:vars :counter] inc)
                 (assoc-in [:vars :mappings id] (vector [::any] [::nothing])))
             [::var id]]))))

(defn deref-var [type-var]
  (match type-var
    [::var ?id]
    (fn [^Types state]
      (when-let [top+bottom (-> state ^TypeVars (.-vars) .-mappings (get ?id))]
        (list [state top+bottom])))))

(defn deref-binding [binding]
  (match binding
    [::bound ?id]
    (fn [^Types state]
      ;; (prn 'deref-binding binding state)
      (when-let [=type (-> state ^BoundTypes (.-bound) .-mappings (get ?id))]
        (list [state =type])))))

(defn update-var [type-var top bottom]
  (match type-var
    [::var ?id]
    (fn [^Types state]
      (if (-> state ^TypeVars (.-vars) .-mappings (get ?id))
        (list [(assoc-in state [:vars :mappings ?id] [top bottom]) nil])))
    ))

(defn update-binding [binding type]
  (match binding
    [::bound ?id]
    (fn [state]
      (list [(assoc-in state [:bound :mappings ?id] type) nil]))))

;; Monads / bound type-vars
(defn bind [type]
  (fn [^Types state]
    (let [id (-> state ^BoundTypes (.-bound) .-counter)]
      (list [(-> state
                 (update-in [:bound :counter] inc)
                 (assoc-in [:bound :mappings id] type))
             [::bound id]]))))

(defn unbind [id]
  (fn [^Types state]
    (list [(update-in state [:bound :mappings] dissoc id) nil])))

;; Monads / DB
(defn define-type [type-name type-def]
  (fn [^Types state]
    (when (not (-> state .-db (contains? type-name)))
      (list [(assoc-in state [:db type-name] type-def) nil]))))

(defn resolve [type-name]
  (fn [^Types state]
    ;; (prn `resolve type-name state)
    (when-let [type (or (-> state .-db (get type-name))
                        [::object type-name []])]
      (list [state type]))))

;; Monads / Classes
(let [qualify-class #(symbol "java::class" (name %))]
 (defn define-class [class parents]
  (fn [^Types state]
    (prn 'define-class class parents (.-class-hierarchy state))
    ;; (prn '(defined? (.-class-hierarchy state) (nth class 0)) (defined? (.-class-hierarchy state) (nth class 0)))
    (when (not (defined? (.-class-hierarchy state) (nth class 0)))
      (let [class-name (qualify-class (nth class 0))
            ;; _ (prn 'parents parents '(map first parents) (map first parents))
            hierarchy* (reduce #(derive %1 class-name %2)
                               (.-class-hierarchy state)
                               (map (comp qualify-class first) parents))]
        ;; (prn '(.-class-hierarchy state) (.-class-hierarchy state))
        (prn 'hierarchy* (mapv (comp qualify-class first) parents) hierarchy*)
        (list [(assoc state :class-hierarchy hierarchy*) nil])
        ))
    )))

(defn super-class? [super sub]
  ;; (prn 'super-class? super sub)
  (fn [^Types state]
    ;; (prn 'super-class?/state state)
    (let [hierarchy (.-class-hierarchy state)]
      ;; (prn 'super-class?
      ;;      (defined? hierarchy super)
      ;;      (defined? hierarchy sub)
      ;;      (isa? hierarchy (symbol "java::class" (name super)) (symbol "java::class" (name sub)))
      ;;      hierarchy)
      (list [state (or (and (defined? hierarchy super)
                            (defined? hierarchy sub)
                            (isa? hierarchy (symbol "java::class" (name super)) (symbol "java::class" (name sub))))
                       (or (= super sub)
                           (= super 'java.lang.Object)))]))))

;; Monads / Solving
(defn solve [expected actual]
  (prn 'solve expected actual)
  (match [expected actual]
    [_ [::bound _]]
    (exec state-seq-m
      [=type (deref-binding actual)
       _ (solve expected =type)]
      (return state-seq-m true))

    [_ [::var _]]
    (exec state-seq-m
      [[=top =bottom] (deref-var actual)
       _ (&util/parallel [(solve expected =top)
                          (exec state-seq-m
                            [_ (solve =top expected)
                             _ (update-var actual expected =bottom)]
                            (return state-seq-m true))])]
      (return state-seq-m true))

    [[::any] _]
    (return state-seq-m true)

    [_ [::nothing]]
    (return state-seq-m true)

    [[::nil] [::nil]]
    (return state-seq-m true)

    [[::literal ?e-class ?e-value] [::literal ?a-class ?a-value]]
    (do ;; (prn '[[::literal _ _] [::literal _ _]] [expected actual]
        ;;      `(~'= ~?e-class ~?a-class) (.equals ?e-class ?a-class)
        ;;      `(~'= ~?e-value ~?a-value) (= ?e-value ?a-value)
        ;;      (and (= ?e-class ?a-class)
        ;;           (= ?e-value ?a-value)))
        (if (and (= ?e-class ?a-class)
                 (= ?e-value ?a-value))
          (return state-seq-m true)
          zero))

    [[::object ?class ?params] [::literal ?lit-class ?lit-value]]
    (exec state-seq-m
      [? (super-class? ?class ?lit-class)]
      (if ?
        (return state-seq-m true)
        zero))

    [[::object ?e-class ?e-params] [::object ?a-class ?a-params]]
    (do (prn [::object ?e-class ?e-params] [::object ?a-class ?a-params])
      (if (= ?e-class ?a-class)
        (exec state-seq-m
          [_ (map-m state-seq-m
                    (fn [[e a]] (solve e a))
                    (map vector ?e-params ?a-params))]
          (return state-seq-m true))
        zero))

    [[::union ?types] _]
    (exec state-seq-m
      [=type (return-all ?types)
       _ (solve =type actual)]
      (return state-seq-m true))

    [[::complement ?type] _]
    (fn [state]
      ;; (prn '[[::complement ?type] actual]
      ;;      [[::complement ?type] actual]
      ;;      (count ((solve ?type actual) state)))
      (let [;; results-1 ((solve ?type actual) state)
            ;; results-2 ((solve actual ?type) state)
            ]
        ;; (prn '[[:complement ?type] _] 'results results)
        (if (and (empty? ((solve ?type actual) state))
                 (empty? ((solve actual ?type) state)))
          (list [state true])
          (zero nil))))

    [[::io] [::io]]
    (return state-seq-m true)

    :else
    zero
    ))

;; Monads / Type-functions
(defn ^:private realize [bindings type]
  (match type
    [::object ?class ?params]
    (return state-seq-m [::object ?class (map realize ?params)])
    
    [::union ?types]
    (return state-seq-m [::union (map realize ?types)])

    [::complement ?type]
    (return state-seq-m [::complement (realize ?type)])

    (?token :guard symbol?)
    (if-let [=var (get bindings ?token)]
      =var
      zero)
    
    :else
    (return state-seq-m type)
    ))

(defn fn-call [type-fn params]
  (match type-fn
    [::all ?params ?type-def]
    (when (= (count ?params) (count params))
      (exec state-seq-m
        [=vars (map-m state-seq-m (fn [_] fresh-var) ?params)
         :let [pairs (map vector =vars params)]
         _ (map-m state-seq-m (fn [[=var =input]] (solve =var =input)) pairs)]
        (realize (into {} pairs) ?type-def)))
    :else
    zero))

;; Monads / Types
(do-template [<fn> <tag> <LT-ret> <GT-ret> <LT> <GT>]
  (letfn [(adder [base addition]
            (match [base addition]
              [_ [<tag> ?addition]]
              (reduce-m state-seq-m adder base ?addition)
              
              [[<tag> ?base] _]
              (exec state-seq-m
                [veredicts (map-m state-seq-m
                                  (fn [=base]
                                    (&util/parallel [(exec state-seq-m
                                                       [_ (solve =base addition)]
                                                       (return state-seq-m <LT>))
                                                     (exec state-seq-m
                                                       [_ (solve addition =base)]
                                                       (return state-seq-m <GT>))
                                                     (return state-seq-m :peer)]))
                                  ?base)]
                (cond (some (partial = :parent) veredicts)
                      (return state-seq-m base)

                      (every? (partial = :peer) veredicts)
                      (return state-seq-m [<tag> (conj ?base addition)])

                      :else
                      (if-let [rem-types (->> (map vector ?base veredicts)
                                              (filter (comp (partial not= :child) second))
                                              (map first)
                                              seq)]
                        (return state-seq-m [<tag> (conj (vec rem-types) addition)])
                        (return state-seq-m addition))))
              
              [_ _]
              (&util/parallel [(exec state-seq-m
                                 [_ (solve base addition)]
                                 (return state-seq-m <LT-ret>))
                               (exec state-seq-m
                                 [_ (solve addition base)]
                                 (return state-seq-m <GT-ret>))
                               (return state-seq-m [<tag> [base addition]])])
              ))]
    (defn <fn> [types]
      (match (vec types)
        []
        zero
        
        [type & others]
        (reduce-m state-seq-m adder type others)
        )))

  $or  ::union        base     addition :parent :child
  $and ::intersection addition base     :child  :parent
  )

(let [adder (fn [t1 t2]
              (match [t1 t2]
                [[::eff ?data-1 ?effs-1] [::eff ?data-2 ?effs-2]]
                (exec state-seq-m
                  [=effs (map-m state-seq-m
                                (fn [key]
                                  (exec state-seq-m
                                    [=merged ($or (filter identity (list (get ?effs-1 key) (get ?effs-2 key))))]
                                    (return state-seq-m [key =merged])))
                                (set/union (set (keys ?effs-1)) (set (keys ?effs-2))))]
                  (return state-seq-m [::eff ?data-2 =effs]))
                
                [[::eff ?data-1 ?effs-1] _]
                (return state-seq-m [::eff t2 ?effs-1])
                
                [_ _]
                (return state-seq-m t2)
                ))]
  (defn sequentially-combine-types [types]
    (match (vec types)
      []
      zero

      [?init & ?others]
      (reduce-m state-seq-m adder ?init ?others))))

(let [adder (fn [t1 t2]
              (match [t1 t2]
                [[::eff ?data-1 ?effs-1] [::eff ?data-2 ?effs-2]]
                (exec state-seq-m
                  [=data ($or [?data-1 ?data-2])
                   =effs (map-m state-seq-m
                                (fn [key]
                                  (exec state-seq-m
                                    [=merged ($or (filter identity (list (get ?effs-1 key) (get ?effs-2 key))))]
                                    (return state-seq-m [key =merged])))
                                (set/union (set (keys ?effs-1)) (set (keys ?effs-2))))]
                  (return state-seq-m [::eff =data =effs]))
                
                [[::eff ?data-1 ?effs-1] _]
                (exec state-seq-m
                  [=data ($or [?data-1 t2])]
                  (return state-seq-m [::eff =data ?effs-1]))
                
                [_ [::eff ?data-2 ?effs-2]]
                (exec state-seq-m
                  [=data ($or [t1 ?data-2])]
                  (return state-seq-m [::eff =data ?effs-2]))
                
                [_ _]
                ($or [t1 t2])
                ))]
  (defn parallel-combine-types [types]
    (match (vec types)
      []
      zero

      [?init & ?others]
      (reduce-m state-seq-m adder ?init ?others))))

;; (Or String Number) Long = (Or String Number)
;; (And String Number) Long = (And String Long)

;; (Or String Number) Any = Any
;; (And String Number) Any = (And String Long)

;; (Or String Number) Nothing = (Or String Number)
;; (And String Number) Nothing = Nothing
