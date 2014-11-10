(ns system.type
  (:refer-clojure :exclude [resolve apply])
  (:require (clojure [set :as set]
                     [template :refer [do-template]])
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]])))

(declare $or $and apply)

;; [Data]
(defrecord TypeVars [counter mappings])
(defrecord BoundTypes [counter mappings])
(defrecord Types [db vars bound class-hierarchy casts members])

;; [Utils]
(defn ^:private defined? [hierarchy class]
  (let [class (symbol "java::class" (name class))]
    (boolean (or (get-in hierarchy [:parents class])
                 (get-in hierarchy [:descendants class])))))

;; [Interface]
;; Constants
(def +falsey+ [::union (list [::nil] [::literal 'java.lang.Boolean false])])
(def +truthy+ [::complement +falsey+])

(def +init+ (Types. {} (TypeVars. 0 {}) (BoundTypes. 0 {}) (make-hierarchy) {} {}))

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
    (prn `resolve type-name state)
    (when-let [type (-> state .-db (get type-name))]
      (list [state type]))))

;; Monads / Classes
(defn ^:private qualify-class [class]
  (symbol "java::class" (name class)))

(defn define-class [[class params] parents]
  (&util/parallel [(exec state-seq-m
                     [_ (resolve class)]
                     zero)
                   (exec state-seq-m
                     [:let [=instance (if (empty? params)
                                        [::object class []]
                                        [::all {} params [::object class params]])]
                      _ (define-type class =instance)]
                     (fn [^Types state]
                       ;; (prn '(defined? (.-class-hierarchy state) (nth class 0)) (defined? (.-class-hierarchy state) (nth class 0)))
                       (let [class-name (qualify-class class)]
                         ;; (prn 'define-class class-name (defined? (.-class-hierarchy state) class-name) (.-class-hierarchy state))
                         (if (not (defined? (.-class-hierarchy state) class-name))
                           (let [;; _ (prn 'parents parents '(map first parents) (map first parents))
                                 hierarchy* (reduce #(derive %1 class-name %2)
                                                    (.-class-hierarchy state)
                                                    (for [[_ class _] parents] (qualify-class class)))]
                             ;; (prn '(.-class-hierarchy state) (.-class-hierarchy state))
                             ;; (prn 'hierarchy* (mapv (comp qualify-class first) parents) hierarchy*)
                             (list [(-> state
                                        (assoc :class-hierarchy hierarchy*)
                                        (assoc-in [:casts class] (into {} (map (fn [[_ p-class p-params]]
                                                                                 [p-class [::all {} params [::object p-class p-params]]])
                                                                               parents))))
                                    nil]))
                           '()))
                       ))]))

(defn define-class-members [class all-members]
  ;; members {decode {:static-methods {java.lang.Long [java.lang.String -> java.lang.Long]}}}
  (exec state-seq-m
    [=class (resolve class)
     :let [wrap (match =class
                  [::object _ _]
                  (fn [=type]
                    [::function (list [::arity [=class] =type])])
                  
                  [::all ?env ?params ?instance-type]
                  (fn [=type]
                    [::all ?env ?params
                     [::function (list [::arity [?instance-type] =type])]])
                  )]]
    (fn [^Types state]
      (list [(update-in state [:members]
                        (fn [members]
                          (reduce (fn [members [category entries]]
                                    (if (= :ctor category)
                                      (assoc-in members [[class category] class] entries)
                                      (reduce (fn [members [name =type]]
                                                (assoc-in members [[name category] class] (if (or (= :static-fields category)
                                                                                                  (= :static-methods category))
                                                                                            =type
                                                                                            (wrap =type))))
                                              members entries)))
                                  members all-members)))
             nil])
      )))

(defn member-candidates [[name category]]
  (fn [^Types state]
    (prn 'member-candidates [name category] (.-members state))
    (for [[[name* category*] classes] (.-members state)
          :when (and (= name name*)
                     (= category category*))
          class+type classes]
      [state class+type])))

(defn ^:private super-class? [super sub]
  (fn [^Types state]
    ;; (prn 'super-class?/state state)
    (let [hierarchy (.-class-hierarchy state)]
      ;; (prn 'super-class?
      ;;      (defined? hierarchy super)
      ;;      (defined? hierarchy sub)
      ;;      (isa? hierarchy (symbol "java::class" (name super)) (symbol "java::class" (name sub)))
      ;;      hierarchy)
      ;; (prn 'super-class?
      ;;      super (defined? hierarchy super)
      ;;      sub (defined? hierarchy sub)
      ;;      [(qualify-class sub) (qualify-class super)]
      ;;      (isa? hierarchy (qualify-class sub) (qualify-class super))
      ;;      hierarchy)
      ;; (prn 'super-class? (and (defined? hierarchy super)
      ;;                         (defined? hierarchy sub)
      ;;                         (isa? hierarchy (qualify-class super) (qualify-class sub))))
      (list [state (and (defined? hierarchy super)
                        (defined? hierarchy sub)
                        (isa? hierarchy (qualify-class sub) (qualify-class super)))]))))

(defn ^:private lineage* [hierarchy from to]
  (for [parent (get-in hierarchy [:parents from])
        member (cond (= to parent)
                     (list parent)
                     
                     (get-in hierarchy [:ancestors parent to])
                     (cons parent (lineage* parent to))
                     
                     :else
                     '())]
    member))

(defn ^:private lineage [from to]
  (let [from* (qualify-class from)
        to* (qualify-class to)]
    (fn [^Types state]
      (list [state (mapv (comp symbol name)
                         (lineage* (.-class-hierarchy state) (qualify-class from) (qualify-class to)))]))
    ))

;; Monads / Solving
(defn upcast [target-type type]
  ;; (prn 'upcast target-type type)
  (match [target-type type]
    [::$fn [::function ?arities]]
    (return state-seq-m type)

    [::$fn [::literal 'clojure.lang.Keyword _]]
    (return state-seq-m [::function (list [::arity (list [::object 'Map []]) [::any]])])

    [::$fn [::literal 'clojure.lang.Symbol _]]
    (return state-seq-m [::function (list [::arity (list [::object 'Map []]) [::any]])])

    [::$fn [::object 'clojure.lang.IPersistentVector [?elem]]]
    (return state-seq-m [::function (list [::arity (list [::object 'java.lang.Long []]) ?elem])])

    [::$fn [::object 'clojure.lang.IPersistentMap [?key ?val]]]
    (return state-seq-m [::function (list [::arity (list ?key) [::union (list [::nil] ?val)]])])

    [::$fn [::object 'clojure.lang.IPersistentSet [?elem]]]
    (return state-seq-m [::function (list [::arity (list ?elem) [::union (list [::nil] ?elem)]])])
    
    [(?target-class :guard symbol?) [::object ?source-class ?params]]
    (if (= ?target-class ?source-class)
      (return state-seq-m type)
      (exec state-seq-m
        [? (super-class? ?target-class ?source-class)
         ;; :let [_ (prn 'upcast/? ?)]
         _ (if ?
             (return state-seq-m nil)
             zero)
         family-line (lineage ?source-class ?target-class)
         :let [;; matches (map vector
               ;;              (cons ?source-class family-line)
               ;;              family-line)
               ;; _ (prn 'family-line family-line)
               ;; _ (prn 'matches matches)
               ]
         ^Types types &util/get-state
         :let [casts (.-casts types)
               ;; _ (prn 'casts casts)
               ]]
        (reduce-m state-seq-m
                  (fn [current next-class]
                    (match current
                      [::object ?current-class ?params]
                      (let [;; _ (prn `(~'get-in ~'casts [~?current-class ~next-class]) (get-in casts [?current-class next-class]))
                            ;; _ (prn `(~'get-in ~'casts [~?current-class]) (get-in casts [?current-class]))
                            =type-fn (get-in casts [?current-class next-class])]
                        (apply =type-fn ?params))))
                  type
                  family-line)
        ;; (upcast target-type [::object ?target-class []])
        ))
    ))

(defn solve [expected actual]
  (prn 'solve expected actual)
  (match [expected actual]
    [_ [::bound _]]
    (exec state-seq-m
      [=type (deref-binding actual)
       _ (solve expected =type)]
      (return state-seq-m true))

    [[::var ?e-id] [::var ?a-id]]
    (if (= ?e-id ?a-id)
      (return state-seq-m true)
      (exec state-seq-m
        [[=top-e =bottom-e] (deref-var expected)
         [=top-a =bottom-a] (deref-var actual)
         _ (solve =top-e =top-a)
         _ (solve =bottom-a =bottom-e)
         _ (update-var expected =top-a =bottom-a)]
        (return state-seq-m true)))
    
    [[::var ?e-id] _]
    (exec state-seq-m
      [[=top =bottom] (deref-var expected)
       _ (exec state-seq-m
           [_ (solve =top actual)
            _ (update-var expected actual =bottom)]
           (return state-seq-m true))]
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
      [? (super-class? ?class ?lit-class)
       ;; :let [_ (prn "Object vs literal:" ?class ?lit-class ?)]
       ;; _ (fn [state]
       ;;     (prn '? ? 'state state)
       ;;     (list [state nil]))
       ]
      (if ?
        (return state-seq-m true)
        zero))

    [[::object ?e-class ?e-params] [::object ?a-class ?a-params]]
    (do ;; (prn [::object ?e-class ?e-params] [::object ?a-class ?a-params])
        (if (= ?e-class ?a-class)
          (exec state-seq-m
            [_ (map-m state-seq-m
                      (fn [[e a]] (solve e a))
                      (map vector ?e-params ?a-params))]
            (return state-seq-m true))
          (exec state-seq-m
            [=actual (upcast ?e-class actual)]
            (solve expected =actual))))

    [[::tuple ?e-parts] [::tuple ?a-parts]]
    (if (<= (count ?e-parts) (count ?a-parts))
      (exec state-seq-m
        [_ (map-m state-seq-m
                  (fn [[e a]] (solve e a))
                  (map vector ?e-parts ?a-parts))]
        (return state-seq-m true))
      zero)

    [[::object ?e-class ?e-params] [::tuple ?a-parts]]
    (exec state-seq-m
      [=elems (if (empty? ?a-parts)
                (return state-seq-m [::nothing])
                ($or ?a-parts))]
      (solve expected [::object 'clojure.lang.IPersistentVector [=elems]]))
    
    [[::object ?e-class ?e-params] [::record ?a-entries]]
    (exec state-seq-m
      [[=keys =vals] (if (empty? ?a-entries)
                       (return state-seq-m [[::nothing] [::nothing]])
                       (exec state-seq-m
                         [=keys ($or (keys ?a-entries))
                          =vals ($or (vals ?a-entries))]
                         (return state-seq-m [=keys =vals])))]
      (solve expected [::object 'clojure.lang.IPersistentMap [=keys =vals]]))
    
    [[::record ?e-entries] [::record ?a-entries]]
    (if (set/superset? (set (keys ?e-entries)) (set (keys ?a-entries)))
      (exec state-seq-m
        [_ (map-m state-seq-m
                  (fn [k] (solve (get ?e-entries k) (get ?a-entries k)))
                  (keys ?e-entries))]
        (return state-seq-m true))
      zero)

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
    (exec state-seq-m
      [=params (map-m state-seq-m (partial realize bindings) ?params)]
      (return state-seq-m [::object ?class (vec =params)]))
    
    [::union ?types]
    (exec state-seq-m
      [=types (map-m state-seq-m (partial realize bindings) ?types)]
      (return state-seq-m [::union (vec =types)]))

    [::complement ?type]
    (exec state-seq-m
      [=type (realize bindings ?type)]
      (return state-seq-m [::complement =type]))

    [::function ?arities]
    (exec state-seq-m
      [=arities (map-m state-seq-m (partial realize bindings) ?arities)]
      (return state-seq-m [::function =arities]))

    [::arity ?args ?return]
    (exec state-seq-m
      [=args (map-m state-seq-m (partial realize bindings) ?args)
       =return (realize bindings ?return)]
      (return state-seq-m [::arity =args =return]))

    (?token :guard symbol?)
    (if-let [=var (get bindings ?token)]
      (return state-seq-m =var)
      zero)

    [::all ?env ?params ?type-def]
    (return state-seq-m [::all (merge bindings ?env) ?params ?type-def])
    
    :else
    (return state-seq-m type)
    ))

(defn apply [type-fn params]
  ;; (prn 'apply type-fn params)
  (match type-fn
    [::all ?env ?params ?type-def]
    (if (= (count ?params) (count params))
      (realize (into ?env (map vector ?params params))
               ?type-def)
      zero)
    
    :else
    zero))

(defn instantiate [type]
  (match type
    [::all _ ?params _]
    (exec state-seq-m
      [=params (map-m state-seq-m (constantly fresh-var) ?params)]
      (apply type =params))
    
    :else
    (return state-seq-m type)))

(defn type-fn? [type]
  (match type
    [::all _ _ _]
    true
    
    :else
    false))

(defn instantiate* [name params]
  (prn 'instantiate* name params)
  (exec state-seq-m
    [=type-fn (resolve name)
     :let [_ (prn '=type-fn)]
     ]
    (if (type-fn? =type-fn)
      (apply =type-fn params)
      (return state-seq-m =type-fn))))

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
