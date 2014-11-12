(ns system.type
  (:refer-clojure :exclude [resolve apply])
  (:require (clojure [set :as set]
                     [template :refer [do-template]])
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [exec
                                            map-m reduce-m
                                            zero return return-all]])))

(declare $or $and apply
         solve)

;; [Data]
(defrecord TypeHeap [counter mappings])
(defrecord Types [db heap class-hierarchy casts members])

;; [Utils]
(defn ^:private defined? [hierarchy class]
  (let [class (symbol "java::class" (name class))]
    (boolean (or (get-in hierarchy [:parents class])
                 (get-in hierarchy [:descendants class])))))

;; [Interface]
;; Constants
(def +falsey+ [::union (list [::nil] [::literal 'java.lang.Boolean false])])
(def +truthy+ [::complement +falsey+])
(def +ambiguous+ [::intersection (list [::complement +truthy+] [::complement +falsey+])])
(def +if-pred+ [::function (list [::arity (list +truthy+) [::literal 'java.lang.Boolean true]]
                                 [::arity (list +falsey+) [::literal 'java.lang.Boolean false]]
                                 [::arity (list +ambiguous+) [::object 'java.lang.Boolean []]])])

(def +init+ (Types. {} (TypeHeap. 0 {}) (make-hierarchy) {} {}))

;; Monads / holes
(def fresh-hole
  (fn [^Types state]
    (let [id (-> state ^TypeHeap (.-heap) .-counter)]
      (list [(update-in state [:heap]
                        #(-> %
                             (update-in [:counter] inc)
                             (assoc-in [:mappings id] [::interval [::any] [::nothing]])))
             [::hole id]]))))

(defn get-hole [hole]
  (match hole
    [::hole ?id]
    (fn [^Types state]
      (let [mappings (-> state ^TypeHeap (.-heap) :mappings)]
        (if (contains? mappings ?id)
          (let [=type (get mappings ?id)]
            (match =type
              [::hole _]
              ((get-hole =type) state)
              
              :else
              (list [state =type])))
          '())))))

(defn narrow-hole [hole top bottom]
  (match hole
    [::hole ?id]
    (exec [interval (get-hole hole)
           :let [[?top ?bottom] (match interval
                                  [::interval ?top ?bottom]
                                  [?top ?bottom])]
           _ (solve ?top top)
           _ (solve bottom ?bottom)]
      (fn [state]
        (list [(assoc-in state [:heap :mappings ?id] [::interval top bottom]) nil])))))

(defn redirect-hole [from to]
  (match [from to]
    [[::hole ?id] [::hole _]]
    (fn [state]
      (list [(assoc-in state [:heap :mappings ?id] to) nil]))))

(defn normalize-hole [hole]
  (match hole
    [::hole ?id]
    (fn [^Types state]
      (if-let [=type (-> state ^TypeHeap (.-heap) .-mappings (get ?id))]
        (match =type
          [::hole _]
          ((normalize-hole =type) state)
          
          :else
          (list [state hole]))
        '()))))

;; Monads / vars
(def fresh-var
  (fn [^Types state]
    (let [id (-> state ^TypeHeap (.-heap) .-counter)]
      (list [(update-in state [:heap]
                        #(-> %
                             (update-in [:counter] inc)
                             (assoc-in [:mappings id] nil)))
             [::var id]]))))

(defn bind-var [type-var type]
  (match type-var
    [::var ?id]
    (fn [^Types state]
      (let [mappings (-> state ^TypeHeap (.-heap) .-mappings)]
        (if (and (contains? mappings ?id)
                 (nil? (get mappings ?id)))
          (list [(assoc-in state [:heap :mappings ?id] type) nil])
          '())))))

(defn rebind-var [type-var type]
  (match type-var
    [::var ?id]
    (fn [^Types state]
      (let [mappings (-> state ^TypeHeap (.-heap) .-mappings)]
        (if (and (contains? mappings ?id)
                 (boolean (get mappings ?id)))
          (list [(assoc-in state [:heap :mappings ?id] type) nil])
          '())))))

(defn bound-var? [type-var]
  (match type-var
    [::var ?id]
    (fn [^Types state]
      (let [mappings (-> state ^TypeHeap (.-heap) :mappings)]
        (if (contains? mappings ?id)
          (list [state (boolean (get mappings ?id))])
          '())))))

(defn deref-var [type-var]
  (match type-var
    [::var ?id]
    (fn [^Types state]
      (let [mappings (-> state ^TypeHeap (.-heap) :mappings)]
        (if-let [=type (get mappings ?id)]
          (list [state =type])
          '())))))

;; Monads / refs
(defn create-ref [type]
  (fn [^Types state]
    (let [id (-> state ^TypeHeap (.-heap) .-counter)]
      (list [(update-in state [:heap]
                        #(-> %
                             (update-in [:counter] inc)
                             (assoc-in [:mappings id] type)))
             [::ref id]]))))

(do-template [<fn> <return>]
  (defn <fn> [ref]
    (match ref
      [::ref ?id]
      (fn [^Types state]
        (let [mappings (-> state ^TypeHeap (.-heap) :mappings)]
          (if (contains? mappings ?id)
            (list <return>)
            '())))))

  get-ref    [state (get mappings ?id)]
  delete-ref [(update-in state [:heap :mappings] dissoc ?id) nil]
  )

(defn set-ref [ref type]
  (match ref
    [::ref ?id]
    (fn [^Types state]
      (let [mappings (-> state ^TypeHeap (.-heap) :mappings)]
        (if (contains? mappings ?id)
          (list [(assoc-in state [:heap :mappings ?id] type) nil])
          '())))))

;; Monads / DB
(defn define-type [type-name type-def]
  (fn [^Types state]
    (when (not (-> state .-db (contains? type-name)))
      (list [(assoc-in state [:db type-name] type-def) nil]))))

(defn resolve [type-name]
  (fn [^Types state]
    (when-let [type (-> state .-db (get type-name))]
      (list [state type]))))

;; Monads / Classes
(defn ^:private qualify-class [class]
  (symbol "java::class" (name class)))

(defn define-class [[class params] parents]
  (&util/try-all [(exec [_ (resolve class)]
                    zero)
                  (exec [:let [=instance (if (empty? params)
                                           [::object class []]
                                           [::all {} params [::object class params]])]
                         _ (define-type class =instance)]
                    (fn [^Types state]
                      (let [class-name (qualify-class class)]
                        (if (not (defined? (.-class-hierarchy state) class-name))
                          (let [hierarchy* (reduce #(derive %1 class-name %2)
                                                   (.-class-hierarchy state)
                                                   (for [[_ class _] parents] (qualify-class class)))]
                            (list [(-> state
                                       (assoc :class-hierarchy hierarchy*)
                                       (assoc-in [:casts class] (into {} (map (fn [[_ p-class p-params]]
                                                                                [p-class [::all {} params [::object p-class p-params]]])
                                                                              parents))))
                                   nil]))
                          '()))
                      ))]))

(defn define-class-members [class all-members]
  (exec [=class (resolve class)
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
    (for [[[name* category*] classes] (.-members state)
          :when (and (= name name*)
                     (= category category*))
          class+type classes]
      [state class+type])))

(defn ^:private super-class? [super sub]
  (fn [^Types state]
    (let [hierarchy (.-class-hierarchy state)]
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
  (match [target-type type]
    [::$fn [::function ?arities]]
    (return type)

    [::$fn [::literal 'clojure.lang.Keyword _]]
    (return [::function (list [::arity (list [::object 'Map []]) [::any]])])

    [::$fn [::literal 'clojure.lang.Symbol _]]
    (return [::function (list [::arity (list [::object 'Map []]) [::any]])])

    [::$fn [::object 'clojure.lang.IPersistentVector [?elem]]]
    (return [::function (list [::arity (list [::object 'java.lang.Long []]) ?elem])])

    [::$fn [::object 'clojure.lang.IPersistentMap [?key ?val]]]
    (return [::function (list [::arity (list ?key) [::union (list [::nil] ?val)]])])

    [::$fn [::object 'clojure.lang.IPersistentSet [?elem]]]
    (return [::function (list [::arity (list ?elem) [::union (list [::nil] ?elem)]])])
    
    [(?target-class :guard symbol?) [::object ?source-class ?params]]
    (if (= ?target-class ?source-class)
      (return type)
      (exec [? (super-class? ?target-class ?source-class)
             _ (if ?
                 (return nil)
                 zero)
             family-line (lineage ?source-class ?target-class)
             ^Types types &util/get-state
             :let [casts (.-casts types)]]
        (reduce-m
         (fn [current next-class]
           (match current
             [::object ?current-class ?params]
             (let [=type-fn (get-in casts [?current-class next-class])]
               (apply =type-fn ?params))))
         type
         family-line)
        ;; (upcast target-type [::object ?target-class []])
        ))
    ))

(defn solve [expected actual]
  (prn 'solve expected actual)
  (match [expected actual]
    [[::var _] _]
    (exec [? (bound-var? expected)]
      (if ?
        (exec [=type (deref-var expected)]
          (solve =type actual))
        (bind-var expected actual)))

    [[::hole ?e-id] [::hole ?a-id]]
    (if (= ?e-id ?a-id)
      (return true)
      (exec [=interval-e (get-hole expected)
             =interval-a (get-hole actual)
             :let [[=top-e =bottom-e] (match =interval-e
                                        [::interval =top =bottom]
                                        [=top =bottom])
                   [=top-a =bottom-a] (match =interval-a
                                        [::interval =top =bottom]
                                        [=top =bottom])]
             _ (solve =top-e =top-a)
             _ (solve =bottom-a =bottom-e)
             _ (redirect-hole expected actual)]
        (return true)))

    [_ [::hole _]]
    (exec [=interval (get-hole actual)
           :let [[=top =bottom] (match =interval
                                  [::interval =top =bottom]
                                  [=top =bottom])]]
      (&util/parallel [(solve expected =top)
                       (exec [_ (solve =top expected)
                              _ (solve expected =bottom)
                              =new-top ($and [expected =top])
                              _ (narrow-hole actual =new-top =bottom)]
                         (return true))]))

    [_ [::ref _]]
    (exec [=type (get-ref actual)]
      (solve expected =type))

    ;; [[::var ?e-id] [::var ?a-id]]
    ;; (if (= ?e-id ?a-id)
    ;;   (return true)
    ;;   (exec
    ;;     [=interval-e (deref-var expected)
    ;;      =interval-a (deref-var actual)
    ;;      :let [[=top-e =bottom-e] (match =interval-e
    ;;                                 [::interval =top =bottom]
    ;;                                 [=top =bottom])
    ;;            [=top-a =bottom-a] (match =interval-a
    ;;                                 [::interval =top =bottom]
    ;;                                 [=top =bottom])]
    ;;      _ (solve =top-e =top-a)
    ;;      _ (solve =bottom-a =bottom-e)
    ;;      _ (update-var expected [::interval =top-a =bottom-a])]
    ;;     (return true)))

    ;; [[::var ?e-id] _]
    ;; (exec
    ;;   [=interval (deref-var expected)
    ;;    :let [[=top =bottom] (match =interval
    ;;                           [::interval =top =bottom]
    ;;                           [=top =bottom])]
    ;;    _ (solve =top actual)
    ;;    _ (solve actual =bottom)
    ;;    _ (update-var expected [::interval actual =bottom])]
    ;;   (return true))
    
    ;; [_ [::var _]]
    ;; (exec
    ;;   [=interval (deref-var actual)
    ;;    :let [[=top =bottom] (match =interval
    ;;                           [::interval =top =bottom]
    ;;                           [=top =bottom])]]
    ;;   (&util/parallel [(solve expected =top)
    ;;                    (exec
    ;;                      [_ (solve =top expected)
    ;;                       _ (solve expected =bottom)
    ;;                       _ (update-var actual [::interval expected =bottom])]
    ;;                      (return true))]))

    [[::any] _]
    (return true)

    [_ [::nothing]]
    (return true)

    [[::nil] [::nil]]
    (return true)

    [[::literal ?e-class ?e-value] [::literal ?a-class ?a-value]]
    (if (and (= ?e-class ?a-class)
             (= ?e-value ?a-value))
      (return true)
      zero)

    [[::object ?class ?params] [::literal ?lit-class ?lit-value]]
    (exec [? (super-class? ?class ?lit-class)]
      (if ?
        (return true)
        zero))

    [[::object ?e-class ?e-params] [::object ?a-class ?a-params]]
    (if (= ?e-class ?a-class)
      (exec [_ (map-m
                (fn [[e a]] (solve e a))
                (map vector ?e-params ?a-params))]
        (return true))
      (exec [=actual (upcast ?e-class actual)]
        (solve expected =actual)))

    [[::tuple ?e-parts] [::tuple ?a-parts]]
    (if (<= (count ?e-parts) (count ?a-parts))
      (exec [_ (map-m
                (fn [[e a]] (solve e a))
                (map vector ?e-parts ?a-parts))]
        (return true))
      zero)

    [[::object ?e-class ?e-params] [::tuple ?a-parts]]
    (exec [=elems (if (empty? ?a-parts)
                    (return [::nothing])
                    ($or ?a-parts))]
      (solve expected [::object 'clojure.lang.IPersistentVector [=elems]]))
    
    [[::object ?e-class ?e-params] [::record ?a-entries]]
    (exec [[=keys =vals] (if (empty? ?a-entries)
                           (return [[::nothing] [::nothing]])
                           (exec [=keys ($or (keys ?a-entries))
                                  =vals ($or (vals ?a-entries))]
                             (return [=keys =vals])))]
      (solve expected [::object 'clojure.lang.IPersistentMap [=keys =vals]]))
    
    [[::record ?e-entries] [::record ?a-entries]]
    (if (set/superset? (set (keys ?e-entries)) (set (keys ?a-entries)))
      (exec [_ (map-m
                (fn [k] (solve (get ?e-entries k) (get ?a-entries k)))
                (keys ?e-entries))]
        (return true))
      zero)

    [[::union ?types] _]
    (exec [=type (return-all ?types)
           _ (solve =type actual)]
      (return true))

    [[::complement ?type] _]
    (fn [state]
      (if (and (empty? ((solve ?type actual) state))
               (empty? ((solve actual ?type) state)))
        (list [state true])
        (zero nil)))

    [[::io] [::io]]
    (return true)

    :else
    zero
    ))

;; Monads / Type-functions
(defn ^:private realize [bindings type]
  (match type
    [::object ?class ?params]
    (exec [=params (map-m (partial realize bindings) ?params)]
      (return [::object ?class (vec =params)]))
    
    [::union ?types]
    (exec [=types (map-m (partial realize bindings) ?types)]
      (return [::union (vec =types)]))

    [::complement ?type]
    (exec [=type (realize bindings ?type)]
      (return [::complement =type]))

    [::function ?arities]
    (exec [=arities (map-m (partial realize bindings) ?arities)]
      (return [::function =arities]))

    [::arity ?args ?return]
    (exec [=args (map-m (partial realize bindings) ?args)
           =return (realize bindings ?return)]
      (return [::arity =args =return]))

    (?token :guard symbol?)
    (if-let [=var (get bindings ?token)]
      (return =var)
      zero)

    [::all ?env ?params ?type-def]
    (return [::all (merge bindings ?env) ?params ?type-def])
    
    :else
    (return type)
    ))

(defn apply [type-fn params]
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
    (exec [=params (map-m (constantly fresh-var) ?params)]
      (apply type =params))
    
    :else
    (return type)))

(defn type-fn? [type]
  (match type
    [::all _ _ _]
    true
    
    :else
    false))

(defn instantiate* [name params]
  (exec [=type-fn (resolve name)]
    (if (type-fn? =type-fn)
      (apply =type-fn params)
      (return =type-fn))))

;; Monads / Types
(do-template [<fn> <tag> <LT-ret> <GT-ret> <LT> <GT>]
  (letfn [(adder [base addition]
            (match [base addition]
              [_ [<tag> ?addition]]
              (reduce-m adder base ?addition)
              
              [[<tag> ?base] _]
              (exec [veredicts (map-m
                                (fn [=base]
                                  (&util/try-all [(exec [_ (solve =base addition)]
                                                    (return <LT>))
                                                  (exec [_ (solve addition =base)]
                                                    (return <GT>))
                                                  (return :peer)]))
                                ?base)]
                (cond (some (partial = :parent) veredicts)
                      (return base)

                      (every? (partial = :peer) veredicts)
                      (return [<tag> (conj ?base addition)])

                      :else
                      (if-let [rem-types (->> (map vector ?base veredicts)
                                              (filter (comp (partial not= :child) second))
                                              (map first)
                                              seq)]
                        (return [<tag> (conj (vec rem-types) addition)])
                        (return addition))))
              
              [_ _]
              (&util/try-all [(exec [_ (solve base addition)]
                                (return <LT-ret>))
                              (exec [_ (solve addition base)]
                                (return <GT-ret>))
                              (return [<tag> [base addition]])])
              ))]
    (defn <fn> [types]
      (match (vec types)
        []
        zero
        
        [type & others]
        (reduce-m adder type others)
        )))

  $or  ::union        base     addition :parent :child
  $and ::intersection addition base     :child  :parent
  )

(let [adder (fn [t1 t2]
              (match [t1 t2]
                [[::eff ?data-1 ?effs-1] [::eff ?data-2 ?effs-2]]
                (exec [=effs (map-m
                              (fn [key]
                                (exec [=merged ($or (filter identity (list (get ?effs-1 key) (get ?effs-2 key))))]
                                  (return [key =merged])))
                              (set/union (set (keys ?effs-1)) (set (keys ?effs-2))))]
                  (return [::eff ?data-2 =effs]))
                
                [[::eff ?data-1 ?effs-1] _]
                (return [::eff t2 ?effs-1])
                
                [_ _]
                (return t2)
                ))]
  (defn sequentially-combine-types [types]
    (match (vec types)
      []
      zero

      [?init & ?others]
      (reduce-m adder ?init ?others))))

(let [adder (fn [t1 t2]
              (match [t1 t2]
                [[::eff ?data-1 ?effs-1] [::eff ?data-2 ?effs-2]]
                (exec [=data ($or [?data-1 ?data-2])
                       =effs (map-m
                              (fn [key]
                                (exec [=merged ($or (filter identity (list (get ?effs-1 key) (get ?effs-2 key))))]
                                  (return [key =merged])))
                              (set/union (set (keys ?effs-1)) (set (keys ?effs-2))))]
                  (return [::eff =data =effs]))
                
                [[::eff ?data-1 ?effs-1] _]
                (exec [=data ($or [?data-1 t2])]
                  (return [::eff =data ?effs-1]))
                
                [_ [::eff ?data-2 ?effs-2]]
                (exec [=data ($or [t1 ?data-2])]
                  (return [::eff =data ?effs-2]))
                
                [_ _]
                ($or [t1 t2])
                ))]
  (defn parallel-combine-types [types]
    (match (vec types)
      []
      zero

      [?init & ?others]
      (reduce-m adder ?init ?others))))
