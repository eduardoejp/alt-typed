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
(defrecord Types [db heap class-hierarchy class-categories casts members])

;; [Utils]
(defn ^:private defined? [hierarchy class]
  (let [class (symbol "java::class" (name class))]
    (boolean (or (get-in hierarchy [:parents class])
                 (get-in hierarchy [:descendants class])))))

;; [Interface]
;; Constants
(def +falsey+ [::union (list [::nil] [::literal 'java.lang.Boolean false])])
(def +truthy+ [::complement +falsey+])
(def +ambiguous+ [::any])

(def +init+ (Types. {} (TypeHeap. 0 {}) (make-hierarchy) {} {} {}))

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
  ;; (prn 'get-hole/_1 hole)
  (match hole
    [::hole ?id]
    (fn [^Types state]
      ;; (prn 'get-hole/_1 state)
      (let [mappings (-> state ^TypeHeap (.-heap) :mappings)]
        (if (contains? mappings ?id)
          (let [=type (get mappings ?id)]
            (match =type
              [::interval ?top ?bottom]
              (list [state [?top ?bottom]])
              
              [::hole _]
              ((get-hole =type) state)))
          '())))))

(defn narrow-hole [hole top bottom]
  (match hole
    [::hole ?id]
    (fn [state]
      (list [(assoc-in state [:heap :mappings ?id] [::interval top bottom]) nil]))
    ;; (exec [[?top ?bottom] (get-hole hole)
    ;;        _ (solve ?top top)
    ;;        _ (solve bottom ?bottom)]
    ;;   (fn [state]
    ;;     (list [(assoc-in state [:heap :mappings ?id] [::interval top bottom]) nil])))
    ))

(defn redirect-hole [from to]
  (match [from to]
    [[::hole ?id] [::hole _]]
    (fn [state]
      (list [(assoc-in state [:heap :mappings ?id] to) nil]))))

(defn normalize-hole [hole]
  ;; (prn 'normalize-hole/_1 hole)
  (match hole
    [::hole ?id]
    (fn [^Types state]
      ;; (prn 'normalize-hole/_1 state)
      (if-let [=type (-> state ^TypeHeap (.-heap) .-mappings (get ?id))]
        (match =type
          [::hole _]
          ((normalize-hole =type) state)
          
          :else
          (list [state hole]))
        '()))))

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

(defn define-class [[class params full-params] parents]
  (&util/try-all [(exec [_ (resolve class)]
                    zero)
                  (exec [:let [=instance (if (empty? params)
                                           [::object class []]
                                           [::all {} full-params [::object class params]])]
                         _ (define-type class =instance)]
                    (fn [^Types state]
                      (let [class-name (qualify-class class)]
                        (if (not (defined? (.-class-hierarchy state) class-name))
                          (let [hierarchy* (reduce #(derive %1 class-name %2)
                                                   (.-class-hierarchy state)
                                                   (for [[_ class _] parents] (qualify-class class)))]
                            (list [(-> state
                                       (assoc :class-hierarchy hierarchy*)
                                       (assoc-in [:class-categories class] :class)
                                       (assoc-in [:casts class] (into {} (map (fn [[_ p-class p-params]]
                                                                                [p-class [::all {} full-params [::object p-class p-params]]])
                                                                              parents))))
                                   nil]))
                          '()))
                      ))]))

(defn interface? [class]
  (fn [state]
    (if (= :interface (get-in state [:class-categories class]))
      (list [state true])
      '())))

(defn class-defined? [class]
  (fn [^Types state]
    (if (-> state .-class-categories (contains? class))
      (list [state true])
      (list [state false]))))

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

    [::$fn [::multi-fn _ ?arities]]
    (return [::function ?arities])

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
    [[::hole ?e-id] [::hole ?a-id]]
    (if (= ?e-id ?a-id)
      (return true)
      (exec [[=top =bottom] (get-hole expected)
             _ (solve =top actual)
             _ (solve actual =bottom)
             _ (redirect-hole expected actual)]
        (return true)))
    ;; (if (= ?e-id ?a-id)
    ;;   (return true)
    ;;   (exec [[=top-e =bottom-e] (get-hole expected)
    ;;          :let [_ (prn 'expected =top-e =bottom-e)]
    ;;          [=top-a =bottom-a] (get-hole actual)
    ;;          :let [_ (prn 'actual =top-a =bottom-a)]
    ;;          _ (solve =top-e =top-a)
    ;;          :let [_ (println "Top fits!")]
    ;;          _ (solve =bottom-a =bottom-e)
    ;;          :let [_ (println "Bottom fits!")]
    ;;          _ (redirect-hole expected actual)]
    ;;     (return true)))

    [_ [::hole _]]
    (exec [[=top =bottom] (get-hole actual)
           :when (not= [::nothing] expected)
           =new-top ($and expected =top)
           ;; :let [_ (prn '=new-top =top expected =new-top)]
           ;; :when (not= [::nothing] =new-top)
           _ (solve =new-top =bottom)
           _ (narrow-hole actual =new-top =bottom)]
      (return true))

    [[::hole _] _]
    (exec [[=top =bottom] (get-hole expected)
           :when (not= [::any] actual)
           =new-bottom ($or actual =bottom)
           ;; :let [_ (prn '=new-bottom =bottom actual =new-bottom)]
           _ (solve =top =new-bottom)
           _ (narrow-hole expected =top =new-bottom)]
      (return true))

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
      (exec [_ (map-m (fn [[e a]] (solve e a))
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
    (exec [=elems (reduce-m $or [::nothing] ?a-parts)]
      (solve expected [::object 'clojure.lang.IPersistentVector [=elems]]))
    
    [[::object ?e-class ?e-params] [::record ?a-entries]]
    (exec [[=keys =vals] (if (empty? ?a-entries)
                           (return [[::nothing] [::nothing]])
                           (exec [=keys (reduce-m $or [::nothing] (keys ?a-entries))
                                  =vals (reduce-m $or [::nothing] (vals ?a-entries))]
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

    [_ [::union ?types]]
    (exec [_ (map-m #(solve expected %) ?types)]
      (return true))

    [[::intersection ?filter] _]
    (exec [_ (map-m #(solve % actual) ?filter)]
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

(defn prepare-params [params]
  (map #(match %
          (?open :guard symbol?)
          ?open
          [?bounded '< ?top]
          ?bounded)
       params))

(defn apply [type-fn params]
  (prn 'apply type-fn params)
  (match type-fn
    [::all ?env ?params ?type-def]
    (do (prn `(~'= ~(count ?params) ~(count params))
             (into ?env (map vector (prepare-params ?params) params)))
      (if (= (count ?params) (count params))
        (realize (into ?env (map vector (prepare-params ?params) params))
                 ?type-def)
        zero))
    
    :else
    zero))

(defn instantiate [type]
  (match type
    [::all _ ?params _]
    (exec [=params (map-m #(match %
                             (?open :guard symbol?)
                             fresh-hole
                             
                             [?bounded '< ?top]
                             (exec [=hole fresh-hole
                                    _ (narrow-hole =hole ?top [::nothing])]
                               (return =hole)))
                          ?params)
           :let [_ (prn '=params =params)]
           =params* (map-m #(exec [[=top _] (get-hole %)]
                              (return =top))
                           =params)
           :let [_ (prn '=params* =params*)]]
      (apply type =params))
    
    :else
    (return type)))

(defn type-fn? [type]
  (match type
    [::all _ _ _]
    true
    
    :else
    false))

(defn multi-fn? [type]
  (match type
    [::multi-fn _ _]
    true
    
    :else
    false))

(defn instantiate*
  ([name]
     (exec [=type-fn (resolve name)]
       (instantiate =type-fn)))
  ([name params]
     (exec [=type-fn (resolve name)]
       (if (type-fn? =type-fn)
         (apply =type-fn params)
         (return =type-fn)))))

(defn fresh-var [arg]
  (exec [=hole fresh-hole]
    (if-let [tag (-> arg meta :tag)]
      (exec [=tag (instantiate* tag)
             _ (solve =tag =hole)]
        (return =hole))
      (return =hole))))

;; Monads / Types
(do-template [<fn> <tag> <LT-ret> <GT-ret> <LT> <GT>]
  (defn <fn> [base addition]
    ;; (prn '<fn> base addition)
    (match [base addition]
      [_ [<tag> ?addition]]
      (reduce-m <fn> base ?addition)
      
      [[<tag> ?base] _]
      (exec [veredicts (map-m (fn [=base]
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
      (&util/try-all [(exec [_ (solve base addition)
                             ;; :let [_ (prn "<LT>")]
                             ]
                        (return <LT-ret>))
                      (exec [_ (solve addition base)
                             ;; :let [_ (prn "<GT>")]
                             ]
                        (return <GT-ret>))
                      (exec [_ (return nil)
                             ;; :let [_ (prn "<=/=>")]
                             ]
                        (return [<tag> [base addition]]))])
      ))

  $or  ::union        base     addition :parent :child
  ;; $and ::intersection addition base     :child  :parent
  )

(defn $and [base addition]
  (match [base addition]
    [_ [::union ?addition]]
    (reduce-m (fn [=filter =refinement]
                ;; (prn '[AND] =filter =refinement)
                (&util/try-all [(exec [_ (solve =filter =refinement)
                                       ;; :let [_ (prn "Case #1")]
                                       ]
                                  (return =refinement))
                                (exec [_ (solve =refinement =filter)
                                       ;; :let [_ (prn "Case #2")]
                                       ]
                                  (return =filter))
                                (match [=filter =refinement]
                                  [[::object ?filter _] [::object ?refinement _]]
                                  (exec [?1 (interface? ?filter)
                                         ?2 (interface? ?refinement)
                                         ;; :let [_ (prn "Case #3..." ?filter ?1 ?refinement ?2)]
                                         :when (and ?1 ?2)
                                         ;; :let [_ (prn "Case #3")]
                                         ]
                                    ($and =filter =refinement))
                                  
                                  :else
                                  (return =filter))]))
              base
              ?addition)

    [_ [::intersection ?addition]]
    (reduce-m $and base ?addition)
    
    [[::intersection ?base] _]
    (exec [veredicts (map-m (fn [=base]
                              (&util/try-all [(exec [_ (solve =base addition)]
                                                (return :child))
                                              (exec [_ (solve addition =base)]
                                                (return :parent))
                                              (return :peer)]))
                            ?base)]
      (cond (some (partial = :parent) veredicts)
            (return base)

            (every? (partial = :peer) veredicts)
            (return [::intersection (conj ?base addition)])

            :else
            (if-let [rem-types (->> (map vector ?base veredicts)
                                    (filter (comp (partial not= :child) second))
                                    (map first)
                                    seq)]
              (return [::intersection (conj (vec rem-types) addition)])
              (return addition))))
    
    [_ _]
    (&util/try-all [(exec [_ (solve base addition)]
                      (return addition))
                    (exec [_ (solve addition base)]
                      (return base))
                    (match [base addition]
                      [[::object ?filter _] [::object ?refinement _]]
                      (exec [?1 (interface? ?filter)
                             ?2 (interface? ?refinement)
                             :when (and ?1 ?2)]
                        (return [::intersection [base addition]]))
                      
                      :else
                      (return [::nothing]))])
    ))

(defn sequential [t1 t2]
  (match [t1 t2]
    [[::eff ?data-1 ?effs-1] [::eff ?data-2 ?effs-2]]
    (exec [=effs (map-m
                  (fn [key]
                    (exec [=merged (reduce-m $or [::nothing] (filter identity (list (get ?effs-1 key) (get ?effs-2 key))))]
                      (return [key =merged])))
                  (set/union (set (keys ?effs-1)) (set (keys ?effs-2))))]
      (return [::eff ?data-2 =effs]))
    
    [[::eff ?data-1 ?effs-1] _]
    (return [::eff t2 ?effs-1])
    
    [_ _]
    (return t2)
    ))

(defn parallel [t1 t2]
  (match [t1 t2]
    [[::eff ?data-1 ?effs-1] [::eff ?data-2 ?effs-2]]
    (exec [=data ($or ?data-1 ?data-2)
           =effs (map-m (fn [key]
                          (exec [=merged (reduce-m $or [::nothing] (filter identity (list (get ?effs-1 key) (get ?effs-2 key))))]
                            (return [key =merged])))
                        (set/union (set (keys ?effs-1)) (set (keys ?effs-2))))]
      (return [::eff =data =effs]))
    
    [[::eff ?data-1 ?effs-1] _]
    (exec [=data ($or ?data-1 t2)]
      (return [::eff =data ?effs-1]))
    
    [_ [::eff ?data-2 ?effs-2]]
    (exec [=data ($or t1 ?data-2)]
      (return [::eff =data ?effs-2]))
    
    [_ _]
    ($or t1 t2)
    ))
