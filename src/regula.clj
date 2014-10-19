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

;; (comment
;;   (if test
;;     then
;;     else)

;;   (let expr
;;     bindings)

;;   (do steps
;;     return)

;;   (case value
;;     ~@match->expr)

;;   (let (str yolo lol)
;;     [yolo 1234
;;      lol 5678])
  
;;   (do [a (foo)
;;        b (bar)
;;        c (baz)]
;;     (+ a b c))

;;   (: str (=> (Show x)
;;              (-> (List x) String)))
;;   (def (str xs)
;;     (case (xs)
;;       ([])        ""
;;       ([x & xs*]) (str (show x) (str xs*))
;;       ))
  
;;   (: str (All [x]
;;               (=> (Show x)
;;                   (-> (List x) String))))
;;   (defcase str
;;     ([])        ""
;;     ([x & xs*]) (str (show x) (str xs*)))

;;   (macro (+ [operands (parse+ expr)])
;;          (e))

;;   (: (\x (Show x))
;;      (All [a | (Show a)]
;;           (-> a String)))

;;   (def (plus x y) (+ x y)) => (def (plus x) (\y (+ x y)))

;;   (plus x y) => ((plus x) y)

;;   (data (Maybe x)
;;         (Just x)
;;         Nothing)

;;   (protocol (Monad m)
;;             (: bind   (-> (m a) (-> a (m b)) (m b)))
;;             (: return (-> a (m a))))

;;   (instance (Monad Maybe)
;;             (def (bind m-value m-step)
;;               (case m-value
;;                 (Just x) (m-step x)
;;                 Nothing  Nothing))
;;             (def (return value)
;;               (Just value))
;;             )

;;   (: when (-> 'Boolean 'x (Maybe 'x)))
;;   (macro when
;;          (do [test parse-expr
;;               then parse-expr]
;;            `(if ~test
;;               (Just ~then)
;;               Nothing)))

;;   ;; (: when (-> 'Boolean 'x (Maybe 'x)))
;;   (macro (when #(test expr) #(then expr))
;;          `(if ~test
;;             (Just ~then)
;;             Nothing))

;;   (macro (do [bindings (+! parse-binding)]
;;            [return parse-expr])
;;          (reduce (\case (return pair)
;;                   (_ (Binding label value))
;;                   `(bind ~value (\ ~label ~step)))
;;                  `(return ~return)
;;                  bindings))

;;   (def (ensure parser)
;;     (do [parsed parser
;;          _ no-more]
;;       (return parsed)))

;;   (def (ensure parser)
;;     (do parsed <- parser
;;         no-more
;;         (return parsed)))

;;   (defcase first
;;     ([])      Nothing
;;     ([h & t]) (Just h))

;;   (defcase first
;;     (Nil)        Nothing
;;     ((Cons h t)) (Just h))

;;   (defn first [l]
;;     (if (empty? l)
;;       nil
;;       (nth l 0)))

;;   (let [x 10]
;;     (when (< x 10)
;;       x))

;;   (type (Lazy x) (-> _ x))
  
;;   (data (LazyList x)
;;         LNil
;;         (LCons x (Lazy (LazyList x))))

;;   (instance (LazyList x) [(Sequence x)]
;;             (defcase head
;;               LNil        Nothing
;;               (LCons x _) (Just x))
;;             (defcase tail
;;               LNil        Nothing
;;               (LCons _ t) (Just (t nil))))

;;   (data Syntax
;;         (Symbol String)
;;         (QualifiedSymbol String String)
;;         (Form [Syntax]))

;;   (do [bindings (parse+ (seq parse-symbol parse-expr))
;;        return parse-expr]
;;     [bindings return])

;;   (def uses!
;;     (do [_ (=symbol 'use)]
;;       (+! (do [name symbol!
;;                alias (?! (do [_ (=symbol 'as)
;;                               alias symbol!]
;;                            alias))
;;                referrals (*! (do [_ (=symbol 'refer)
;;                                   refers list!]
;;                                refers))]))))
  
;;   (let (macro (module [name symbol!]
;;                       [deps (+! dep!)]))
;;     (dep! (or! uses! imports!)))

;;   (% + 1 2 3 4 5)

;;   (macro (% (op expr)
;;             (args (>! 2 expr)))
;;          (case (args)
;;            ([a1 a2])
;;            `(~op a1 a2)
           
;;            ([a1 a2 & args*])
;;            `(% (~op a1 a2) ~@args*)
;;            ))

;;   (do [#(_ #(country area local)) #"(\d{3})-?(\d{3})-?(\d{4})"]
;;     (return (PhoneNumber country area local)))
  
;;   #"(\d{3})-?(\d{3})-?(\d{4})" -> (Maybe #(String #(String String String)))

;;   ;; <; This is a comment like any other.
;;   ;;    Comments can't be in the middle of other tokens, but they can be
;;   ;;    anywhere else. ;>

;;   (macro (-> (init expr!)
;;              (parts (*! expr!)))
;;          (reduce (\ (inner outer)
;;                   (case outer
;;                     (Form [f & elems]) `(~f ~inner ~@elems)
;;                     (Symbol _)         `(~outer inner)))
;;                  init
;;                  parts))

;;   (syntax (-> (init expr!)
;;               (parts (*! expr!)))
;;           (reduce (\ (inner outer)
;;                    (case outer
;;                      (Form [f & elems]) `(~f ~inner ~@elems)
;;                      (Symbol _)         `(~outer inner)))
;;                   init
;;                   parts))
;;   (macro ->
;;          (do [init expr!
;;               parts (*! expr!)]
;;            (reduce (\ (inner outer)
;;                     (case outer
;;                       (Form [f & elems]) `(~f ~inner ~@elems)
;;                       (Symbol _)         `(~outer inner)))
;;                    init
;;                    parts)))

;;   (macro ->
;;          (do init <- expr!
;;              parts <- (*! expr!)
;;              (reduce (\ (inner outer)
;;                       (case outer
;;                         (Form [f & elems]) `(~f ~inner ~@elems)
;;                         (Symbol _)         `(~outer inner)))
;;                      init
;;                      parts)))

;;   (macro (->> (init expr!)
;;               (parts (*! expr!)))
;;          (reduce (\ (inner outer)
;;                   (case outer
;;                     (Form elems) `(~@elems ~inner)
;;                     (Symbol _)   `(~outer inner)))
;;                  init
;;                  parts))

;;   (type-class (Stack stack)
;;               (: push (-> x stack stack))
;;               (: pop (-> stack (Maybe stack))))

;;   (instance (Stack (List x))
;;             (def (push x list)
;;               (cons x list))
;;             (defcase pop
;;               []      Nothing
;;               [x & _] (Just x)))

;;   (def (reduce f init elems)
;;     (case elems
;;       []       init
;;       [x & xs] (reduce f (f init x) xs)))

;;   (defcase reduce
;;     (f init [])       init
;;     (f init [x & xs]) (reduce f (f init x) xs))

;;   (defn reduce [f init elems]
;;     (if (empty? elems)
;;       init
;;       (recur f (f init (first elem)) (rest elem))))

;;   (-> yolo
;;       lol
;;       (foo bar)
;;       (baz)
;;       (->> (with :yolo 20)
;;            (without :lol)))

;;   (with :yolo 20 {:lol 10})
;;   (without :lol {:lol 10})

;;   (module regula
;;           (use (alt.typed :as t :refer [defalias])
;;                (clojure.core.logic :as logic)
;;                (clojure.core.logic.pldb :as logic-db))
;;           (import (clojure.lang [Keyword])))

;;   [x | x <- (range 10) :when (even? x)]

;;   (do [x (range 0 10)
;;        :when (even? x)]
;;     x)

;;   (css ("*" {}
;;         (".yolo" {}))
;;        ("#lol" {}))

;;   (html (:div (:span#lol)))

;;   (data HTMLElem
;;         (HTMLElem (Map String String) [HTMLElem]))

;;   (data List x = Nil | Cons x (List x))

  
;;   ;; Yields private definition
;;   (def (plus x y)
;;     (+ x y))

;;   ;; Yields public definition
;;   (export
;;    (def (plus x y)
;;      (+ x y)))

;;   ;; Same goes for macros...

;;   ;; Tuple syntax
;;   (: #(a b c) #(Int String Boolean))
;;   {: {:a 1 :b "YOLO"} {:a Integer :b String}}

;;   #a ;; Characters

;;   (: assoc (-> k v r {k v & r}))
  
;;   (let (assoc :c True rec)
;;     [rec {:a 1 :b "YOLO"}])

;;   (lazy (+ 1 2))
;;   (! lazy-value)

;;   (= (! (lazy (+ 1 2)))
;;      (+ 1 2))

;;   (macro (lazy #(expr expr))
;;          `(\ _# ~expr))

;;   (defmacro lazy [expr]
;;     `(fn [_#] ~expr))

;;   Just == Just.apply == (new Just x)

;;   #"yolo" ;; Regex syntax actually compiles down to monadic parser.
  
;;   (defcase take
;;     (0 _)        (Just [])
;;     (n [])       Nothing
;;     (n [x & xs]) (do [taken (take (- n 1) xs)]
;;                    (return (cons x taken))))

;;   (macro (cond [branches (+! branch)]
;;                [else expr])
;;          (reduce (\case
;;                   (else #(test then))
;;                   `(if ~test ~then ~else))
;;                  expr
;;                  branches))

;;   (cond (= 0 0) HellYeah
;;         (= 0 1) HeavensNo
;;         Dunno)

;;   (type (Lazy x) (-> _ x))
;;   (data (LazyList x)
;;         LNil
;;         (LCons (Lazy x) (LazyList x)))

;;   (protocol (Sequence x)
;;             (: first (-> (Sequence x) (Maybe x)))
;;             (: rest (-> (Sequence x) (Maybe (Sequence x)))))

;;   (interface (Sequence x)
;;              (: first (-> (Sequence x) (Maybe x)))
;;              (: rest (-> (Sequence x) (Maybe (Sequence x)))))

;;   (instance (LazyList x) [(Sequence x)]
;;             (defcase first
;;               (LNil)         Nothing
;;               (LCons lazy _) (lazy nil))
;;             (defcase rest ...))

;;   (defcase count
;;     ([])       0
;;     ([x & xs]) (+ 1 (count xs)))

;;   (data (Iterator x)
;;         Done
;;         (Iterator x (-> _ (Iterator x))))

;;   (: iterate (-> x (-> x x) (Iterator x)))
;;   (def (iterate init f)
;;     (Iterator init (\ (_) (iterate (f init) f))))

;;   (defcase current
;;     [Done]                Nothing
;;     [(Iterator now next)] (Just now))

;;   (def (current Done)             Nothing)
;;   (def (current (Iterator now _)) (Just now))

;;   (def (next iterator)
;;     (case iterator
;;       Done                Nothing
;;       (Iterator now next) (Just (next nil))))

;;   (def (println string)
;;     (wrap-io (j/. System out (println string))))

;;   (defmacro (wrap-io computation)
;;     (IO (\ [_] computation)
;;         (\ (next) (next computation))))

;;   (data (IO x)
;;         (IO (-> _ x)))

;;   (: unsafe-perform-io io)
;;   (def (unsafe-perform-io io)
;;     (case io
;;       (IO now) (let [now* (now nil)]
;;                  (IO (\ _ (then now*))))))

;;   (data (Message x)
;;         Die
;;         (Message x))

;;   (data Message x = Die | Message x)

;;   (type (Message x)
;;         (data Die
;;               (Message x)))

;;   (def (send chan msg)
;;     (# send chan (Message msg)))

;;   (data (Process state input output)
;;         (Process state (Channel input) (Channel output)))
  
;;   (: reply (-> output (Process state input output) (Process state input output)))
  
;;   (process (P state)
;;     YOLO (reply! "nyan")
;;     LOL  (reply! "cat"))
  
;;   (do [p (spawn! P)
;;        _ (send! p YOLO)]
;;     )

;;   (j/. System out (println "YOLO"))
;;   )
