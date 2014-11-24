(ns system
  (:require [clojure.template :refer [do-template]]
            [clojure.core.match :refer [match]]
            (system [util :as &util :refer [exec
                                            return return-all
                                            map-m reduce-m]]
                    ;; [type :as &type]
                    [parser :as &parser]
                    [type-checker :as &type-checker]
                    [translator :as &translator]
                    [prelude :as &prelude])
            ;; :reload-all
            :reload
            ))

(defonce _init_
  (do ;; (alter-var-root #'clojure.core/prn
      ;;                 (constantly #(.println System/out (apply pr-str %&))))
      ))

(let [context (&prelude/install &type-checker/+init+)]
  ;; (prn 'context context)
  (defn run [code]
    (println "Code:" (pr-str code))
    (let [monad (exec [_ (&util/spread context)
                       parsed-code (&parser/parse code)
                       ;; :let [_ (prn 'parsed-code parsed-code)]
                       ]
                  (&type-checker/check parsed-code))]
      (match (monad nil)
        [::&util/failure ?message]
        (do (println "Error:" ?message)
          (println "")
          [::&util/failure ?message])
        [::&util/ok ?worlds]
        (do (assert (= 1 (count ?worlds)))
          (let [type (&translator/type->code (-> ?worlds first (nth 1)))]
            (->> type pr-str (println "Type:"))
            (println "")
            type))
        ))))


(comment
  (run nil)

  (run '(do (ann parse-int (Fn [java.lang.String -> (Or nil java.lang.Long)]))
          (fn foo [x]
            (let [result (parse-int x)]
              (if result
                result
                "YOLO")))))
  
  (time (do (defn test-contants! []
              (do-template [<type> <form>]
                (assert (= '<type> (run '<form>)))
                
                nil
                nil

                true
                true

                10
                10

                10.0
                10.0

                \a
                \a

                :lol
                :lol

                10N
                10N

                10M
                10M

                1/2
                1/2))

          (defn test-simple-forms! []
            (do-template [<type> <form>]
              (assert (= '<type> (run '<form>)))
              
              nil
              (do nil)
              
              (clojure.lang.Var Nothing)
              (def foo)

              (clojure.lang.Var nil)
              (def foo (do nil))

              nil
              (let [foo nil]
                nil)

              10
              (let [foo 10]
                foo)

              nil
              (do (def foo nil)
                foo)

              (clojure.lang.Var 10)
              (do (def foo 10)
                #'foo)))

          (defn test-simple-inference! []
            (do-template [<type> <form>]
              (assert (= '<type> (run '<form>)))
              
              (Or nil java.lang.Long)
              (do (ann parse-int (Fn [java.lang.String -> (Or nil java.lang.Long)]))
                (parse-int "1234"))

              (Or java.lang.Long "YOLO")
              (do (ann parse-int (Fn [java.lang.String -> (Or nil java.lang.Long)]))
                (let [result (parse-int "1234")]
                  (if result
                    result
                    "YOLO")))

              (Fn (All [a] [a -> a]))
              (fn id [x] x)

              (Fn [java.lang.String -> (Or nil java.lang.Long)])
              (do (ann parse-int (Fn [java.lang.String -> (Or nil java.lang.Long)]))
                (fn foo [x]
                  (parse-int x)))

              (Fn [java.lang.String -> (Or java.lang.Long "YOLO")])
              (do (ann parse-int (Fn [java.lang.String -> (Or nil java.lang.Long)]))
                (fn foo [x]
                  (let [result (parse-int x)]
                    (if result
                      result
                      "YOLO"))))

              (Fn [clojure.lang.IPersistentMap -> :klk]
                  [(Not clojure.lang.IPersistentMap) -> "manito"])
              (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                                [(Not clojure.lang.IPersistentMap) -> false]))
                (fn foo [x]
                  (if (map? x)
                    :klk
                    "manito")))
              
              (Fn [clojure.lang.IPersistentMap -> :yolo]
                  [(Not clojure.lang.IPersistentMap) -> "lol"])
              (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                                [(Not clojure.lang.IPersistentMap) -> false]))
                (fn foo [x]
                  (let [? (map? x)]
                    (if ?
                      :yolo
                      "lol"))))

              (Fn [clojure.lang.IPersistentMap -> "manito"]
                  [(Not clojure.lang.IPersistentMap) -> :klk])
              (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                                [(Not clojure.lang.IPersistentMap) -> false]))
                (fn foo [x]
                  (let [x (if (map? x)
                            "manito"
                            :klk)]
                    x)))

              java.lang.Object
              (do (ann foo (Fn [java.lang.Object -> java.lang.Object]))
                (foo "bar"))

              (Fn [1 -> "YOLO"]
                  ["2" -> "LOL"]
                  [:3 -> "MEME"])
              (fn case-test [x]
                (case x
                  1   "YOLO"
                  "2" "LOL"
                  :3  "MEME"))))

          (test-contants!)
          (test-simple-forms!)
          (test-simple-inference!)
          
          (do-template [<type> <form>]
            (assert (= '<type> (run '<form>)))
            
            nil
            (defalias (Maybe x) (Or nil x))

            IntOrString
            (do (defalias IntOrString (Or java.lang.Integer java.lang.String))
              (ann yolo IntOrString)
              yolo)

            '[]
            []

            '{}
            {}

            (clojure.lang.IPersistentSet Nothing)
            #{}

            '[:klk "YOLO"]
            [:klk "YOLO"]
            
            (Fn [1 -> "YOLO"] ["2" -> "LOL"] [:3 -> "MEME"] [Any -> "default"])
            (fn case-test [x]
              (case x
                1   "YOLO"
                "2" "LOL"
                :3  "MEME"
                "default"))

            (Fn [(Or 1 2 3) -> "YOLO"] ["2" -> "LOL"] [:3 -> "MEME"] [Any -> "default"])
            (fn case-test [x]
              (case x
                (1 2 3)   "YOLO"
                "2" "LOL"
                :3  "MEME"
                "default"))

            'yolo
            'yolo
            
            (clojure.lang.PersistentList (Or 1 'dos "tres"))
            '(1 dos "tres")

            nil
            (monitor-enter "YOLO")
            
            nil
            (monitor-exit "YOLO")
            
            nil
            (do (monitor-enter "YOLO")
              (monitor-exit "YOLO"))

            [::&util/failure "Can't solve types. Expected: [:system.type/complement [:system.type/nil]] Actual: [:system.type/nil]"]
            (monitor-enter nil)

            [::&util/failure "Can't solve types. Expected: [:system.type/complement [:system.type/nil]] Actual: [:system.type/nil]"]
            (monitor-exit nil)

            (Eff Nothing {:try java.lang.Exception})
            (do (ann ex (Fn [-> java.lang.Exception]))
              (throw (ex)))

            (Eff 1 {:try java.lang.Exception})
            (do (ann ex (Fn [-> java.lang.Exception]))
              (throw (ex))
              1)

            (Eff :else {:try java.lang.Exception})
            (do (ann test (Or true false))
              (ann ex (Fn [-> java.lang.Exception]))
              (let [test* test]
                (if test*
                  (throw (ex))
                  :else)))

            (Eff :else {:try java.lang.Exception})
            (do (ann test (Or true false))
              (ann ex (Fn [-> java.lang.Exception]))
              (let [test* test]
                (try (if test*
                       (throw (ex))
                       :else))))

            (Or :catch :else)
            (do (ann test (Or true false))
              (ann ex (Fn [-> java.lang.Exception]))
              (let [test* test]
                (try (if test*
                       (throw (ex))
                       :else)
                  (catch java.lang.Exception e
                    :catch)
                  (finally :finally))))

            (Eff (Or :catch :else) {:try java.lang.Exception})
            (do (ann test (Or true false))
              (ann ex (Fn [-> java.lang.Exception]))
              (ann-class java.lang.YoloException [java.lang.Exception])
              (let [test* test]
                (try (if test*
                       (throw (ex))
                       :else)
                  (catch java.lang.YoloException e
                    :catch)
                  (finally :finally))))

            (Eff java.lang.String {:io IO})
            (do (ann read-line (Fn [-> (Eff java.lang.String {:io IO})]))
              (read-line))

            (Eff Nothing {:io IO, :try java.lang.Exception})
            (do (ann ex (Fn [-> java.lang.Exception]))
              (ann read-line (Fn [-> (Eff java.lang.String {:io IO})]))
              (read-line)
              (throw (ex)))

            (Eff :yolo {:io IO})
            (do (ann println (Fn [java.lang.String -> (Eff nil {:io IO})]))
              (println "YOLO")
              :yolo)

            1
            (do (ann global java.lang.String)
              (binding [global "YOLO"]
                1))

            [::&util/failure "Can't solve types. Expected: [:system.type/object java.lang.String []] Actual: [:system.type/literal java.lang.Long 10]"]
            (do (ann global java.lang.String)
              (binding [global 10]
                1))

            10
            (loop [a 10]
              a)

            java.lang.Long
            (do (ann + (Fn [java.lang.Long java.lang.Long -> java.lang.Long]))
              (loop [a 10
                     b 20]
                (+ a b)))

            Nothing
            (do (ann inc (Fn [java.lang.Long -> java.lang.Long]))
              (loop [a 0]
                (recur (inc a))))

            [::&util/failure "No alternative worked!"]
            (do (ann defn Macro)
              defn)

            10
            (do (ann defn Macro)
              10)

            (Fn [Map -> Any])
            (fn _ [x]
              (:yolo x))

            java.lang.String
            (do (ann-class java.lang.Collection [java.lang.Object])
              (ann-class java.lang.Map [java.lang.Collection])
              (ann get-map (Fn [-> java.lang.Map]))
              (ann coll->str (Fn [java.lang.Collection -> java.lang.String]))
              (coll->str (get-map)))

            '{:a 10 :b "YOLO"}
            {:a 10 :b "YOLO"}

            "YOLO"
            (do (ann identity (Fn (All [x] [x -> x])))
              (identity "YOLO"))

            java.lang.String
            (do (ann-class (java.lang.Collection x) [java.lang.Object])
              (ann-class (java.lang.KV key val) [java.lang.Object])
              (ann-class (java.lang.Map key val) [(java.lang.Collection (java.lang.KV key val))])
              (ann get-map (Fn [-> (java.lang.Map java.lang.String java.lang.Integer)]))
              (ann coll->str (Fn (All [key val]
                                      [(java.lang.Collection (java.lang.KV key val)) -> java.lang.String])))
              (coll->str (get-map)))

            (java.lang.Collection (java.lang.KV java.lang.String java.lang.Integer))
            (do (ann-class (java.lang.Collection x) [java.lang.Object])
              (ann-class (java.lang.KV key val) [java.lang.Object])
              (ann-class (java.lang.Map key val) [(java.lang.Collection (java.lang.KV key val))])
              (ann get-map (Fn [-> (java.lang.Map java.lang.String java.lang.Integer)]))
              (ann ->coll (Fn (All [key val elem]
                                   [(java.lang.Map key val) -> (java.lang.Collection (java.lang.KV key val))])))
              (->coll (get-map)))

            (Fn [java.lang.Long -> java.lang.Double])
            (fn _ [x]
              (. x (doubleValue)))
            
            (Fn [java.lang.Long -> java.lang.Long])
            (fn _ [x]
              (. x value))

            java.lang.Long
            (java.lang.Long/decode "YOLO")

            java.lang.Long
            java.lang.Long/MAX_VALUE

            java.lang.Long
            (new java.lang.Long "YOLO")

            (Fn (All [[a < (java.lang.Map Any Any)]] [a -> a]))
            (do (ann-class (java.lang.Map key val) [java.lang.Object])
              (ann map? (Fn [(java.lang.Map Any Any) -> true]
                            [(Not (java.lang.Map Any Any)) -> false]))
              (fn foo [x]
                (assert (map? x) "YOLO")
                x))

            (Fn (All [[a < (java.lang.Map Any Any)]] [a -> a]))
            (do (ann-class (java.lang.Map key val) [java.lang.Object])
              (ann map? (Fn [(java.lang.Map Any Any) -> true]
                            [(Not (java.lang.Map Any Any)) -> false]))
              (fn [x]
                (assert (map? x) "YOLO")
                x))

            (Fn (All [a b] [(Fn [a -> b]) a -> b]))
            (fn _ [f x]
              (f x))

            java.lang.Long
            (do (ann inc (Fn [java.lang.Long -> java.lang.Long]))
              (ann = (Fn [Any Any -> java.lang.Boolean]))
              (loop [a 0]
                (if (= 10 a)
                  a
                  (recur (inc a)))))

            java.lang.Long
            (do (ann inc (Fn [java.lang.Long -> java.lang.Long]))
              (ann = (Fn [Any Any -> java.lang.Boolean]))
              (loop [a 0]
                (if (= 10 a)
                  (recur (inc a))
                  a)))

            (Eff Nothing {:try java.lang.Exception})
            (do (ann ex (Fn [-> java.lang.Exception]))
              (if true
                (throw (ex))
                :else))

            :else
            (do (ann ex (Fn [-> java.lang.Exception]))
              (if false
                (throw (ex))
                :else))

            (Eff :else {:try java.lang.Exception})
            (do (ann test java.lang.Boolean)
              (ann ex java.lang.Exception)
              (let [test* test]
                (if test*
                  (throw ex)
                  :else)))

            (Eff :else {:try java.lang.Exception})
            (do (ann test java.lang.Boolean)
              (ann ex java.lang.Exception)
              (if test
                :else
                (throw ex)))

            (Fn [java.lang.Exception -> :yolo])
            (do (ann only-exs (Fn (All [[x < java.lang.Exception]] [x -> x])))
              (fn _ [x]
                (only-exs x)
                :yolo))

            (Fn (All [[a < java.lang.Exception]] [a -> a]))
            (do (ann only-exs (Fn (All [[x < java.lang.Exception]] [x -> x])))
              (fn _ [x]
                (only-exs x)))

            (MultiFn (Fn (All [c] [c -> (java.lang.Class c)])) =>
                     [java.lang.String -> "It's a string!"])
            (do (ann class (Fn (All [c] [c -> (java.lang.Class c)])))
              (defmulti obj->string class)
              (defmethod obj->string java.lang.String [_]
                "It's a string!"))

            (MultiFn (Fn (All [c] [c -> (java.lang.Class c)])) =>
                     (All [[a < java.lang.String]] [a -> a]))
            (do (ann class (Fn (All [c] [c -> (java.lang.Class c)])))
              (defmulti obj->string class)
              (defmethod obj->string java.lang.String [s]
                s))

            "It's a string!"
            (do (ann class (Fn (All [c] [c -> (java.lang.Class c)])))
              (defmulti obj->string class)
              (defmethod obj->string java.lang.String [_]
                "It's a string!")
              (obj->string "yolo"))

            [::&util/failure "Can't solve types. Expected: [:system.type/object java.lang.String ()] Actual: [:system.type/literal clojure.lang.Keyword :yolo]"]
            (do (ann class (Fn (All [c] [c -> (java.lang.Class c)])))
              (defmulti obj->string class)
              (defmethod obj->string java.lang.String [_]
                "It's a string!")
              (obj->string :yolo))

            (Fn (All [[a < (java.lang.Map Any Any)]] [a -> a]))
            (do (ann-class (java.lang.Map key val) [java.lang.Object])
              (ann map? (Fn [(java.lang.Map Any Any) -> true]
                            [(Not (java.lang.Map Any Any)) -> false]))
              (fn [x]
                {:pre [(map? x)]}
                x))

            (Fn (All [[a < (java.lang.Map java.lang.String Any)]] [a -> a]))
            (do (ann-class (java.lang.Map key val) [java.lang.Object])
              (ann map? (Fn [(java.lang.Map Any Any) -> true]
                            [(Not (java.lang.Map Any Any)) -> false]))
              (ann string-map? (Fn [(java.lang.Map java.lang.String Any) -> true]
                                   [(Not (java.lang.Map Any Any)) -> false]))
              (fn [x]
                {:pre [(map? x)]
                 :post [(string-map? %)]}
                x))

            (Fn (All [[a < java.lang.String]] [a -> a]))
            (fn [^java.lang.String x]
              x)

            (Fn (All [[a < java.lang.Long]] [a -> a]))
            (do (ann inc (Fn [java.lang.Long -> java.lang.Long]))
              (ann = (Fn [Any Any -> java.lang.Boolean]))
              (fn [a]
                (if (= 10 a)
                  a
                  (recur (inc a)))))

            (Fn [java.lang.Long -> Nothing])
            (do (ann inc (Fn [java.lang.Long -> java.lang.Long]))
              (ann = (Fn [Any Any -> java.lang.Boolean]))
              (fn [a]
                (recur (inc a))))

            (Fn (All [[a < (java.lang.Map Any Any)]] [a -> a])
                [(Not (java.lang.Map Any Any)) -> "YOLO"])
            (do (ann-class (java.lang.Map key val) [java.lang.Object])
              (ann map? (Fn [(java.lang.Map Any Any) -> true]
                            [(Not (java.lang.Map Any Any)) -> false]))
              (fn foo [x]
                (if (map? x)
                  x
                  "YOLO")))

            Test
            (do (defalias Test
                  (Rec [x]
                       (Or java.lang.Long (clojure.lang.PersistentList x))))
              (ann list (Fn (All [x] [x -> (clojure.lang.PersistentList x)])))
              (ann as-test (Fn (All [[a < Test]] [a -> a])))
              (as-test 10))

            Test
            (do (defalias Test
                  (Rec [x]
                       (Or java.lang.Long (clojure.lang.PersistentList x))))
              (ann list (Fn (All [x] [x -> (clojure.lang.PersistentList x)])))
              (ann as-test (Fn (All [[a < Test]] [a -> a])))
              (as-test (list 10)))

            Test
            (do (defalias Test
                  (Rec [x]
                       (Or java.lang.Long (clojure.lang.PersistentList x))))
              (ann list (Fn (All [x] [x -> (clojure.lang.PersistentList x)])))
              (ann as-test (Fn (All [[a < Test]] [a -> a])))
              (as-test (list (list 10))))

            [::&util/failure "Can't solve types. Expected: [:system.type/object clojure.lang.PersistentList [[:system.type/rec x [:system.type/union [[:system.type/object java.lang.Long []] [:system.type/object clojure.lang.PersistentList [x]]]]]]] Actual: [:system.type/literal java.lang.String \"10\"]"]
            (do (defalias Test
                  (Rec [x]
                       (Or java.lang.Long (clojure.lang.PersistentList x))))
              (ann list (Fn (All [x] [x -> (clojure.lang.PersistentList x)])))
              (ann as-test (Fn (All [[a < Test]] [a -> a])))
              (as-test (list (list "10"))))

            (Or java.lang.Long (clojure.lang.PersistentList (ctor elem)))
            (do (defalias Test
                  (Rec [ctor]
                       (All [elem]
                            (Or elem (clojure.lang.PersistentList (ctor elem))))))
              (ann list (Fn (All [x] [x -> (clojure.lang.PersistentList x)])))
              (ann as-test (Fn (All [[a < (Test java.lang.Long)]] [a -> a])))
              (as-test 10))

            (Or java.lang.Long (clojure.lang.PersistentList (ctor elem)))
            (do (defalias Test
                  (Rec [ctor]
                       (All [elem]
                            (Or elem (clojure.lang.PersistentList (ctor elem))))))
              (ann list (Fn (All [x] [x -> (clojure.lang.PersistentList x)])))
              (ann as-test (Fn (All [[a < (Test java.lang.Long)]] [a -> a])))
              (as-test (list (list 10))))

            10
            (do (ann yolo java.lang.Long)
              (set! yolo 10))

            [::&util/failure "Can't solve types. Expected: [:system.type/object java.lang.Long []] Actual: [:system.type/literal java.lang.String \"10\"]"]
            (do (ann yolo java.lang.Long)
              (set! yolo "10"))

            'Yolo
            (defprotocol Yolo
              (yolo [_]))

            (Protocol Yolo {yolo (Fn [Any -> Any])})
            (do (defprotocol Yolo
                  (yolo [_]))
              Yolo)

            (java.lang.Class Bar)
            (do (defprotocol Foo
                  (foo [_]))
              (deftype Bar []
                Foo
                (foo [_] "BAR")))

            (java.lang.Class Bar)
            (do (defprotocol Foo
                  (foo [_]))
              (defrecord Bar []
                Foo
                (foo [_] "BAR")))

            (Reify {Foo {foo (Fn [Any -> 17])}})
            (do (defprotocol Foo
                  (foo [_]))
              (reify Foo
                (foo [self] 17)))

            nil
            (do (defprotocol Foo
                  (foo [_]))
              (extend java.lang.String
                Foo
                {:foo (fn [self] self)}))

            (clojure.lang.PersistentList java.lang.String)
            (do (ann map (Fn (All [a b] [(Fn [a -> b]) (clojure.lang.PersistentList a) -> (clojure.lang.PersistentList b)])))
              (ann str (Fn [Any -> java.lang.String]))
              (map str '(1 2 3)))

            (clojure.lang.PersistentList java.lang.Long)
            (do (ann map (Fn (All [a b] [(Fn [a -> b]) (clojure.lang.PersistentList a) -> (clojure.lang.PersistentList b)])))
              (ann inc (Fn [java.lang.Integer -> java.lang.Long]))
              (ann get-list (Fn [-> (clojure.lang.PersistentList java.lang.Integer)]))
              (map inc (get-list)))
            )))

  
  ;; (run ')
  
  
  
  ;; MISSING: Destructuring
  ;; MISSING: covariance, contravariance & invariance.
  ;; MISSING: Multi-arity fns.
  ;; MISSING: var-args
  ;; MISSING: gen-class & proxy
  ;; MISSING: macro-expansion.
  ;; MISSING: Scope handling (public vs private)
  ;; MISSING: Pre-inference annotating.
  ;; MISSING: 
  ;; MISSING: 
  ;; MISSING: 

  

  
  
  (do (defn combinations [elems]
        (distinct (for [head elems
                        tail (for [entry (cons #{head} (combinations (disj elems head)))]
                               (conj entry head))]
                    tail)))
    (combinations #{1 2 3}))

  (#{1} #{1 2} #{1 3} #{1 2 3} #{2} #{2 3} #{3}) ;; Expected
  (#{1} #{1 2} #{1 3} #{1 2 3} #{2} #{2 3} #{3}) ;; Actual
  
  
  
  
  
  
  

  
  
  ;; The one below is not supposed to type-check due to lack of
  ;; coverage of type possibilities.
  ;; Gotta make holes on check*, instead of on ::let
  (run '(do (ann get-object (Fn [-> java.lang.Object]))
          (ann use-case (Fn [java.lang.String -> :yolo]
                            [java.lang.Integer -> :lol]
                            [java.lang.Boolean -> :meme]))
          (fn foo []
            (use-case (get-object)))))

  (run '(do (ann get-object (Fn [-> java.lang.Object]))
          (ann use-case (Fn [String -> :yolo]
                            [Integer -> :lol]
                            [Boolean -> :meme]))
          (fn foo []
            (use-case (get-object)))))

  (run '(do (ann-class (java.lang.List x) [java.lang.Object])
          (defalias (RecTest x) (Or x (java.lang.List (RecTest x))))
          (ann yolo (RecTest java.lang.Integer))
          yolo
          ))

  ;; TODO: Don't add :try effects if the throwable is either an Error or a RuntimeException
  ;; TODO: The missing aesthetic changes on recursive types for correct translation + inference.
  ;; TODO: Take into account return type-tags.
  ;; TODO: Infer recursive types by analysing code.
  ;; TODO: On 'let forms, ensure refining goes over all possibilities.
  ;; TODO: 
  
  ;; Must fix issue with refining in order to get this to type-check.
  (run '(do (ann inc (Fn [(Or java.lang.Integer java.lang.Long) -> java.lang.Integer]))
          (ann < (Fn [java.lang.Number java.lang.Number -> java.lang.Boolean]))
          (loop [cnt 0]
            (if (< cnt 10)
              (recur (inc cnt))
              :done))))

  (run '(do (ann inc (Fn [(Or java.lang.Integer java.lang.Long) -> java.lang.Integer]))
          (ann < (Fn [java.lang.Number java.lang.Number -> java.lang.Boolean]))
          (fn [cnt]
            (if (< cnt 10)
              (recur (inc cnt))
              :done))))

  (run '(do (ann inc (Fn [(Or java.lang.Integer java.lang.Long) -> java.lang.Integer]))
          (ann < (Fn [java.lang.Number java.lang.Number -> java.lang.Boolean]))
          (let [cnt 0]
            (< cnt 10)
            (inc cnt))))

  
  ;; This is a valid way of implementing letfn using a macro...
  ;; (let [odd* (fn [odd even]
  ;;              (fn [x]
  ;;                (if (= 0 x)
  ;;                  false
  ;;                  ((even odd even) (dec x)))))
  ;;       even* (fn [odd even]
  ;;               (fn [x]
  ;;                 (if (= 0 x)
  ;;                   true
  ;;                   ((odd odd even) (dec x)))))
  ;;       odd (odd* odd* even*)
  ;;       even (even* odd* even*)]
  ;;   (odd 21))
  
  ;; (def (** base exp)
  ;;   (reduce * 1 (repeat base exp)))

  ;; (class **
  ;;   (execute [base exp]
  ;;     (reduce * 1 (repeat base exp))))
  
  ;; (reify Function
  ;;   (apply [self base]
  ;;     (reify Function
  ;;       (apply [self exp]
  ;;         (.execute ** base exp)))))
  
  ;; (defprotocol Function
  ;;   (apply [self x]))

  ;; ($math 10 < x < (20 ** 5))

  ;; (-> [Integer Integer] Integer) vs (-> Integer Integer Integer)

  ;; (defmacro (defmacro* [name symbol] [args n-tuple] [body expr])
  ;;   `(defmacro ((~ name) (~@ (map (\ a (->tuple (list a expr))) args)))
  ;;      ~body))

  ;; (defmacro* defn [name args body]
  ;;   `(def ((~ name) (~@ args))
  ;;      (~ body)))

  ;; (defn+ (plus [x Int] [y Int] Int)
  ;;   (+ x y))

  ;; (: plus (All [a] (-> a a a)))
  ;; (def (plus x y)
  ;;   (+ x y))

  ;; (defn+ ((plus a) [x a] [y a] a)
  ;;   (+ x y))

  )
