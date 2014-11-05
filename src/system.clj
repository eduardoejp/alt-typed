(ns system
  (:require [clojure.template :refer [do-template]]
            (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]]
                    ;; [type :as &type]
                    [parser :as &parser]
                    [type-checker :as &type-checker]
                    [translator :as &translator]
                    [prelude :as &prelude])
            ;; :reload-all
            :reload
            ))

(comment
  (time (do (defonce _init_
              (do (alter-var-root #'clojure.core/prn
                                  (constantly #(.println System/out (apply pr-str %&))))))
          
          (let [[[context _]] (&prelude/install &type-checker/+init+)]
            ;; (prn 'context context)
            (defn run [code]
              (println "Code:" (pr-str code))
              (let [monad (exec state-seq-m
                            [parsed-code (&parser/parse code)]
                            (&type-checker/check parsed-code))
                    types (map (comp &translator/type->code second)
                               (monad context))]
                (doseq [type types]
                  (->> type pr-str (println "Type:")))
                (println "")
                types)))
          
          (do-template [<type> <form>]
            (assert (= '<type> (run '<form>)))
            
            (nil)
            nil

            (true)
            true

            (10)
            10

            (10.0)
            10.0

            (\a)
            \a

            (:lol)
            :lol

            (10N)
            10N

            (10M)
            10M

            (1/2)
            1/2

            (nil)
            (do nil)
            
            ((clojure.lang.Var Nothing))
            (def foo)

            ((clojure.lang.Var nil))
            (def foo (do nil))

            (nil)
            (let [foo nil]
              nil)

            (10)
            (let [foo 10]
              foo)

            (nil)
            (do (def foo nil)
              foo)

            ((clojure.lang.Var 10))
            (do (def foo 10)
              #'foo)

            ((Or nil java.lang.Long))
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (parse-int "1234"))

            (nil)
            (defalias (Maybe x) (Or nil x))

            ((Or "YOLO" java.lang.Long))
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (let [result (parse-int "1234")]
                (if result
                  result
                  "YOLO")))

            ((All [a] [a -> a]))
            (fn id [x] x)

            ((Tuple))
            []

            ({})
            {}

            ((clojure.lang.IPersistentSet Nothing))
            #{}

            ((Tuple :klk "YOLO"))
            [:klk "YOLO"]
            
            ([java.lang.String -> (Or nil java.lang.Long)])
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (fn foo [x]
                (parse-int x)))

            ([java.lang.String -> (Or "YOLO" java.lang.Long)])
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (fn foo [x]
                (let [result (parse-int x)]
                  (if result
                    result
                    "YOLO"))))

            ((Fn [clojure.lang.IPersistentMap -> :klk]
                 [(Not clojure.lang.IPersistentMap) -> "manito"]))
            (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                              [(Not clojure.lang.IPersistentMap) -> false]))
              (fn foo [x]
                (if (map? x)
                  :klk
                  "manito")))
            
            ((Fn [clojure.lang.IPersistentMap -> :yolo]
                 [(Not clojure.lang.IPersistentMap) -> "lol"]))
            (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                              [(Not clojure.lang.IPersistentMap) -> false]))
              (fn foo [x]
                (let [? (map? x)]
                  (if ?
                    :yolo
                    "lol"))))

            ((Fn [clojure.lang.IPersistentMap -> "manito"]
                 [(Not clojure.lang.IPersistentMap) -> :klk]))
            (do (ann map? (Fn [clojure.lang.IPersistentMap -> true]
                              [(Not clojure.lang.IPersistentMap) -> false]))
              (fn foo [x]
                (let [x (if (map? x)
                          "manito"
                          :klk)]
                  x)))

            (java.lang.Object)
            (do ;; (ann-class java.lang.String [java.lang.Object])
                (ann foo [java.lang.Object -> java.lang.Object])
              (foo "bar"))

            ((Fn [1 -> "YOLO"]
                 ["2" -> "LOL"]
                 [:3 -> "MEME"]))
            (fn case-test [x]
              (case x
                1   "YOLO"
                "2" "LOL"
                :3  "MEME"))
            
            ((Fn [1 -> "YOLO"] ["2" -> "LOL"] [:3 -> "MEME"] [Any -> "default"]))
            (fn case-test [x]
              (case x
                1   "YOLO"
                "2" "LOL"
                :3  "MEME"
                "default"))

            ((Fn [(Or 1 2 3) -> "YOLO"] ["2" -> "LOL"] [:3 -> "MEME"] [Any -> "default"]))
            (fn case-test [x]
              (case x
                (1 2 3)   "YOLO"
                "2" "LOL"
                :3  "MEME"
                "default"))

            ('yolo)
            'yolo

            ((clojure.lang.PersistentList (Or 1 'dos "tres")))
            '(1 dos "tres")

            (nil)
            (monitor-enter "YOLO")
            
            (nil)
            (monitor-exit "YOLO")
            
            (nil)
            (do (monitor-enter "YOLO")
              (monitor-exit "YOLO"))

            ()
            (monitor-enter nil)

            ()
            (monitor-exit nil)

            ((Eff Nothing {:try java.lang.Exception}))
            (do (ann ex [-> java.lang.Exception])
              (throw (ex)))

            ((Eff 1 {:try java.lang.Exception}))
            (do (ann ex [-> java.lang.Exception])
              (throw (ex))
              1)

            ((Eff :else {:try java.lang.Exception}))
            (do (ann test (Or true false))
              (ann ex [-> java.lang.Exception])
              (let [test* test]
                (if test*
                  (throw (ex))
                  :else)))

            ((Eff :else {:try java.lang.Exception}))
            (do (ann test (Or true false))
              (ann ex [-> java.lang.Exception])
              (let [test* test]
                (try (if test*
                       (throw (ex))
                       :else))))

            ((Or :catch :else))
            (do (ann test (Or true false))
              (ann ex [-> java.lang.Exception])
              (let [test* test]
                (try (if test*
                       (throw (ex))
                       :else)
                  (catch java.lang.Exception e
                    :catch)
                  (finally :finally))))

            ((Eff (Or :catch :else) {:try java.lang.Exception}))
            (do (ann test (Or true false))
              (ann ex [-> java.lang.Exception])
              (let [test* test]
                (try (if test*
                       (throw (ex))
                       :else)
                  (catch java.lang.YoloException e
                    :catch)
                  (finally :finally))))

            ((Eff String {:io IO}))
            (do (ann read-line [-> (Eff String {:io IO})])
              (read-line))

            ((Eff Nothing {:io IO, :try java.lang.Exception}))
            (do (ann ex [-> java.lang.Exception])
              (ann read-line [-> (Eff String {:io IO})])
              (read-line)
              (throw (ex)))

            (1)
            (do (ann global java.lang.String)
              (binding [global "YOLO"]
                1))

            ()
            (do (ann global java.lang.String)
              (binding [global 10]
                1))

            (10)
            (loop [a 10]
              a)

            (java.lang.Long)
            (do (ann + [java.lang.Long java.lang.Long -> java.lang.Long])
              (loop [a 10
                     b 20]
                (+ a b)))

            (Nothing)
            (do (ann inc [java.lang.Long -> java.lang.Long])
              (loop [a 0]
                (recur (inc a))))

            ()
            (do (ann defn Macro)
              defn)

            (10)
            (do (ann defn Macro)
              10)

            ([Map -> Any])
            (fn _ [x]
              (:yolo x))

            (String)
            (do (ann-class Object [])
              (ann-class String [Object])
              (ann-class Integer [Object])
              (ann-class Collection [Object])
              (ann-class Map [Collection])
              (ann get-map [-> Map])
              (ann coll->str [Collection -> String])
              (coll->str (get-map)))

            ({:a 10 :b "YOLO"})
            {:a 10 :b "YOLO"}

            ("YOLO")
            (do (ann identity (All [x] [x -> x]))
              (identity "YOLO"))
            )))

  (run '(do (ann-class String [Object])
          (ann-class Integer [Object])
          (ann-class (Collection x) [Object])
          (ann-class (Map key val) [(Collection (KV key val))])
          (ann get-map [-> (Map String Integer)])
          (ann coll->str [(Collection (KV key val)) -> String])
          (coll->str (get-map))))

  (run '(do (ann identity (All [x] [x -> x]))
          (identity "YOLO")))

  ;; MISSING: assert
  ;; MISSING: Destructuring
  ;; MISSING: Methods & fields for classes
  ;; MISSING: Java interop
  ;; MISSING: Automatically generate Fn types when calling a type-var in fn-call.
  ;; MISSING: Automatically generate Class types when doing unannotated host interop.
  ;; MISSING: Clojure type tags.
  ;; MISSING: Interact with Java reflection & Clojure type annotations.
  ;; MISSING: var-args
  ;; MISSING: macro-expansion.
  ;; MISSING: Scope handling (public vs private)

  ;; MISSING: def(protocol|type|record), proxy & reify
  ;; MISSING: multimethods
  ;; MISSING: gen-class
  ;; MISSING: covariance, contravariance & invariance.
  ;; MISSING: Recursive types
  
  ;; The one below is not supposed to type-check due to lack of
  ;; coverage of type possibilities.
  (run '(do (ann get-object [-> java.lang.Object])
          (ann use-case (Fn [String -> :yolo]
                            [Integer -> :lol]
                            [Boolean -> :meme]))
          (fn foo []
            (use-case (get-object)))))


  ;; Must fix issue with refining in order to get this to type-check.
  (run '(do (ann inc [(Or java.lang.Integer java.lang.Long) -> java.lang.Integer])
          (ann < [java.lang.Long java.lang.Long -> java.lang.Boolean])
          (loop [cnt 0]
            (if (< cnt 10)
              (recur (inc cnt))
              :done))))

  (run '(do (ann map? (Fn [Map -> true]
                          [(Not Map) -> false]))
          (fn foo [x]
            (assert (map? x) "YOLO")
            x)))

  

  ;; Refactorings to do:
  ;; ::expr instead of ::bound to signal a type that has been calculated by the type-checker.
  ;; Eliminate ::bound & ::var.
  ;; Have an ::interval type with local top and bottom as a substitute for type-vars.
  ;; Improve type updating mechanism in recur and allow recur to work with fn.
  ;; Fix issue with refining.
  
  ;; (run '(do (ann ex [-> java.lang.Exception])
  ;;         (if true
  ;;           (throw (ex))
  ;;           :else)))

  ;; (run '(do (ann ex [-> java.lang.Exception])
  ;;         (if false
  ;;           (throw (ex))
  ;;           :else)))

  (run '(do (ann test java.lang.Boolean)
          (ann ex [-> java.lang.Exception])
          (let [test* test]
            (if test*
              (throw (ex))
              :else))))

  (run '(do (ann test java.lang.Boolean)
          (ann ex [-> java.lang.Exception])
          (if test
            :else
            (throw (ex)))))

  

  

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
  )
