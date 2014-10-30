(ns system
  (:require [clojure.template :refer [do-template]]
            (system [util :as &util :refer [state-seq-m exec
                                            map-m reduce-m
                                            zero return return-all]]
                    [type :as &type]
                    [parser :as &parser]
                    [type-checker :as &type-checker]
                    [translator :as &translator])
            ;; :reload-all
            :reload
            ))

(comment
  (time (do (defonce _init_
              (do (alter-var-root #'clojure.core/prn
                                  (constantly #(.println System/out (apply pr-str %&))))))
          
          (defn run [code]
            (println "Code:" (pr-str code))
            (let [monad (exec state-seq-m
                          [parsed-code (&parser/parse code)]
                          (&type-checker/check parsed-code))
                  types (map (comp &translator/type->code second)
                             (monad &type-checker/+init+))]
              (doseq [type types]
                (->> type pr-str (println "Type:")))
              (println "")
              types))
          
          (do-template [<type> <form>]
            (assert (= '(<type>) (run '<form>)))
            
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
            1/2

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
              #'foo)

            (Or nil java.lang.Long)
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (parse-int "1234"))

            nil
            (defalias (Maybe x) (Or nil x))

            (Or "YOLO" java.lang.Long)
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (let [result (parse-int "1234")]
                (if result
                  result
                  "YOLO")))

            (All [a] [a -> a])
            (fn foo [x] x)

            (clojure.lang.IPersistentVector Nothing)
            []

            (clojure.lang.IPersistentMap Nothing Nothing)
            {}

            (clojure.lang.IPersistentSet Nothing)
            #{}

            (clojure.lang.IPersistentVector (Or :klk "YOLO"))
            [:klk "YOLO"]
            
            [java.lang.String -> (Or nil java.lang.Long)]
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
              (fn foo [x]
                (parse-int x)))

            [java.lang.String -> (Or "YOLO" java.lang.Long)]
            (do (ann parse-int [java.lang.String -> (Or nil java.lang.Long)])
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
            (do (ann-class java.lang.String [java.lang.Object])
              (ann foo [java.lang.Object -> java.lang.Object])
              (foo "bar"))

            (Fn [1 -> "YOLO"]
                ["2" -> "LOL"]
                [:3 -> "MEME"])
            (fn case-test [x]
              (case x
                1   "YOLO"
                "2" "LOL"
                :3  "MEME"))
            
            (Fn [1 -> "YOLO"]
                ["2" -> "LOL"]
                [:3 -> "MEME"]
                [Any -> "default"])
            (fn case-test [x]
              (case x
                1   "YOLO"
                "2" "LOL"
                :3  "MEME"
                "default"))

            (Fn [(Or 1 2 3) -> "YOLO"]
                ["2" -> "LOL"]
                [:3 -> "MEME"]
                [Any -> "default"])
            (fn case-test [x]
              (case x
                (1 2 3)   "YOLO"
                "2" "LOL"
                :3  "MEME"
                "default"))
            )))

  (run '(do (ann-class String [Object])
          (ann-class Integer [Object])
          (ann-class (Collection x) [Object])
          (ann-class (Map key val) [(Collection (KV key val))])
          (ann get-map [-> (Map String Integer)])
          (ann coll->str [(Collection (KV key val)) -> String])
          (coll->str (get-map))))

  (run '(do (ann ex-info [java.lang.String (clojure.lang.IPersistentMap Any Any) -> java.lang.Exception])
          (throw (ex-info "YOLO" {}))))

  

  ;; MISSING: class conversions
  ;; MISSING: throw, try, catch, finally
  
  ;; MISSING: loop, recur
  
  ;; MISSING: Java interop
  ;; MISSING: binding
  
  ;; MISSING: ns management
  ;; MISSING: records & tuples
  
  ;; MISSING: treating objects as IFn (like keywords & maps)
  ;; MISSING: quote
  
  ;; MISSING: def(protocol|type|record)
  ;; MISSING: proxy & reify

  ;; MISSING: monitor-enter & monitor-leave
  ;; MISSING: multimethods

  ;; MISSING: prelude
  ;; MISSING: gen-class
  

  ;; The one below is not supposed to type-check due to lack of
  ;; coverage of type possibilities.
  (run '(do (ann get-object [-> java.lang.Object])
          (ann use-case (Fn [String -> :yolo]
                            [Integer -> :lol]
                            [Boolean -> :meme]))
          (fn foo []
            (use-case (get-object)))))

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
