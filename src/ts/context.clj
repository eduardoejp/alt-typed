(ns ts.context
  (:refer-clojure :exclude [==])
  (:require [clojure.template :refer [do-template]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.protocols :refer [walk ext-no-check]]
            [ts.util :as &util]))

;; [Constants]
(def +new-context+
  {:env/global {}
   :env/local {}
   :types {}
   :classes/defs {}
   :ns nil
   :ns/all {}
   :context/vars {}
   :context/bindings {}})

;; [Interface]
(do-template [<put> <get> <key>]
  (do (defn <put> [&context &label &datum &new-context]
        (&util/%put! &context [<key> &label] &datum &new-context))
    (defn <get> [&context &label &datum]
      (&util/%get! &context [<key> &label] &datum)))

  %intern-var %find-var   :env/global
  %learn-type %find-type  :types
  %def-class  %find-class :classes/defs
  )

(defn %refine! [&context &id &refined &new-context]
  (&util/%put! &context [:context/bindings &id] &refined &new-context))

(defn %at-local [&context &id &type]
  (&util/%get! &context [:context/bindings &id] &type))

(do-template [<put> <get> <key>]
  (do (defn <put> [&context &label &datum &new-context]
        (fresh [$id $context]
          (== $id (hash $id))
          (&util/%put! &context [:context/bindings $id] &datum $context)
          (&util/%put! $context [<key> &label] [:bound &label $id] &new-context)))
    (defn <get> [&context &label &datum]
      (all (trace-lvars '%find-local &label &context)
           (&util/%get! &context [<key> &label] &datum))))

  %with-local %find-local :env/local)

(do-template [<put> <get> <key>]
  (do (defn <put> [&context &datum &new-context]
        (&util/%put! &context [<key>] &datum &new-context))
    (defn <get> [&context &datum]
      (&util/%get! &context [<key>] &datum)))

  %in-ns      %ns         :ns
  )

(do-template [<put> <test> <key>]
  (do (defn <put> [&context &datum &new-context]
        (fresh [$ns]
          (%ns &context $ns)
          (&util/%put! &context [:ns/all $ns <key> &datum] nil &new-context)))
    (defn <test> [&context &datum]
      (fresh [$ns]
        (%ns &context $ns)
        (&util/%get! &context [:ns/all $ns <key> &datum] nil))))

  %import!    %imports?   :imports
  %refer!     %refers?    :refers
  )

(defn %with-locals [&context &labels &data &new-context]
  (matche [&labels &data]
    ([[] []]
       (== &context &new-context))
    ([[?label . ?rest] [?datum . ?rem]]
       (fresh [$context]
         (%with-local &context ?label ?datum $context)
         (%with-locals $context ?rest ?rem &new-context)))
    ))
