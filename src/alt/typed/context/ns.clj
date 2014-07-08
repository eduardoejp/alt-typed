(ns alt.typed.context.ns
  (:refer-clojure :exclude [refer intern ns-name resolve import])
  (:require (clojure [string :as string]
                     [set :as set])
            [alt.typed.util :as &util]))

;; [Protocols]
(defprotocol $Reference
  (refers-to [refer])
  (referred-as [refer])
  (local? [refer symbol])
  (recognize [refer symbol])
  )

(defprotocol $NS
  (ns-name [ns])
  (common-name [ns sym])
  (ns-alias [ns real-ns])
  (ns-import [ns class-name])
  (public-vars [ns])
  (refer [self namespace alias only exclude rename])
  (import [ns class-name])
  (intern [ns var-name])
  (resolve [ns symbol])
  )

;; [Implementations]
(defrecord Reference [ns alias direct-syms all-syms]
  $Reference
  (refers-to [self]
    ns)
  (referred-as [self]
    alias)
  (local? [refer symbol]
    (contains? direct-syms symbol))
  (recognize [self sym]
    ;; (prn 'Reference/recognize sym ns alias direct-syms all-syms)
    (if-let [direct-name (get direct-syms sym)]
      (symbol (name ns) (name direct-name))
      (let [sym-ns (namespace sym)
            sym-name (name sym)]
        (if (and sym-ns
                 (contains? all-syms (symbol sym-name))
                 (contains? #{ns alias} (symbol sym-ns)))
          (symbol (name ns) sym-name)))))
  )

(defrecord NS [_ns-name _refers _imports _vars]
  $NS
  (ns-name [self]
    _ns-name)
  (common-name [self sym]
    (assert (namespace sym))
    ;; (prn 'common-name _ns-name sym)
    (let [real-ns (-> sym namespace symbol)
          real-name (-> sym name symbol)]
      (if (= real-ns _ns-name)
        real-name
        (some (fn [refer] (if (= real-ns (refers-to refer))
                           (if (local? refer real-name)
                             real-name
                             (symbol (name (referred-as refer)) (name real-name)))))
              _refers))))
  (ns-alias [self real-ns]
    (some (fn [refer] (if (= real-ns (refers-to refer)) (referred-as refer)))
          _refers))
  (ns-import [self class-name]
    (get (set/map-invert _imports) class-name))
  (public-vars [self]
    _vars)
  (refer [self namespace alias only exclude rename]
    (assert (not (some (comp (partial = alias) referred-as) _refers))
            ;; (<< "#{_ns-name} can't re-use alias \"#{alias}\" for #{namespace}.")
            [(str "Can't re-use the same alias to for another namespace.")
             {:ns _ns-name, :refer namespace, :alias alias}])
    (let [ns-name (ns-name namespace)
          all-syms (public-vars namespace)
          direct-syms* (cond (not (empty? exclude))
                             (set/difference all-syms exclude)

                             (nil? only)
                             all-syms

                             :else
                             (set/intersection all-syms (set/union (set only)
                                                                   (set (keys rename)))))
          direct-syms (into {} (for [sym direct-syms*
                                     :let [sym* (get rename sym sym)]]
                                 [sym* sym]))]
      (update-in self [:_refers] conj (Reference. ns-name alias direct-syms all-syms))))
  (import [self class-name]
    (assert (string? class-name))
    (let [parts (string/split class-name #"\.")
          simple-name (symbol (last parts))
          full-name (symbol class-name)]
      (update-in self [:_imports] assoc simple-name full-name)))
  (intern [self var-name]
    (update-in self [:_vars] conj var-name))
  (resolve [self sym]
    ;; (prn 'NS/resolve sym _ns-name
    ;;      ;; (map (fn [r] [(referred-as r) (refers-to r)])
    ;;      ;;      _refers)
    ;;      ;; _imports
    ;;      _vars)
    (or (get _imports sym)
        (if (&util/fully-qualified-class? sym)
          sym)
        (if-let [ns (namespace sym)]
          (if (= _ns-name (symbol ns))
            sym))
        (if (contains? _vars sym)
          (symbol (name _ns-name) (name sym)))
        (some #(recognize % sym) _refers)))
  )

;; [Functions]
(defn make-ns [ns-sym]
  (NS. ns-sym [] {} #{}))
