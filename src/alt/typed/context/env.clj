(ns alt.typed.context.env)

;; [Protocols]
(defprotocol $Environment
  (bind [env symbol graph-cell-id])
  (lookup [env symbol]))

;; [Implementations]
(defrecord Environment [_store]
  $Environment
  (bind [self symbol graph-cell-id]
    (assoc-in self [:_store symbol] graph-cell-id))
  (lookup [self symbol]
    (get _store symbol)))

;; [Constants]
(def +new-env+
  (Environment. (hash-map)))
