(ns alt.typed.syntax.representation)

;; [Records]
(defrecord Literal [value])

(defrecord Identifier [name])

(defrecord TypeCtorCall [ctor args])

(defrecord TypeVar [name type])

(defrecord Arity [args return])

(defrecord Fn [arities])

(defrecord Or [types])

(defrecord Not [type])

(defrecord All [vars type])

(defrecord Rec [self type])
