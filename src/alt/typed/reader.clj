(ns alt.typed.reader
  (:require [clojure.string :as string]
            [clojure.java.io :as io])
  (:import (java.io FileReader
                    InputStreamReader)
           (java.util.zip ZipFile)
           (clojure.lang LineNumberingPushbackReader
                         LispReader
                         LispReader$ReaderException
                         Compiler
                         RT
                         IObj
                         Var
                         IMapEntry)))

;; [Utils]
(defn ^:private namespace->file-path [namespace]
  (-> namespace str (string/replace #"\." "/") (str ".clj")))

;; [Functions]
(defn original-form [form]
  (or (-> form meta ::form)
      form))

(defn source [form]
  (-> form meta ::source))

(let [forms-to-ignore #{'quote 'clojure.core/assert 'clojure.core/defprotocol}]
  (defn macroexpand-all* [form & [parent-metadata]]
    (let [form-meta (merge (select-keys parent-metadata [:line :column])
                           (meta form)
                           {::form form})
          inner #(macroexpand-all* % form-meta)
          form* (loop [form form]
                  (if (and (seq? form)
                           (contains? forms-to-ignore (first form)))
                    form
                    (let [form* (macroexpand-1 form)]
                      (if (= form* form)
                        form
                        (recur form*)))))
          form** (cond (instance? IMapEntry form*) (mapv inner form*)
                       (list? form*)               (apply list (map inner form*))
                       (seq? form*)                (if (contains? forms-to-ignore (first form*))
                                                     form*
                                                     (doall (map inner form*)))
                       (coll? form*)               (into (empty form*) (map inner form*))
                       :else                       form*)]
      (if (instance? IObj form**)
        (with-meta form** form-meta)
        form**))))

;; (ann get-reader [String -> (Maybe LineNumberingPushbackReader)])
(defn ^:private get-reader ^LineNumberingPushbackReader [^String source-path]
  (if (.contains source-path ".jar!/")
    (when-let [[_ ^String path sub-path] (re-find #"^file:(.+)!/(.+)$" source-path)]
      (let [jar-file (ZipFile. path)
            source-entry (.getEntry jar-file sub-path)]
        (LineNumberingPushbackReader. (InputStreamReader. (.getInputStream jar-file source-entry)))))
    (LineNumberingPushbackReader. (FileReader. source-path))))

;; [Procedures]
(defn read-ns [namespace]
  (let [source (namespace->file-path namespace)
        source-path (.getFile (io/resource source))
        +eof+ (Object.)]
    (with-open [reader (get-reader source-path)]
      (Var/pushThreadBindings (RT/mapUniqueKeys (to-array [Compiler/LOADER         (RT/makeClassLoader)
                                                           Compiler/SOURCE_PATH    source-path
                                                           Compiler/SOURCE         source
                                                           Compiler/METHOD         nil
                                                           Compiler/LOCAL_ENV      nil
                                                           Compiler/LOOP_LOCALS    nil
                                                           Compiler/NEXT_LOCAL_NUM 0
                                                           RT/READEVAL             RT/T
                                                           RT/CURRENT_NS           (.deref RT/CURRENT_NS)
                                                           Compiler/LINE_BEFORE    (.getLineNumber reader)
                                                           Compiler/COLUMN_BEFORE  (.getColumnNumber reader)
                                                           Compiler/LINE_AFTER     (.getLineNumber reader)
                                                           Compiler/COLUMN_AFTER   (.getColumnNumber reader)
                                                           RT/UNCHECKED_MATH       (.deref RT/UNCHECKED_MATH)
                                                           RT/DATA_READERS         (.deref RT/DATA_READERS)])))
      (try (loop [exprs []]
             (let [expr (LispReader/read reader false +eof+ false)]
               (if (= +eof+ expr)
                 exprs
                 (do (.set Compiler/LINE_AFTER (.getLineNumber reader))
                   (.set Compiler/COLUMN_AFTER (.getColumnNumber reader))
                   (.set Compiler/LINE_BEFORE (.getLineNumber reader))
                   (.set Compiler/COLUMN_BEFORE (.getColumnNumber reader))
                   (recur (conj exprs expr))))))
        (catch LispReader$ReaderException e
          (throw (ex-info "Error while reading namespace." {:source source
                                                            :exception e})))
        (finally (Var/popThreadBindings))))
    ))

(comment
  (.getFile (io/resource (namespace->file-path "clojure.core")))
  "file:/home/eduardoejp/.m2/repository/org/clojure/clojure/1.5.1/clojure-1.5.1.jar!/clojure/core.clj"
  )
