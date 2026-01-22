(ns debug
  (:require [cljs.analyzer :as ana]
            [cljs.compiler :as comp]
            [cljs.env :as env]))

(def cenv (env/default-compiler-env))

;; Initialize cljs.core so macros work
(env/with-compiler-env cenv
  (ana/analyze-file "cljs/core.cljs"))

(defn analyze [env form]
  (env/ensure (ana/analyze env form)))

(defn emit [ast]
  (env/ensure (comp/emit ast)))

(def aenv (assoc-in (ana/empty-env) [:ns :name] 'cljs.user))

(defn cljs->js [form]
  (env/with-compiler-env cenv
    (binding [ana/*cljs-ns* 'cljs.user]
      (with-out-str
        (emit (analyze aenv form))))))

;; Test with macros
(println "=== (let [x (if true 1 2)] x) ===")
(println (cljs->js '(def x (let [x (if (odd? 1) 1 2)] x))))

(println "\n=== (fn [c] (let [x (if c 1 2)] x)) ===")
(println (cljs->js '(set! x (fn [c] (let [x (if c 1 2)] x)))))

(println "\n=== (let [y (let [x 1] x)] y) ===")
(println (cljs->js '(let [y (let [x 1] x)] y)))

(println "\n=== Nested let with if ===")
(println (cljs->js '(let [y (let [x (if (odd? 1) 1 2)] x)] y)))

(println "\n=== binding ===")
(println (cljs->js '(def x (fn []
                             (binding [*print-fn* *print-fn*]
                               (let [x 1] nil))))))
