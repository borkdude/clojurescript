;; Copyright (c) Rich Hickey. All rights reserved.
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;; which can be found in the file epl-v10.html at the root of this distribution.
;; By using this software in any fashion, you are agreeing to be bound by
;; the terms of this license.
;; You must not remove this notice, or any other, from this software.

(ns cljs.analyzer.passes.anf
  "ANF (A-Normal Form) pass that lifts statement-like forms out of expression
   position to avoid IIFE generation in the compiler.

   For example:
     (f (let [x 1] (inc x)))
   becomes:
     (let [x 1 G__1 (inc x)] (f G__1))

   This eliminates the need for (function(){ var x = 1; return x + 1; })()
   in the generated JavaScript.")

;; Ops that cause IIFE when in :expr context (from compiler.cljc)
(def statement-ops
  #{:let :loop :try :letfn :throw})

(defn- expr-context? [ast]
  (= :expr (-> ast :env :context)))

(defn- needs-lifting? [ast]
  (and (expr-context? ast)
       (or (contains? statement-ops (:op ast))
           ;; :do with statements needs IIFE in :expr context
           (and (= :do (:op ast))
                (seq (:statements ast))))))

;; --- AST node constructors ---

(defn- make-binding
  "Create a :binding AST node for use in a synthetic let."
  [name-sym init-ast]
  {:op :binding
   :name name-sym
   :form name-sym
   :init init-ast
   :tag (:tag init-ast)
   :local :let
   :shadow nil
   :env (select-keys (:env init-ast) [:line :column])
   :info {:name name-sym
          :shadow nil}
   :binding-form? true
   :children [:init]})

(defn- make-local-ref
  "Create a :local AST node referencing a binding."
  [name-sym tag env]
  {:op :local
   :name name-sym
   :form name-sym
   :env (assoc env :context :expr)
   :tag tag
   :local :let
   :info {:name name-sym}
   :children []})

(defn- let-body
  "Extract the return value of a :let body (unwrapping :do if no statements)."
  [let-ast]
  (let [body (:body let-ast)]
    (if (and (= :do (:op body))
             (empty? (:statements body)))
      (:ret body)
      body)))

(defn- wrap-in-let
  "Wrap an AST node in a :let with the given bindings."
  [bindings body-ast env]
  (let [body-wrapped {:op :do
                      :env (:env body-ast)
                      :statements []
                      :ret body-ast
                      :form (:form body-ast)
                      :children [:statements :ret]
                      :body? true}]
    {:op :let
     :env env
     :bindings (vec bindings)
     :body body-wrapped
     :form nil
     :children [:bindings :body]}))

;; --- Lifting logic ---

(defn- ->expr-env
  "Change an AST node's context to :expr."
  [ast]
  (assoc-in ast [:env :context] :expr))

(defn- extract-let-bindings
  "Given a :let AST in expr context, extract its bindings and body.
   Returns [bindings body-ast] where body-ast replaces the original let."
  [let-ast result-env]
  (let [inner-bindings (:bindings let-ast)
        body (-> (let-body let-ast) ->expr-env)
        ;; Generate a fresh symbol for the let's result
        result-sym (gensym "anf__")
        result-binding (make-binding result-sym body)
        all-bindings (conj inner-bindings result-binding)
        local-ref (make-local-ref result-sym (:tag body) result-env)]
    [all-bindings local-ref]))

(defn- extract-do-bindings
  "Given a :do AST with statements in expr context, extract statements
   as side-effect bindings and the ret value.
   Returns [bindings body-ast]."
  [do-ast result-env]
  ;; For a do with statements, we need to hoist the statements.
  ;; We wrap each statement as a binding with a dummy name (value discarded).
  ;; The ret becomes the replacement expression.
  ;; Actually, we can't easily represent side-effect-only statements as let bindings.
  ;; Instead, we extract the ret and wrap the whole thing:
  ;; (f (do stmt ret)) -> (do stmt (f ret))
  ;; But that changes the parent structure, which is harder in a pass.
  ;; Simpler: treat the whole do as a value and bind it.
  (let [result-sym (gensym "anf__")
        ;; Change the do's context from :expr to :return so it won't IIFE
        ;; when emitted as a let binding init (let bindings are :expr context
        ;; but emit-let handles them without IIFE)
        result-binding (make-binding result-sym do-ast)
        local-ref (make-local-ref result-sym (:tag (:ret do-ast)) result-env)]
    [[result-binding] local-ref]))

(defn- lift-arg
  "If an invoke arg needs lifting, extract bindings and return [bindings replacement].
   Otherwise returns [nil arg]."
  [arg result-env]
  (if (needs-lifting? arg)
    (case (:op arg)
      :let (extract-let-bindings arg result-env)
      (:loop :try :letfn :throw)
      (let [result-sym (gensym "anf__")
            result-binding (make-binding result-sym arg)
            local-ref (make-local-ref result-sym (:tag arg) result-env)]
        [[result-binding] local-ref])
      ;; :do with statements
      (extract-do-bindings arg result-env))
    [nil arg]))

;; --- Per-op optimizers ---

(defn- optimize-invoke
  "Lift statement-ops out of :invoke args."
  [ast]
  (let [args (:args ast)
        env (:env ast)]
    (if (some needs-lifting? args)
      (let [results (mapv #(lift-arg % env) args)
            all-bindings (into [] (mapcat first) results)
            new-args (mapv second results)
            new-invoke (assoc ast :args new-args)]
        (wrap-in-let all-bindings new-invoke env))
      ast)))

(defn- optimize-let-bindings
  "Flatten nested :let in binding inits.
   (let [y (let [x 1] x)] ...) -> (let [x 1 y x] ...)"
  [ast]
  (let [bindings (:bindings ast)]
    (if (some #(and (= :let (:op (:init %)))
                    (expr-context? (:init %)))
              bindings)
      (let [new-bindings
            (reduce
              (fn [acc binding]
                (let [init (:init binding)]
                  (if (and (= :let (:op init))
                           (expr-context? init))
                    ;; Flatten: add inner bindings, then bind name to inner body
                    (let [inner-bindings (:bindings init)
                          inner-body (-> (let-body init) ->expr-env)
                          outer-binding (assoc binding :init inner-body)]
                      (into acc (conj inner-bindings outer-binding)))
                    (conj acc binding))))
              []
              bindings)]
        (assoc ast :bindings new-bindings))
      ast)))

;; --- Main pass entry point ---

(defn optimize [env ast _]
  (case (:op ast)
    :invoke (optimize-invoke ast)
    :let (optimize-let-bindings ast)
    ast))
