;; Copyright (c) Rich Hickey. All rights reserved.
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;; which can be found in the file epl-v10.html at the root of this distribution.
;; By using this software in any fashion, you are agreeing to be bound by
;; the terms of this license.
;; You must not remove this notice, or any other, from this software.

(ns cljs.anf
  "ANF (A-Normal Form) transformation on s-expressions.
   Lifts IIFE-causing forms (let*, loop*, try, letfn*) out of
   expression position to avoid IIFE generation in the compiler.

   For example:
     (f (let [x 1] (inc x)))
   becomes:
     (let* [x 1 G__1 (inc x)] (f G__1))

   Expects ::get-expander in env for macro expansion.
   Tracks locals to avoid expanding locally-bound symbols.")

;; Special forms that should not be macroexpanded
(def ^:private specials
  '#{if def fn* do let* loop* letfn* throw try recur new set!
     ns deftype* defrecord* . js* & quote case* var ns* await})

(defn- preserve-meta
  "Transfer metadata from original form to rebuilt form.
   Merges metadata so inner type tags (e.g. :tag 'boolean from bool-expr)
   are not overwritten by outer source location metadata.
   Only applies when rebuilt supports metadata (not primitives like strings/numbers)."
  [original rebuilt]
  (if-let [m (meta original)]
    (if (instance? #?(:clj clojure.lang.IObj :cljs cljs.core/IWithMeta) rebuilt)
      (with-meta rebuilt (merge (meta rebuilt) m))
      rebuilt)
    rebuilt))

(defn- needs-lifting?
  "Returns true if form would cause an IIFE when compiled in expression position."
  [form]
  (and (seq? form)
       (contains? #{'let* 'loop* 'try 'letfn*} (first form))))

(defn- do-with-statements?
  "Returns true if form is a do with 2+ sub-forms (causes IIFE in expr position)."
  [form]
  (and (seq? form)
       (= 'do (first form))
       (> (count (rest form)) 1)))

(defn- if-with-iife-branch?
  "Returns true if form is an if where any branch needs-lifting? or is
   itself an if-with-iife-branch? (handles nested if with IIFE branches)."
  [form]
  (and (seq? form)
       (= 'if (first form))
       (let [[_ _test then else] form]
         (or (needs-lifting? then)
             (needs-lifting? else)
             (do-with-statements? then)
             (do-with-statements? else)
             (if-with-iife-branch? then)
             (if-with-iife-branch? else)))))

(declare transform)

(defn- replace-sym
  "Replace all occurrences of symbol old with new in form."
  [form old new]
  (cond
    (and (symbol? form) (= form old)) new
    (seq? form) (with-meta (doall (map #(replace-sym % old new) form)) (meta form))
    (vector? form) (mapv #(replace-sym % old new) form)
    (map? form) (into {} (map (fn [[k v]] [k (replace-sym v old new)]) form))
    (set? form) (set (map #(replace-sym % old new) form))
    :else form))

(defn- rename-inner-bindings
  "Rename binding symbols that conflict with existing locals to gensyms.
   Returns [new-bindings new-body] with conflicting references substituted."
  [locals inner-bindings body]
  (let [pairs (partition 2 inner-bindings)]
    (loop [pairs pairs
           renames {}
           out-bindings []]
      (if-let [[sym init] (first pairs)]
        (let [init (reduce-kv (fn [form old new] (replace-sym form old new))
                     init renames)
              conflicts? (contains? locals sym)
              new-sym (if conflicts? (gensym (str (name sym) "__")) sym)
              renames (if conflicts? (assoc renames sym new-sym) renames)]
          (recur (rest pairs) renames (conj out-bindings new-sym init)))
        (let [new-body (reduce-kv (fn [form old new] (replace-sym form old new))
                         body renames)]
          [out-bindings new-body])))))

(defn- flatten-nested-lets
  "Recursively extract bindings from nested let* bodies.
   Returns [all-bindings final-body] where final-body is not a let*."
  [locals bindings body]
  (if (and (seq? body) (= 'let* (first body)))
    (let [[_ inner-bindings & inner-body] body
          body-form (if (= 1 (count inner-body))
                      (first inner-body)
                      (cons 'do inner-body))
          [renamed-bindings renamed-body] (rename-inner-bindings locals inner-bindings body-form)
          inner-syms (take-nth 2 renamed-bindings)]
      (flatten-nested-lets (into locals (set inner-syms))
                           (into bindings renamed-bindings)
                           renamed-body))
    [bindings body]))

(defn- wrap-in-assign
  "Wrap the result of form in a js* assignment to sym.
   For let*, places the assignment on the body's last expression
   so the let* stays in statement position (no IIFE).
   For if, pushes the assignment into each branch to keep them
   in statement position.
   Renames inner bindings that shadow sym to avoid wrong assignment target."
  [sym form]
  (cond
    (and (seq? form) (= 'let* (first form)))
    (let [[_ bindings & body] form
          binding-syms (set (take-nth 2 bindings))
          body-form (if (= 1 (count body)) (first body) (cons 'do body))
          ;; Rename any inner bindings that shadow the assignment target
          [bindings body-form] (if (contains? binding-syms sym)
                                 (rename-inner-bindings #{sym} bindings body-form)
                                 [bindings body-form])
          body-vec (if (and (seq? body-form) (= 'do (first body-form)))
                     (vec (rest body-form))
                     [body-form])
          last-expr (peek body-vec)
          init-stmts (pop body-vec)]
      (apply list 'let* (vec bindings)
        (conj init-stmts (wrap-in-assign sym last-expr))))

    (and (seq? form) (= 'if (first form)))
    (let [[_ test then else] form]
      (if (> (count form) 3)
        (list 'if test (wrap-in-assign sym then) (wrap-in-assign sym else))
        (list 'if test (wrap-in-assign sym then))))

    (and (seq? form) (= 'do (first form)))
    (let [do-forms (vec (rest form))
          init-stmts (pop do-forms)
          last-expr (peek do-forms)]
      (apply list 'do (conj init-stmts (wrap-in-assign sym last-expr))))

    :else
    (list 'js* "(~{} = ~{})" sym form)))

(defn- lift-args
  "Given a list of transformed args, extract any IIFE-causing forms into
   let* bindings. Returns [bindings stmts new-args].
   For let*, flattens by hoisting inner bindings (renaming conflicts with
   locals to avoid shadowing). For if with IIFE branches, uses declare-assign
   pattern with js*. For other forms, binds the whole form to a gensym."
  [locals args]
  (reduce
    (fn [[bindings stmts new-args] arg]
      ;; Unwrap do-with-statements: hoist stmts into stmts accumulator,
      ;; then process last-expr through the normal cond
      (let [[stmts arg] (if (do-with-statements? arg)
                           (let [do-forms (vec (rest arg))
                                 do-stmts (pop do-forms)
                                 last-expr (peek do-forms)]
                             [(into stmts do-stmts) last-expr])
                           [stmts arg])]
        (cond
          (needs-lifting? arg)
          (if (= 'let* (first arg))
            ;; Flatten let*: hoist its bindings, use body directly if trivial
            (let [[_ inner-bindings & body] arg
                  body-form (if (= 1 (count body))
                              (first body)
                              (cons 'do body))
                  [renamed-bindings renamed-body] (rename-inner-bindings locals inner-bindings body-form)]
              (if (needs-lifting? renamed-body)
                ;; Body itself needs lifting — bind to gensym
                (let [result-sym (gensym "anf__")]
                  [(-> bindings
                       (into renamed-bindings)
                       (conj result-sym renamed-body))
                   stmts
                   (conj new-args result-sym)])
                ;; Body is trivial — use directly as arg
                [(into bindings renamed-bindings)
                 stmts
                 (conj new-args renamed-body)]))
            ;; Other IIFE-causing forms: bind whole thing to gensym
            (let [result-sym (gensym "anf__")]
              [(conj bindings result-sym arg)
               stmts
               (conj new-args result-sym)]))

          (if-with-iife-branch? arg)
          ;; Declare-assign: declare tmp, use if-as-statement with js* assignments
          (let [tmp (gensym "anf__")
                [_ test then else] arg]
            [(conj bindings tmp (list 'js* "void 0"))
             (conj stmts (if (> (count arg) 3)
                           (list 'if test
                                 (wrap-in-assign tmp then)
                                 (wrap-in-assign tmp else))
                           (list 'if test
                                 (wrap-in-assign tmp then))))
             (conj new-args tmp)])

          :else
          [bindings stmts (conj new-args arg)])))
    [[] [] []]
    args))

(defn- transform-args
  "Transform function call args. If any transformed arg is IIFE-causing
   or is an if with IIFE branches, extract into surrounding let* bindings.
   If-with-IIFE-branches uses declare-assign pattern with js*.
   Preserves metadata from the original form on the rebuilt call."
  [env locals form op args]
  (let [transformed (doall (map #(transform env locals %) args))]
    (if (or (some needs-lifting? transformed)
            (some if-with-iife-branch? transformed)
            (some do-with-statements? transformed))
      (let [[bindings stmts new-args] (lift-args locals transformed)]
        (apply list 'let* (vec bindings)
               (concat stmts [(preserve-meta form (cons op new-args))])))
      (preserve-meta form (cons op transformed)))))

(defn- transform-let*
  "Transform let* form: recursively transform binding inits and body.
   Flattens nested let* in binding inits to avoid IIFEs.
   Inner bindings are renamed to gensyms to prevent shadowing.
   If-with-IIFE-branches in binding inits use declare-assign pattern:
   the let* is split, with the if-as-statement in the body."
  [env locals bindings body]
  (let [pairs (partition 2 bindings)]
    (loop [pairs pairs
           acc []
           current-locals locals]
      (if-let [[sym init] (first pairs)]
        (let [t-init (transform env current-locals init)]
          (cond
            ;; Flatten nested let*
            (and (seq? t-init) (= 'let* (first t-init)))
            (let [[_ inner-bindings & inner-body] t-init
                  body-form (if (= 1 (count inner-body))
                              (first inner-body)
                              (cons 'do inner-body))
                  [initial-bindings initial-body] (rename-inner-bindings current-locals inner-bindings body-form)
                  ;; Recursively flatten nested let* in body
                  [renamed-bindings renamed-body] (flatten-nested-lets
                                                    (into current-locals (set (take-nth 2 initial-bindings)))
                                                    (vec initial-bindings)
                                                    initial-body)
                  inner-syms (take-nth 2 renamed-bindings)]
              (cond
                ;; Flattened body is if-with-IIFE-branch → declare-assign, split let*
                (if-with-iife-branch? renamed-body)
                (let [new-locals (into (conj current-locals sym) inner-syms)
                      [_ test then else] renamed-body
                      if-stmt (if (> (count renamed-body) 3)
                                (list 'if test
                                      (wrap-in-assign sym then)
                                      (wrap-in-assign sym else))
                                (list 'if test
                                      (wrap-in-assign sym then)))
                      remaining (vec (mapcat identity (rest pairs)))
                      inner (if (seq remaining)
                              (transform-let* env new-locals remaining body)
                              (let [t-body (doall (map #(transform env new-locals %) body))]
                                (if (= 1 (count t-body))
                                  (first t-body)
                                  (cons 'do t-body))))]
                  (apply list 'let* (vec (-> acc (into renamed-bindings) (conj sym (list 'js* "void 0"))))
                         if-stmt
                         (if (and (seq? inner) (= 'do (first inner)))
                           (rest inner)
                           [inner])))

                ;; Body is do-with-statements → split with declare-assign
                (do-with-statements? renamed-body)
                (let [do-forms (vec (rest renamed-body))
                      stmts (pop do-forms)
                      last-expr (peek do-forms)
                      new-locals (into (conj current-locals sym) inner-syms)
                      remaining (vec (mapcat identity (rest pairs)))
                      inner (if (seq remaining)
                              (transform-let* env new-locals remaining body)
                              (let [t-body (doall (map #(transform env new-locals %) body))]
                                (if (= 1 (count t-body))
                                  (first t-body)
                                  (cons 'do t-body))))]
                  (apply list 'let* (vec (-> acc (into renamed-bindings) (conj sym (list 'js* "void 0"))))
                         (concat stmts
                                 [(wrap-in-assign sym last-expr)]
                                 (if (and (seq? inner) (= 'do (first inner)))
                                   (rest inner)
                                   [inner]))))

                ;; Normal flatten: recur
                :else
                (recur (rest pairs)
                       (-> acc (into renamed-bindings) (conj sym renamed-body))
                       (into (conj current-locals sym) inner-syms))))

            ;; If with IIFE branches → declare-assign, split let*
            (if-with-iife-branch? t-init)
            (let [new-locals (conj current-locals sym)
                  [_ test then else] t-init
                  if-stmt (if (> (count t-init) 3)
                            (list 'if test
                                  (wrap-in-assign sym then)
                                  (wrap-in-assign sym else))
                            (list 'if test
                                  (wrap-in-assign sym then)))
                  ;; Process remaining bindings + body as inner let* or just body
                  remaining (vec (mapcat identity (rest pairs)))
                  inner (if (seq remaining)
                          (transform-let* env new-locals remaining body)
                          (let [t-body (doall (map #(transform env new-locals %) body))]
                            (if (= 1 (count t-body))
                              (first t-body)
                              (cons 'do t-body))))]
              (apply list 'let* (vec (conj acc sym (list 'js* "void 0")))
                     if-stmt
                     (if (and (seq? inner) (= 'do (first inner)))
                       (rest inner)
                       [inner])))

            ;; do-with-statements in binding init → split: stmts in body, assign last-expr
            (do-with-statements? t-init)
            (let [do-forms (vec (rest t-init))
                  do-stmts (pop do-forms)
                  last-expr (peek do-forms)
                  new-locals (conj current-locals sym)
                  remaining (vec (mapcat identity (rest pairs)))
                  inner (if (seq remaining)
                          (transform-let* env new-locals remaining body)
                          (let [t-body (doall (map #(transform env new-locals %) body))]
                            (if (= 1 (count t-body))
                              (first t-body)
                              (cons 'do t-body))))]
              (apply list 'let* (vec (conj acc sym (list 'js* "void 0")))
                     (concat do-stmts
                             [(wrap-in-assign sym last-expr)]
                             (if (and (seq? inner) (= 'do (first inner)))
                               (rest inner)
                               [inner]))))

            ;; Normal binding
            :else
            (recur (rest pairs)
                   (conj acc sym t-init)
                   (conj current-locals sym))))
        ;; Done — build final let*
        (let [t-body (doall (map #(transform env current-locals %) body))]
          (apply list 'let* (vec acc) t-body))))))

(defn- try-macroexpand-1
  "Attempt to macroexpand form once using ::get-expander from env.
   Merges ANF-tracked locals into env so macros like reify see them.
   Returns original form if no expander or expansion fails."
  [env locals form]
  (if-let [get-exp (::get-expander env)]
    (let [op (first form)
          ;; Merge ANF-tracked locals into :locals so macros see them
          env (update env :locals
                (fn [m]
                  (reduce (fn [m sym]
                            (if (contains? m sym) m (assoc m sym {:name sym})))
                    (or m {}) locals)))]
      (if-let [mac-var (when (symbol? op) (get-exp op env))]
        (try
          (apply #?(:clj @mac-var :cljs mac-var) form env (rest form))
          (catch #?(:clj Throwable :cljs :default) _
            form))
        form))
    form))

(defn transform
  "Walk an s-expression and lift IIFE-causing forms out of expression position.
   Macroexpands forms using ::get-expander from env.

   env    - ClojureScript analyzer env with ::get-expander for expansion
   locals - set of locally-bound symbols (not macroexpanded)"
  [env locals form]
  (cond
    (seq? form)
    (if-not (seq form)
      form ;; empty list — return as-is
      (let [op (first form)
            ;; Try to macroexpand if not a special form and not locally bound
            expanded (if (and (symbol? op)
                             (not (contains? specials op))
                             (not (contains? locals op)))
                      (try-macroexpand-1 env locals form)
                      form)]
        (if (not= expanded form)
          ;; Macro expanded — recurse on expanded form, preserving original metadata
          (preserve-meta form (transform env locals expanded))
          ;; No expansion — handle by form type
          (case op
            let* (let [[_ bindings & body] form]
                   (transform-let* env locals bindings body))
            loop* (let [[_ bindings & body] form
                        pairs (partition 2 bindings)
                        [new-bindings new-locals]
                        (reduce
                          (fn [[acc current-locals] [sym init]]
                            [(conj acc sym (transform env current-locals init))
                             (conj current-locals sym)])
                          [[] locals]
                          pairs)
                        t-body (doall (map #(transform env new-locals %) body))]
                    (preserve-meta form (apply list 'loop* (vec new-bindings) t-body)))
            do (let [forms (doall (map #(transform env locals %) (rest form)))]
                 (if (= 1 (count forms))
                   (first forms)
                   (preserve-meta form (cons 'do forms))))
            if (if (< (count form) 3)
                 form ;; too few args — let analyzer report error
                 (let [[_ test then else] form
                       t-test (transform env locals test)
                       t-then (transform env locals then)
                       has-else (> (count form) 3)
                       t-else (when has-else (transform env locals else))]
                   (if (or (needs-lifting? t-test) (if-with-iife-branch? t-test) (do-with-statements? t-test))
                     ;; Lift test into let* binding — test is always evaluated so safe
                     (let [[bindings stmts [new-test]] (lift-args locals [t-test])
                           if-form (preserve-meta form
                                     (if has-else
                                       (list 'if new-test t-then t-else)
                                       (list 'if new-test t-then)))]
                       (apply list 'let* (vec bindings)
                              (concat stmts [if-form])))
                     (preserve-meta form
                       (if has-else
                         (list 'if t-test t-then t-else)
                         (list 'if t-test t-then))))))
            fn* form
            quote form
            try form
            case* form
            letfn* form
            deftype* form
            defrecord* form
            ns form
            ns* form
            def form
            ;; General expression: function call or other
            (transform-args env locals form op (rest form))))))

    (vector? form)
    (let [transformed (doall (map #(transform env locals %) form))]
      (if (or (some needs-lifting? transformed)
              (some if-with-iife-branch? transformed)
              (some do-with-statements? transformed))
        (let [[bindings stmts new-elems] (lift-args locals transformed)]
          (apply list 'let* (vec bindings)
                 (concat stmts [(vec new-elems)])))
        (vec transformed)))

    :else form))
