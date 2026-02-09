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

(defn- needs-lifting?
  "Returns true if form would cause an IIFE when compiled in expression position."
  [form]
  (and (seq? form)
       (contains? #{'let* 'loop* 'try 'letfn*} (first form))))

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

(defn- lift-args
  "Given a list of transformed args, extract any IIFE-causing forms into
   let* bindings. Returns [bindings new-args].
   For let*, flattens by hoisting inner bindings (renaming conflicts with
   locals to avoid shadowing). For other forms, binds the whole form to a gensym."
  [locals args]
  (reduce
    (fn [[bindings new-args] arg]
      (if (needs-lifting? arg)
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
                 (conj new-args result-sym)])
              ;; Body is trivial — use directly as arg
              [(into bindings renamed-bindings)
               (conj new-args renamed-body)]))
          ;; Other IIFE-causing forms: bind whole thing to gensym
          (let [result-sym (gensym "anf__")]
            [(conj bindings result-sym arg)
             (conj new-args result-sym)]))
        [bindings (conj new-args arg)]))
    [[] []]
    args))

(defn- transform-args
  "Transform function call args. If any transformed arg is IIFE-causing,
   extract it into a surrounding let* and replace with a gensym reference."
  [env locals op args]
  (let [transformed (doall (map #(transform env locals %) args))]
    (if (some needs-lifting? transformed)
      (let [[bindings new-args] (lift-args locals transformed)]
        (list 'let* (vec bindings) (cons op new-args)))
      (cons op transformed))))

(defn- transform-let*
  "Transform let* form: recursively transform binding inits and body.
   Flattens nested let* in binding inits to avoid IIFEs.
   Inner bindings are renamed to gensyms to prevent shadowing."
  [env locals bindings body]
  (let [pairs (partition 2 bindings)
        [new-bindings new-locals]
        (reduce
          (fn [[acc current-locals] [sym init]]
            (let [t-init (transform env current-locals init)]
              (if (and (seq? t-init) (= 'let* (first t-init)))
                ;; Flatten: hoist inner bindings (renamed), bind inner body to sym
                (let [[_ inner-bindings & inner-body] t-init
                      body-form (if (= 1 (count inner-body))
                                  (first inner-body)
                                  (cons 'do inner-body))
                      [renamed-bindings renamed-body] (rename-inner-bindings current-locals inner-bindings body-form)
                      inner-syms (take-nth 2 renamed-bindings)]
                  [(-> acc (into renamed-bindings) (conj sym renamed-body))
                   (into (conj current-locals sym) inner-syms)])
                [(conj acc sym t-init)
                 (conj current-locals sym)])))
          [[] locals]
          pairs)
        t-body (doall (map #(transform env new-locals %) body))]
    (apply list 'let* (vec new-bindings) t-body)))

(defn- try-macroexpand-1
  "Attempt to macroexpand form once using ::get-expander from env.
   Returns original form if no expander or expansion fails."
  [env form]
  (if-let [get-exp (::get-expander env)]
    (let [op (first form)]
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
    (let [op (first form)
          ;; Try to macroexpand if not a special form and not locally bound
          expanded (if (and (symbol? op)
                           (not (contains? specials op))
                           (not (contains? locals op)))
                    (try-macroexpand-1 env form)
                    form)]
      (if (not= expanded form)
        ;; Macro expanded — recurse on expanded form
        (transform env locals expanded)
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
                   (apply list 'loop* (vec new-bindings) t-body))
          do (cons 'do (doall (map #(transform env locals %) (rest form))))
          if (let [[_ test then else] form]
               (if else
                 (list 'if (transform env locals test)
                       (transform env locals then)
                       (transform env locals else))
                 (list 'if (transform env locals test)
                       (transform env locals then))))
          fn* form
          quote form
          try form
          case* form
          letfn* form
          ;; General expression: function call or other
          (transform-args env locals op (rest form)))))

    (vector? form)
    (let [transformed (doall (map #(transform env locals %) form))]
      (if (some needs-lifting? transformed)
        (let [[bindings new-elems] (lift-args locals transformed)]
          (list 'let* (vec bindings) (vec new-elems)))
        (vec transformed)))

    :else form))
