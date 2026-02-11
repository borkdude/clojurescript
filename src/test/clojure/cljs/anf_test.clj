(ns cljs.anf-test
  "Tests for the ANF (A-Normal Form) transformation.
   Demonstrates how IIFE-causing forms are lifted out of expression position."
  (:require [cljs.anf :as anf]
            [clojure.test :refer [deftest is testing]]))

;; ---------------------------------------------------------------------------
;; Test helpers
;; ---------------------------------------------------------------------------

(defn- deterministic-gensyms
  "Returns a gensym function that produces predictable symbol names:
   G__1, G__2, ... (no prefix) or prefix1, prefix2, ... (with prefix)."
  []
  (let [counter (atom 0)]
    (fn
      ([] (symbol (str "G__" (swap! counter inc))))
      ([prefix] (symbol (str prefix (swap! counter inc)))))))

(defmacro with-gensyms
  "Execute body with deterministic gensym names for predictable test output."
  [& body]
  `(with-redefs [gensym (deterministic-gensyms)]
     ~@body))

(defn- t
  "Shorthand: transform form with empty env and given locals set."
  ([form] (anf/transform {} #{} form))
  ([locals form] (anf/transform {} locals form)))

;; ---------------------------------------------------------------------------
;; Basic lifting — let* flattening
;; ---------------------------------------------------------------------------

(deftest let*-flattening-in-fn-args
  (testing "let* in function arg position is flattened"
    ;; (f (let* [x 1] x))
    ;; => (let* [x 1] (f x))
    ;; The let* is hoisted so it's no longer in expression position (no IIFE).
    (is (= '(let* [x 1] (f x))
           (t '(f (let* [x 1] x)))))))

(deftest nested-let*-flattening
  (testing "Nested let* forms are recursively flattened"
    ;; (f (let* [x (let* [y 1] y)] x))
    ;; => (let* [y 1 x y] (f x))
    ;; Both levels of let* are flattened into a single binding vector.
    (is (= '(let* [y 1 x y] (f x))
           (t '(f (let* [x (let* [y 1] y)] x)))))))

(deftest let*-in-let*-binding-init
  (testing "let* in a let* binding init is flattened into the outer let*"
    ;; (let* [a (let* [b 1] b)] a)
    ;; => (let* [b 1 a b] a)
    (is (= '(let* [b 1 a b] a)
           (t '(let* [a (let* [b 1] b)] a))))))

(deftest multiple-let*-args-flattened
  (testing "Multiple let* args are all flattened into one binding vector"
    ;; (f (let* [x 1] x) (let* [y 2] y))
    ;; => (let* [x 1 y 2] (f x y))
    (is (= '(let* [x 1 y 2] (f x y))
           (t '(f (let* [x 1] x) (let* [y 2] y)))))))

;; ---------------------------------------------------------------------------
;; Opaque forms — not recursed into
;; ---------------------------------------------------------------------------

(deftest opaque-forms-pass-through
  (testing "fn*, quote, try, case*, letfn* are returned as-is"
    (is (= '(fn* [x] x)         (t '(fn* [x] x))))
    (is (= '(quote (let* [x 1] x)) (t '(quote (let* [x 1] x)))))
    (is (= '(try x)              (t '(try x))))
    (is (= '(letfn* [f (fn* f ([] 1))] (f)) (t '(letfn* [f (fn* f ([] 1))] (f))))))

  (testing "deftype*, defrecord*, ns, ns*, def are returned as-is"
    (is (= '(def x 1)            (t '(def x 1))))
    (is (= '(ns foo)             (t '(ns foo))))
    (is (= '(ns* foo)            (t '(ns* foo))))))

;; ---------------------------------------------------------------------------
;; Edge cases
;; ---------------------------------------------------------------------------

(deftest empty-list-unchanged
  (testing "Empty list () passes through without error"
    (is (= '() (t '())))))

(deftest symbols-and-literals-unchanged
  (testing "Atoms pass through unchanged"
    (is (= 'x   (t 'x)))
    (is (= 42   (t 42)))
    (is (= "hi" (t "hi")))
    (is (= :k   (t :k)))
    (is (= nil  (t nil)))))

(deftest if-preserves-else-false
  (testing "Literal false in else position is preserved, not dropped"
    ;; (if true 1 false) => (if true 1 false)
    ;; Previously (when else ...) treated false as missing else.
    (is (= '(if true 1 false)
           (t '(if true 1 false))))))

(deftest if-without-else
  (testing "if with no else branch stays as two-arg if"
    (is (= '(if true 1)
           (t '(if true 1))))))

(deftest do-single-form
  (testing "do with a single sub-form simplifies to that form"
    (is (= 'x (t '(do x))))))

(deftest do-multiple-forms-unchanged
  (testing "do with multiple forms is preserved"
    (is (= '(do a b) (t '(do a b))))))

;; ---------------------------------------------------------------------------
;; Lifting with gensyms — loop*, try, letfn* bound to gensym
;; ---------------------------------------------------------------------------

(deftest loop*-in-fn-arg
  (testing "loop* in fn arg is bound to a gensym (can't be flattened)"
    ;; (f (loop* [x 1] x))
    ;; => (let* [anf__1 (loop* [x 1] x)] (f anf__1))
    (with-gensyms
      (is (= '(let* [anf__1 (loop* [x 1] x)] (f anf__1))
             (t '(f (loop* [x 1] x))))))))

(deftest try-in-fn-arg
  (testing "try in fn arg is bound to a gensym (can't be flattened)"
    (with-gensyms
      (is (= '(let* [anf__1 (try x)] (f anf__1))
             (t '(f (try x))))))))

(deftest letfn*-in-fn-arg
  (testing "letfn* in fn arg is bound to a gensym"
    (with-gensyms
      (is (= '(let* [anf__1 (letfn* [g (fn* g ([] 1))] (g))]
                (f anf__1))
             (t '(f (letfn* [g (fn* g ([] 1))] (g)))))))))

;; ---------------------------------------------------------------------------
;; Vector literals
;; ---------------------------------------------------------------------------

(deftest vector-lifting
  (testing "let* inside a vector literal is lifted out"
    ;; [(let* [x 1] x)] => (let* [x 1] [x])
    (is (= '(let* [x 1] [x])
           (t '[(let* [x 1] x)])))))

(deftest vector-multiple-lifts
  (testing "Multiple IIFE-causing forms in vector are all lifted"
    (with-gensyms
      (is (= '(let* [x 1 y 2] [x y])
             (t '[(let* [x 1] x) (let* [y 2] y)]))))))

;; ---------------------------------------------------------------------------
;; Declare-assign pattern — if with IIFE-causing branches
;; ---------------------------------------------------------------------------

(deftest if-with-iife-branch-in-fn-arg
  (testing "if with let* branch uses declare-assign: void 0 + js* assignment"
    ;; (f (if test (let* [x 1] x) y))
    ;; => (let* [anf__1 (js* "void 0")]
    ;;      (if test (let* [x 1] (js* "(~{} = ~{})" anf__1 x))
    ;;              (js* "(~{} = ~{})" anf__1 y))
    ;;      (f anf__1))
    (with-gensyms
      (is (= '(let* [anf__1 (js* "void 0")]
                (if test
                  (let* [x 1] (js* "(~{} = ~{})" anf__1 x))
                  (js* "(~{} = ~{})" anf__1 y))
                (f anf__1))
             (t '(f (if test (let* [x 1] x) y))))))))

(deftest if-with-iife-branch-in-let*-init
  (testing "if with IIFE branch in let* binding init uses declare-assign"
    ;; (let* [x (if test (let* [y 1] y) z)] (f x))
    ;; => (let* [x (js* "void 0")]
    ;;      (if test (let* [y 1] (js* "(~{} = ~{})" x y))
    ;;              (js* "(~{} = ~{})" x z))
    ;;      (f x))
    (let [result (t '(let* [x (if test (let* [y 1] y) z)] (f x)))]
      (is (= 'let* (first result)))
      (let [[_ bindings & body] result]
        (is (= 'x (first bindings)))
        (is (= '(js* "void 0") (second bindings)))
        ;; if-statement in body
        (is (= 'if (first (first body))))
        ;; fn call after if
        (is (= '(f x) (second body)))))))

(deftest if-with-iife-both-branches
  (testing "if where both branches have let* uses declare-assign for both"
    (with-gensyms
      (let [result (t '(f (if test (let* [x 1] x) (let* [y 2] y))))]
        (is (= 'let* (first result)))
        (let [[_ bindings & body] result
              if-stmt (first body)]
          ;; void 0 declaration
          (is (= '(js* "void 0") (second bindings)))
          ;; if has then and else, both with assignments
          (is (= 'if (first if-stmt)))
          (let [[_ _test then else] if-stmt]
            ;; then branch: (let* [x 1] (js* "(~{} = ~{})" sym x))
            (is (= 'let* (first then)))
            ;; else branch: (let* [y 2] (js* "(~{} = ~{})" sym y))
            (is (= 'let* (first else)))))))))

(deftest flattened-let*-body-is-if-with-iife
  (testing "After flattening let*, body that is if-with-iife gets declare-assign"
    ;; (f (let* [t (g)] (if t (let* [x t] x) nil)))
    ;; Without fix: the if-with-iife body passes through as arg → IIFE.
    ;; With fix: declare-assign on the flattened body.
    (with-gensyms
      (is (= '(let* [t (g) anf__1 (js* "void 0")]
                (if t
                  (let* [x t] (js* "(~{} = ~{})" anf__1 x))
                  (js* "(~{} = ~{})" anf__1 nil))
                (f anf__1))
             (t '(f (let* [t (g)] (if t (let* [x t] x) nil)))))))))

;; ---------------------------------------------------------------------------
;; Variable shadowing — rename-inner-bindings
;; ---------------------------------------------------------------------------

(deftest rename-on-local-conflict
  (testing "Inner let* binding renamed when it conflicts with locals"
    ;; With locals=#{x}: (f (let* [x 1] x))
    ;; => (let* [x__1 1] (f x__1))
    ;; The inner x is renamed to avoid shadowing the outer x.
    (with-gensyms
      (is (= '(let* [x__1 1] (f x__1))
             (t #{'x} '(f (let* [x 1] x))))))))

(deftest no-rename-without-conflict
  (testing "Inner let* binding is NOT renamed when no conflict"
    ;; With locals=#{y}: (f (let* [x 1] x))
    ;; => (let* [x 1] (f x))
    (is (= '(let* [x 1] (f x))
           (t #{'y} '(f (let* [x 1] x)))))))

(deftest same-name-rebinding-declare-assign
  (testing "Same-name rebinding with if-with-iife uses gensym to avoid clobber"
    ;; (let* [x 1 x (if test (let* [y 2] y) 3)] (f x))
    ;; The second x would clobber the first's value with void 0.
    ;; Fix: second x is renamed to a gensym, remaining refs updated.
    (with-gensyms
      (let [result (t '(let* [x 1 x (if test (let* [y 2] y) 3)] (f x)))]
        (is (= 'let* (first result)))
        (let [[_ bindings & body] result
              binding-syms (take-nth 2 bindings)]
          ;; First binding is x, followed by inner bindings, then gensym
          (is (= 'x (first binding-syms)))
          ;; The declare-assign gensym should NOT be x (renamed)
          (is (not= 'x (last binding-syms)))
          ;; Body should reference the gensym, not x
          (let [fn-call (last body)]
            (is (= 'f (first fn-call)))
            (is (not= 'x (second fn-call)))))))))

;; ---------------------------------------------------------------------------
;; Accumulated locals in lift-args (bug #16 — gensym collision)
;; ---------------------------------------------------------------------------

(deftest lift-args-accumulated-locals
  (testing "Two let* args with same binding name: second is renamed"
    ;; (f (let* [t 1] t) (let* [t 2] t))
    ;; Without fix: both t bindings collide in the flattened let*.
    ;; With fix: second t is renamed because first t is in accumulated bindings.
    (with-gensyms
      (let [result (t '(f (let* [t 1] t) (let* [t 2] t)))]
        (is (= 'let* (first result)))
        (let [[_ bindings & body] result
              pairs (partition 2 bindings)
              syms (map first pairs)]
          ;; Should have two bindings with different names
          (is (= 2 (count pairs)))
          (is (not= (first syms) (second syms))
              "Second t should be renamed to avoid shadowing first t")
          ;; The fn call should use both (different) symbols
          (let [[f-sym arg1 arg2] (first body)]
            (is (= 'f f-sym))
            (is (= (first syms) arg1))
            (is (= (second syms) arg2))))))))

;; ---------------------------------------------------------------------------
;; do-with-statements
;; ---------------------------------------------------------------------------

(deftest do-with-statements-in-fn-arg
  (testing "do with statements in fn arg position is lifted"
    ;; (f (do stmt val))
    ;; => (let* [] stmt (f val))  — stmts hoisted into let* body
    ;; The do is split: statements become let* body stmts, last expr stays as arg.
    (let [result (t '(f (do (side-effect) val)))]
      ;; Should be a let* with the side-effect as a statement
      (is (= 'let* (first result)))
      (let [[_ bindings & body] result]
        (is (= [] (vec bindings)))
        (is (= '(side-effect) (first body)))
        (is (= '(f val) (second body)))))))

;; ---------------------------------------------------------------------------
;; Metadata preservation
;; ---------------------------------------------------------------------------

(deftest metadata-preserved-on-if
  (testing "Metadata on if form is preserved after transformation"
    (let [form (with-meta '(if true 1 2) {:tag 'boolean})
          result (t form)]
      (is (= {:tag 'boolean} (meta result))))))

(deftest metadata-preserved-on-do
  (testing "Metadata on do form is preserved"
    (let [form (with-meta '(do a b) {:line 42})
          result (t form)]
      (is (= {:line 42} (meta result))))))

(deftest metadata-preserved-on-fn-call
  (testing "Metadata on function call form is preserved after transformation"
    (let [form (with-meta '(f x y) {:tag 'boolean})
          result (t form)]
      (is (= {:tag 'boolean} (meta result))))))

(deftest metadata-preserved-through-lifting
  (testing "Metadata on fn call is preserved even when args are lifted"
    (let [form (with-meta '(f (let* [x 1] x)) {:tag 'string})
          result (t form)]
      ;; Result is (let* [x 1] (f x)) — check the inner (f x) has the tag
      (is (= 'let* (first result)))
      (let [[_ _ inner-call] result]
        (is (= 'f (first inner-call)))
        (is (= {:tag 'string} (meta inner-call)))))))

;; ---------------------------------------------------------------------------
;; loop* binding inits are transformed
;; ---------------------------------------------------------------------------

(deftest loop*-binding-inits-transformed
  (testing "loop* binding inits are transformed (but loop body is too)"
    ;; (loop* [x (let* [y 1] y)] x)
    ;; => (loop* [x (let* [y 1] y)] x)
    ;; Note: loop* binding inits go through transform, but the let*
    ;; stays because we can't flatten into loop* bindings the same way.
    ;; The body is also transformed.
    (let [result (t '(loop* [x (let* [y 1] y)] x))]
      (is (= 'loop* (first result))))))

;; ---------------------------------------------------------------------------
;; Nested if-with-iife (recursive case)
;; ---------------------------------------------------------------------------

(deftest nested-if-with-iife
  (testing "Nested if where inner if has IIFE branch is handled"
    ;; (f (if a (if b (let* [x 1] x) c) d))
    ;; The outer if's then-branch is itself an if-with-iife-branch.
    (with-gensyms
      (let [result (t '(f (if a (if b (let* [x 1] x) c) d)))]
        ;; Should produce a declare-assign pattern
        (is (= 'let* (first result)))))))
