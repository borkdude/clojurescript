(ns cljs.async-await-test
  (:require [clojure.test :refer [deftest is async]]))

(defn ^:async foo [n]
  (let [x (js-await (js/Promise.resolve 10))
        y (let [y (js-await (js/Promise.resolve 20))]
            (inc y))
        ;; not async
        f (fn [] 20)]
    (+ n x y (f))))

(deftest defn-test
  (async done
    (try
      (let [v (js-await (foo 10))]
        (is (= 61 v)))
      (let [v (js-await (apply foo [10]))]
        (is (= 61 v)))
      (catch :default e (prn :should-not-reach-here e))
      (finally (done)))))

(deftest fn-test
  (async done
    (try
      (let [f (^:async fn [x] (+ x (js-await (js/Promise.resolve 20))))
            v (js-await (f 10))
            v2 (js-await (apply f [10]))]
        (is (= 30 v v2)))
      (catch :default e (prn :should-not-reach-here e))
      (finally (done)))))

(deftest varargs-fn-test
  (async done
    (try
      (let [f (^:async fn [x & xs] (apply + x (js-await (js/Promise.resolve 20)) xs))
            v (js-await (f 10))
            v2 (js-await (apply f [10]))
            v3 (js-await (f 5 5))
            v4 (js-await (apply f [5 5]))]
        (is (= 30 v v2 v3 v4)))
      (catch :default e (prn :should-not-reach-here e))
      (finally (done)))))

(deftest variadic-fn-test
  (async done
    (try (let [f (^:async fn
                  ([x] (js-await (js/Promise.resolve x)))
                  ([x y] (cons (js-await (js/Promise.resolve x)) [y])))]
           (is (= [1 1 [1 2] [1 2]]
                  [(js-await (f 1))
                   (js-await (apply f [1]))
                   (js-await (f 1 2))
                   (js-await (apply f [1 2]))])))
         (catch :default e (prn :should-not-reach-here e))
         (finally (done)))))

(deftest variadic-varargs-fn-test
  (async done
    (try (let [f (^:async fn
                  ([x] (js-await (js/Promise.resolve x)))
                  ([x & xs] (cons (js-await (js/Promise.resolve x)) xs)))]
           (is (= [1 1 [1 2 3] [1 2 3]]
                  [(js-await (f 1))
                   (js-await (apply f [1]))
                   (js-await (f 1 2 3))
                   (js-await (apply f [1 2 3]))])))
         (catch :default e (prn :should-not-reach-here e))
         (finally (done)))))

(deftest await-in-throw-test
  (async done
    (let [f (^:async fn [x] (inc (if (odd? x) (throw (js-await (js/Promise.resolve "dude"))) x)))]
      (try
        (let [x (js-await (f 2))]
          (is (= 3 x)))
        (let [x (try (js-await (f 1))
                     (catch :default e e))]
          (is (= "dude" x)))
        (catch :default e (prn :should-not-reach-here e))
        (finally (done))))))

(deftest await-in-do-test
  (async done
    (try
      (let [a (atom 0)
            f (^:async fn [] (let [_ (do (swap! a inc)
                                         (swap! a + (js-await (js/Promise.resolve 2))))]
                               @a))
            v (js-await (f))]
        (is (= 3 v)))
      (catch :default e (prn :should-not-reach-here e))
      (finally (done)))))
