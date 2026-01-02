(ns cljs.async-await-test
  (:require [clojure.test :refer [deftest is async]]))

(defn ^:async foo [n]
  (let [x (js-await (js/Promise.resolve 10))
        y (let [y (js-await (js/Promise.resolve 20))]
            (inc y))
        ;; not async
        f (fn [] 20)]
    (+ n x y (f))))

(deftest async-await-defn-test
  (async done
    (-> (foo 10)
        (.then
            (fn [v]
              (is (= 61 v))))
        (.finally done))))

(deftest async-await-fn-test
  (async done
    (let [f (^:async fn [x] (+ x (js-await (js/Promise.resolve 20))))]
      (-> (f 10)
          (.then
           (fn [v]
             (is (= 30 v))))
          (.finally done)))))

(defn ^:async await-in-throw-fn [x]
  (inc (if (odd? x) (throw (js-await (js/Promise.resolve "dude"))) x)))

(deftest await-in-throw-test
  (async done
    (try
      (let [x (js-await (await-in-throw-fn 2))]
        (is (= 3 x)))
      (let [x (try (js-await (await-in-throw-fn 1))
                   (catch :default e e))]
        (is (= "dude" x)))
      (catch :default e (prn :should-not-reach-here e))
      (finally (done)))))
