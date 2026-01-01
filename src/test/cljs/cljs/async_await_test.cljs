(ns cljs.async-await-test
  (:require [clojure.test :refer [deftest is async]]))

(defn ^:async foo [n]
  (let [x (js-await (js/Promise.resolve 10))
        y (let [y (js-await (js/Promise.resolve 20))]
            (inc y))
        ;; not async
        f (fn [] 20)]
    (+ n x y (f))))

(deftest async-await-test
  (async done
    (-> (foo 10)
        (.then
            (fn [v]
              (is (= 61 v))))
        (.finally done))))
