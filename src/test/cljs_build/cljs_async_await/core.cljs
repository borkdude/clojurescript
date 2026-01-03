(ns cljs-async-await.core)

(defn foo []
  (^:async fn [x & xs] (apply + x (js-await (js/Promise.resolve 20)) xs)))
