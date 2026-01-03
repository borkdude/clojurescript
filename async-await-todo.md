- [ ] Go over compiler.cljc and make hard-coded IIFEs compatible with async await
  - [ ] loop test

- [ ] check / agree on syntax over multiple dialects of Clojure (Dart, CLR)

Placing the metadata on the form isn't a great fit for CLJS since it turns the function into a MetaFn
^:async #(inc (js-await (js/Promise.resolve 1)))
#object[cljs.core.MetaFn]
cljs.user=> ^:async (fn [] (inc (js-await (js/Promise.resolve 1))))
#object[cljs.core.MetaFn]
8:32 PM
which isn't great for interop

- [ ] Optional: warn about using `js-await` on non-async context?
- [ ] Write JIRA issue + patch
