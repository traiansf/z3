# This file contains tests for predabst's validation of input that is malformed
# in various ways.  Each test case tests for a single error, and is
# self-explanatory.

unknown_tests = [
    ("wf-odd-arity",
     """
(declare-fun __wf__p (Int) Bool)
(assert (forall ((x Int)) (__wf__p x)))""",
     "WF predicate symbol __wf__p has odd arity"),

    ("wf-mismatching-args",
     """
(declare-fun __wf__p (Int Real) Bool)
(assert (forall ((x Int) (y Real)) (__wf__p x y)))""",
     "WF predicate symbol __wf__p has mismatching argument types"),

    ("wf-non-int-args",
     """
(declare-fun __wf__p (Real Real) Bool)
(assert (forall ((x Real) (y Real)) (__wf__p x y)))""",
     "WF predicate symbol __wf__p has non-integer argument types"),

     ("extra-multiple-same-type",
     """
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((a Int)) (__temp__extra__ a)))
(assert (forall ((a Int)) (__temp__extra__ a)))""",
     "found multiple extra template constraints"),

     ("extra-multiple-different-type",
     """
(declare-fun __temp__extra__ (Int) Bool)
(declare-fun __temp__extra__ (Int Int) Bool)
(assert (forall ((a Int)) (__temp__extra__ a)))
(assert (forall ((a Int) (b Int)) (__temp__extra__ a b)))""",
     "found multiple extra template constraints"),

    ("extra-in-body",
     """
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((a Int)) (=> (__temp__extra__ a) false)))""",
     "found extra template constraint in non-head position"),

    ("extra-uninterp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((a Int)) (=> (p a) (__temp__extra__ a))))""",
     "extra template constraint has an uninterpreted tail"),

    ("extra-non-var-args",
     """
(declare-fun __temp__extra__ (Int Int) Bool)
(assert (forall ((a Int)) (__temp__extra__ a 0)))""",
     "extra template constraint has invalid argument list"),

    ("extra-non-unique-args",
     """
(declare-fun __temp__extra__ (Int Int) Bool)
(assert (forall ((a Int)) (__temp__extra__ a a)))""",
     "extra template constraint has invalid argument list"),

    ("extra-free-vars",
     """
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((a Int) (b Int)) (=> (= a b) (__temp__extra__ a))))""",
     "extra template constraint has free variables"),

    ("templ-zero-length-query",
     """
(declare-fun __temp__ (Int) Bool)
(assert (forall ((x Int)) (__temp__ x)))""",
     "found template for predicate symbol with zero-length name"),

    ("templ-insufficient-args",
     """
(declare-fun __temp__extra__ (Int Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((a Int) (b Int)) (__temp__extra__ a b)))
(assert (forall ((x Int)) (__temp__p x)))""",
     "template for p has insufficient parameters"),

    ("templ-mismatching-args",
     """
(declare-fun __temp__extra__ (Int Real) Bool)
(declare-fun __temp__p (Real Int) Bool)
(assert (forall ((a Int) (b Real)) (__temp__extra__ a b)))
(assert (forall ((a Real) (b Int)) (__temp__p a b)))""",
     "extra parameter to template for p is of wrong type"),

    ("templ-no-query",
     """
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (__temp__p x)))""",
     "found template for non-existent predicate symbol p"),

    ("templ-no-query-same-type",
     """
(declare-fun p (Real) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Real)) (p x)))
(assert (forall ((x Int)) (__temp__p x)))""",
     "found template for non-existent predicate symbol p"),

    ("templ-wf",
     """
(declare-fun __wf__p (Int Int) Bool)
(declare-fun __temp____wf__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (__wf__p x y)))
(assert (forall ((x Int) (y Int)) (__temp____wf__p x y)))""",
     "found template for WF predicate symbol __wf__p"),

    ("templ-multiple",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (__temp__p x)))
(assert (forall ((x Int)) (__temp__p x)))""",
     "found multiple templates for p"),

    ("templ-in-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (__temp__p x) false)))""",
     "found template __temp__p in non-head position"),

    ("templ-uninterp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (p x) (__temp__p x))))""",
     "template for p has an uninterpreted tail"),

    ("templ-non-var-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (__temp__p x 0)))""",
     "template for p has invalid argument list"),

    ("templ-non-unique-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (__temp__p x x)))""",
     "template for p has invalid argument list"),

    ("templ-free-vars",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__temp__p x))))""",
     "template for p has free variables"),

    ("expargs-zero-length-query",
     """
(declare-fun __expargs__ (Int) Bool)
(assert (forall ((x Int)) (__expargs__ x)))""",
     "found explicit argument list for predicate symbol with zero-length name"),

    ("expargs-no-query",
     """
(declare-fun __expargs__p (Int) Bool)
(assert (forall ((x Int)) (__expargs__p x)))""",
     "found explicit argument list for non-existent predicate symbol p"),

    ("expargs-no-query-same-type",
     """
(declare-fun p (Real) Bool)
(declare-fun __expargs__p (Int) Bool)
(assert (forall ((x Real)) (p x)))
(assert (forall ((x Int)) (__expargs__p x)))""",
     "found explicit argument list for non-existent predicate symbol p"),

    ("expargs-templ",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (__temp__p x)))
(assert (forall ((x Int)) (__expargs__p x)))""",
     "found explicit argument list for templated predicate symbol p"),

    ("expargs-in-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (__expargs__p x) false)))""",
     "found explicit argument list __expargs__p in non-head position"),

    ("expargs-interp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (= x 0) (__expargs__p x))))""",
     "explicit argument list for p has an interpreted tail"),

    ("expargs-non-var-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (__expargs__p x 0)))""",
     "explicit argument list for p has invalid argument list"),

    ("expargs-non-unique-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (__expargs__p x x)))""",
     "explicit argument list for p has invalid argument list"),

    ("expargs-tail-not-exparg",
     """
(declare-fun p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (p x) (__expargs__p x))))""",
     "explicit argument list for p has unexpected predicate in uninterpreted tail"),

    ("expargs-tail-bad-exparg-arity",
     """
(declare-fun p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(declare-fun __exparg__ () Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> __exparg__ (__expargs__p x))))""",
     "explicit argument list for p has __exparg__ predicate of incorrect arity"),

    ("expargs-tail-not-var-arg",
     """
(declare-fun p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (__exparg__ 0) (__expargs__p x))))""",
     "explicit argument list for p has __exparg__ predicate with non-variable argument"),

    ("expargs-tail-not-head-var-arg",
     """
(declare-fun p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ y) (__expargs__p x))))""",
     "explicit argument list for p has __exparg__ predicate with argument that does not appear in the head"),

    ("expargs-duplicate-exparg",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int) (y Int)) (=> (and (__exparg__ x) (__exparg__ x)) (__expargs__p x y))))""",
     "explicit argument list for p has duplicate __exparg__ declaration for argument"),

    ("exparg-in-head",
     """
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int)) (__exparg__ x)))""",
     "found explicit argument __exparg__ in head position"),

    ("exparg-in-regular-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int)) (=> (__exparg__ x) (p x))))""",
     "found explicit argument __exparg__ in body of regular rule"),

    ("expargs-wf-not-pairwise",
     """
(declare-fun __wf__p (Int Int) Bool)
(declare-fun __expargs____wf__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (__wf__p x y)))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs____wf__p x y))))""",
     "WF predicate symbol __wf__p has non-pairwise explicit arguments"),

    ("expargs-incorrect",
     """
(declare-fun p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (__exparg__ x) (__expargs__p x))))""",
     "values of explicit arguments for p were not uniquely determined"),

    ("plist-zero-length-query",
     """
(declare-fun __pred__ (Int) Bool)
(assert (forall ((x Int)) (__pred__ x)))""",
     "found predicate list for predicate symbol with zero-length name"),

    ("plist-no-query",
     """
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (__pred__p x)))""",
     "found predicate list for non-existent predicate symbol p"),

    ("plist-no-query-same-type",
     """
(declare-fun p (Real) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Real)) (p x)))
(assert (forall ((x Int)) (__pred__p x)))""",
     "found predicate list for non-existent predicate symbol p"),

    ("plist-templ",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (__temp__p x)))
(assert (forall ((x Int)) (__pred__p x)))""",
     "found predicate list for templated predicate symbol p"),

    ("plist-in-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (__pred__p x) false)))""",
     "found predicate list __pred__p in non-head position"),

    ("plist-uninterp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (p x) (__pred__p x))))""",
     "predicate list for p has an uninterpreted tail"),

    ("plist-non-var-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (__pred__p x 0)))""",
     "predicate list for p has invalid argument list"),

    ("plist-non-unique-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (__pred__p x x)))""",
     "predicate list for p has invalid argument list"),

    ("plist-free-vars",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__pred__p x))))""",
     "predicate for p has free variables"),

    ("plist-explicit-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__pred__p x y))))""",
     "predicate for p uses explicit arguments"),

    ("names-zero-length-query",
     """
(declare-fun __names__ (Int) Bool)
(assert (forall ((x Int)) (__names__ x)))""",
     "found argument name list for predicate symbol with zero-length name"),

    ("names-no-query",
     """
(declare-fun __names__p (Int) Bool)
(assert (forall ((x Int)) (__names__p x)))""",
     "found argument name list for non-existent predicate symbol p"),

    ("names-no-query-same-type",
     """
(declare-fun p (Real) Bool)
(declare-fun __names__p (Int) Bool)
(assert (forall ((x Real)) (p x)))
(assert (forall ((x Int)) (__names__p x)))""",
     "found argument name list for non-existent predicate symbol p"),

    ("names-templ",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(declare-fun __names__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (__temp__p x)))
(assert (forall ((x Int)) (__names__p x)))""",
     "found argument name list for templated predicate symbol p"),

    ("names-in-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __names__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (__names__p x) false)))""",
     "found argument name list __names__p in non-head position"),

    ("names-interp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __names__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (= x 0) (__names__p x))))""",
     "argument name list for p has an interpreted tail"),

    ("names-non-var-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __names__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (__names__p x 0)))""",
     "argument name list for p has invalid argument list"),

    ("names-non-unique-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __names__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (__names__p x x)))""",
     "argument name list for p has invalid argument list"),

    ("names-tail-not-name",
     """
(declare-fun p (Int) Bool)
(declare-fun __names__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (p x) (__names__p x))))""",
     "argument name list for p has unexpected predicate in uninterpreted tail"),

    ("names-tail-bad-name-arity",
     """
(declare-fun p (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __name__foo () Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> __name__foo (__names__p x))))""",
     "argument name list for p has __name__X predicate of incorrect arity"),

    ("names-tail-not-var-arg",
     """
(declare-fun p (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __name__foo (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (__name__foo 0) (__names__p x))))""",
     "argument name list for p has __name__X predicate with non-variable argument"),

    ("names-tail-not-head-var-arg",
     """
(declare-fun p (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __name__foo (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int) (y Int)) (=> (__name__foo y) (__names__p x))))""",
     "argument name list for p has __name__X predicate with argument that does not appear in the head"),

    ("names-zero-length-name",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __names__p (Int Int) Bool)
(declare-fun __name__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int) (y Int)) (=> (__name__ x) (__names__p x y))))""",
     "argument name list for p has zero-length name for argument"),

    ("names-duplicate-name-same",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __names__p (Int Int) Bool)
(declare-fun __name__foo (Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int) (y Int)) (=> (and (__name__foo x) (__name__foo x)) (__names__p x y))))""",
     "argument name list for p has duplicate name for argument"),

    ("names-duplicate-name-different",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __names__p (Int Int) Bool)
(declare-fun __name__foo (Int) Bool)
(declare-fun __name__bar (Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int) (y Int)) (=> (and (__name__foo x) (__name__bar x)) (__names__p x y))))""",
     "argument name list for p has duplicate name for argument"),

    ("names-non-unique-name",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __names__p (Int Int) Bool)
(declare-fun __name__foo (Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int) (y Int)) (=> (and (__name__foo x) (__name__foo y)) (__names__p x y))))""",
     "argument name list for p has non-unique argument names"),

    ("name-in-head",
     """
(declare-fun __name__foo (Int) Bool)
(assert (forall ((x Int)) (__name__foo x)))""",
     "found argument name __name__foo in head position"),

    ("name-in-regular-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __name__foo (Int) Bool)
(assert (forall ((x Int)) (=> (__name__foo x) (p x))))""",
     "found argument name __name__foo in body of regular rule"),
]

inpval_tests = ([], [], unknown_tests)
