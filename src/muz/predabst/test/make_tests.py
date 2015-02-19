inpval_tests = [
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

    ("plist-no-query",
     """
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (__pred__p x))))""",
     "found predicate list for non-existent query symbol p"),
# XXX What about a similar case where a predicate with the same name but different arity/types exists?

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
(assert (forall ((x Int)) (=> (= x 0) (__pred__p x 0))))""",
     "predicate list for p has invalid argument list"),

    ("plist-non-unique-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (=> (= x 0) (__pred__p x x))))""",
     "predicate list for p has invalid argument list"),

    ("plist-free-vars",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__pred__p x))))""",
     "predicate for p has free variables"),

     ("extra-multiple-same-type",
     """
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((a Int)) (=> (= a 0) (__temp__extra__ a))))
(assert (forall ((a Int)) (=> (= a 1) (__temp__extra__ a))))""",
     "found multiple extra template constraints"),

     ("extra-multiple-different-type",
     """
(declare-fun __temp__extra__ (Int) Bool)
(declare-fun __temp__extra__ (Int Int) Bool)
(assert (forall ((a Int)) (=> (= a 0) (__temp__extra__ a))))
(assert (forall ((a Int) (b Int)) (=> (= b 1) (__temp__extra__ a b))))""",
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
(assert (forall ((a Int)) (=> (= a 0) (__temp__extra__ a 0))))""",
     "extra template constraint has invalid argument list"),

    ("extra-non-unique-args",
     """
(declare-fun __temp__extra__ (Int Int) Bool)
(assert (forall ((a Int)) (=> (= a 0) (__temp__extra__ a a))))""",
     "extra template constraint has invalid argument list"),

    ("extra-free-vars",
     """
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((a Int) (b Int)) (=> (= a b) (__temp__extra__ a))))""",
     "extra template constraint has free variables"),

    ("templ-insufficient-args",
     """
(declare-fun __temp__extra__ (Int Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((a Int) (b Int)) (=> (= a b) (__temp__extra__ a b))))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))""",
     "template for p has insufficient parameters"),

    ("templ-mismatching-args",
     """
(declare-fun __temp__extra__ (Int Real) Bool)
(declare-fun __temp__p (Real Int) Bool)
(assert (forall ((a Int) (b Real)) (=> (= a 0) (__temp__extra__ a b))))
(assert (forall ((a Real) (b Int)) (=> (= b 0) (__temp__p a b))))""",
     "extra parameter to template for p is of wrong type"),

    ("templ-no-query",
     """
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))""",
     "found template for non-existent query symbol p"),
# XXX What about a similar case where a predicate with the same name but different arity/types exists?

    ("templ-multiple",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) false)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))
(assert (forall ((x Int)) (=> (= x 1) (__temp__p x))))""",
     "found multiple templates for p"),
# XXX What about a similar (non-error) case where templates exist for two predicates with the same name but different arities/types?

    ("templ-in-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) false)))
(assert (forall ((x Int)) (=> (__temp__p x) false)))""",
     "found template __temp__p in non-head position"),

    ("templ-uninterp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) false)))
(assert (forall ((x Int)) (=> (p x) (__temp__p x))))""",
     "template for p has an uninterpreted tail"),

    ("templ-non-var-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (p x y) false)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x 0))))""",
     "template for p has invalid argument list"),

    ("templ-non-unique-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (p x y) false)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x x))))""",
     "template for p has invalid argument list"),

    ("templ-free-vars",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) false)))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__temp__p x))))""",
     "template for p has free variables"),

    ("templ-and-rule",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))""",
     "both rule and template for p"),
]

norefine_sat_tests = [
    ("empty",
     "",
     ""),

    ("trivial-unconstrained",
     """
(declare-fun p0 () Bool)
(declare-fun p1 (Int) Bool)
(declare-fun p2 (Int Int) Bool)
(assert (forall ((a Int)) (=> (distinct a a) p0)))
(assert (forall ((a Int) (x Int)) (=> (distinct a a) (p1 x))))
(assert (forall ((a Int) (x Int) (y Int)) (=> (distinct a a) (p2 x y))))""",
     """
(define-fun p0 () Bool false)
(define-fun p1 ((x!1 Int)) Bool false)
(define-fun p2 ((x!1 Int) (x!2 Int)) Bool false)"""),

    ("trivial-all-true",
     """
(declare-fun p0 () Bool)
(declare-fun p1 (Int) Bool)
(declare-fun p2 (Int Int) Bool)
(assert p0)
(assert (forall ((x Int)) (p1 x)))
(assert (forall ((x Int) (y Int)) (p2 x y)))""",
     """
(define-fun p0 () Bool true)
(define-fun p1 ((x!1 Int)) Bool true)
(define-fun p2 ((x!1 Int) (x!2 Int)) Bool true)"""),

    ("trivial-some-true",
     """
(declare-fun p1 (Int) Bool)
(declare-fun p2 (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p1 x))))
(assert (forall ((x Int) (y Int)) (=> (= x 0) (p2 x y))))""",
     """
(define-fun p1 ((x!1 Int)) Bool true)
(define-fun p2 ((x!1 Int) (x!2 Int)) Bool true)"""),

    ("trivial-some-false",
     """
(declare-fun p1 (Int) Bool)
(declare-fun p2 (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (not (p1 x)))))
(assert (forall ((x Int) (y Int)) (=> (= x 0) (not (p2 x y)))))""",
     """
(define-fun p1 ((x!1 Int)) Bool false)
(define-fun p2 ((x!1 Int) (x!2 Int)) Bool false)"""),

    ("trivial-all-false",
     """
(declare-fun p0 () Bool)
(declare-fun p1 (Int) Bool)
(declare-fun p2 (Int Int) Bool)
(assert (not p0))
(assert (forall ((x Int)) (not (p1 x))))
(assert (forall ((x Int) (y Int)) (not (p2 x y))))""",
     """
(define-fun p0 () Bool false)
(define-fun p1 ((x!1 Int)) Bool false)
(define-fun p2 ((x!1 Int) (x!2 Int)) Bool false)"""),

    ("simple-multiple-predicate-lists",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 5) (p x))))
(assert (forall ((x Int)) (=> (= x 6) (p x))))
(assert (forall ((x Int)) (=> (<= x 2) (p x))))
(assert (forall ((x Int)) (=> (>= x 9) (p x))))
(assert (forall ((x Int)) (__pred__p x)))
(assert (forall ((x Int)) (=> (= x 5) (__pred__p x))))
(assert (forall ((x Int)) (=> (and (= x 6) (<= x 2) (>= x 9)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (= x!1 5) (= x!1 6) (<= x!1 2) (>= x!1 9)))"""),

    ("simple-literal-head",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p 0)))
(assert (forall ((x Int)) (p 1)))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 1)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (= x!1 0) (= x!1 1)))"""),

    ("simple-duplicate-var-head",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int)) (p x x)))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (= x!1 x!2))"""),

    ("simple-complex-body",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (<= x 5) (>= y 3) (<= y 7)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (<= x 5) (>= y 3) (<= y 7)) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (and (<= x!1 5) (>= x!1 0) (<= x!2 7) (>= x!2 3)))"""),

    ("simple-overlapping-preds-1",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 1) (p x))))
(assert (forall ((x Int)) (=> (<= x 2) (p x))))
(assert (forall ((x Int)) (=> (<= x 3) (p x))))
(assert (forall ((x Int)) (=> (<= x 4) (p x))))
(assert (forall ((x Int)) (=> (and (<= x 2) (<= x 3) (<= x 4)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 4))"""),

    ("simple-overlapping-preds-2",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 4) (p x))))
(assert (forall ((x Int)) (=> (<= x 3) (p x))))
(assert (forall ((x Int)) (=> (<= x 2) (p x))))
(assert (forall ((x Int)) (=> (<= x 1) (p x))))
(assert (forall ((x Int)) (=> (and (<= x 2) (<= x 3) (<= x 4)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 4))"""),

    ("simple-duplicate-preds",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 0) (= x 0)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (= x!1 0))"""),

    ("simple-redundant-preds",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (and (= x 0) (<= x 0) (>= x 0)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (= x!1 0))"""),

    ("infer-constants-seq",
     """
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun s () Bool)
(assert p)
(assert (=> p q))
(assert (=> q r))
(assert (not s))""",
     """
(define-fun p () Bool true)
(define-fun q () Bool true)
(define-fun r () Bool true)
(define-fun s () Bool false)"""),

    ("infer-constants-tree",
     """
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun s () Bool)
(assert p)
(assert q)
(assert (=> (and p q) r))
(assert (not s))""",
     """
(define-fun p () Bool true)
(define-fun q () Bool true)
(define-fun r () Bool true)
(define-fun s () Bool false)"""),

    ("infer-constants-unreach",
     """
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun s () Bool)
(assert p)
(assert (=> (and p q) r))
(assert (not s))""",
     """
(define-fun p () Bool true)
(define-fun q () Bool false)
(define-fun r () Bool false)
(define-fun s () Bool false)"""),

    ("infer-discrete",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (p 0))
(assert (=> (p 0) (p 2)))
(assert (=> (p 2) (p 4)))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 1) (= x 2) (= x 3) (= x 4)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (= x!1 0) (= x!1 2) (= x!1 4)))"""),

    ("infer-infinite",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (p 0))
(assert (forall ((x Int)) (=> (p x) (p (+ x 1)))))
(assert (forall ((x Int)) (=> (and (= x 0) (>= x 1)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (= x!1 0) (>= x!1 1)))"""),

    ("infer-multiple-parents",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (p 4))
(assert (p 5))
(assert (forall ((a Int) (b Int) (c Int)) (=> (and (p a) (p b) (p c) (distinct a b)) (p (+ a (+ b c))))))
(assert (forall ((x Int)) (=> (and (= x 4) (= x 5) (= x 13) (= x 14) (= x 21) (>= x 22)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (= x!1 4) (= x!1 5) (= x!1 13) (= x!1 14) (>= x!1 22) (= x!1 21)))"""),

    ("infer-non-integers",
     """
(declare-fun p (Bool Real) Bool)
(declare-fun __pred__p (Bool Real) Bool)
(assert (p true 0.0))
(assert (forall ((y Real)) (=> (p true y) (p false (- 1.0 y)))))
(assert (forall ((x Bool) (y Real)) (=> (and (= x true) (= x false) (<= y 0.0) (>= y 1.0)) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Bool) (x!2 Real)) Bool (or (and (= x!1 true) (<= x!2 0.0)) (and (= x!1 false) (>= x!2 1.0))))"""),
]

norefine_unsat_tests = [
    ("empty",
     """
(assert false)"""),

    ("trivial-0",
     """
(declare-fun p () Bool)
(assert p)
(assert (not p))"""),

    ("trivial-1",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (not (p x))))"""),

    ("trivial-2",
     """
(declare-fun p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int) (y Int)) (not (p x y))))"""),

    ("infer-discrete",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (p 0))
(assert (=> (p 0) (p 2)))
(assert (=> (p 2) (p 4)))
(assert (not (p 4)))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 1) (= x 2) (= x 3) (= x 4)) (__pred__p x))))"""),
]

norefine_t_sat_tests = [
    ("empty-true-constraint",
     """
(declare-fun __temp__extra__ () Bool)
(assert (=> (= true true) __temp__extra__))""",
     ""),

    ("no-extra",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) (> x 0))))
(assert (forall ((x Int)) (=> (>= x 7) (__pred__p x))))
(assert (forall ((x Int)) (=> (= x 7) (__temp__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (>= x!1 7))"""),

    ("extra-no-params",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(declare-fun __temp__extra__ () Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) (> x 0))))
(assert (forall ((x Int)) (=> (>= x 7) (__pred__p x))))
(assert (=> (= true true) __temp__extra__))
(assert (forall ((x Int)) (=> (= x 7) (__temp__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (>= x!1 7))"""),

    ("extra-unique-solution",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(declare-fun __temp__extra__ (Int Int) Bool)
(declare-fun __temp__p (Int Int Int) Bool)
(assert (forall ((x Int)) (=> (p x) (> x 0))))
(assert (forall ((x Int)) (=> (>= (* 5 x) 11) (__pred__p x))))
(assert (forall ((a Int) (b Int)) (=> (and (= a 5) (= b 15)) (__temp__extra__ a b))))
(assert (forall ((x Int) (a Int) (b Int)) (=> (= (* a x) b) (__temp__p x a b))))""",
     """
(define-fun p ((x!1 Int)) Bool (>= (* 5 x!1) 11))"""),

    ("extra-any-solution",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(declare-fun __temp__extra__ (Int Int) Bool)
(declare-fun __temp__p (Int Int Int) Bool)
(assert (forall ((x Int)) (=> (p x) (> x -5))))
(assert (forall ((x Int)) (=> (> x 0) (__pred__p x))))
(assert (forall ((a Int) (b Int)) (=> (and (> a 0) (> b 0)) (__temp__extra__ a b))))
(assert (forall ((x Int) (a Int) (b Int)) (=> (= (* a x) b) (__temp__p x a b))))""",
     """
(define-fun p ((x!1 Int)) Bool (> x!1 0))"""),

    ("extra-non-int-params",
     """
(declare-fun p (Real Bool) Bool)
(declare-fun __pred__p (Real Bool) Bool)
(declare-fun __temp__extra__ (Real Bool) Bool)
(declare-fun __temp__p (Real Bool Real Bool) Bool)
(assert (forall ((x Real) (y Bool)) (=> (p x y) (and (> x 0.0) (= y true)))))
(assert (forall ((x Real) (y Bool)) (=> (and (> x 3.0) (= y true)) (__pred__p x y))))
(assert (forall ((a Real) (b Bool)) (=> (and (= a 5.0) (= b true)) (__temp__extra__ a b))))
(assert (forall ((x Real) (y Bool) (a Real) (b Bool)) (=> (and (> x a) (= y b)) (__temp__p x y a b))))""",
     """
(define-fun p ((x!1 Real) (x!2 Bool)) Bool (and (= x!2 true) (> x!1 3.0)))"""),
]

norefine_t_unsat_tests = [
    ("empty-false-constraint",
     """
(declare-fun __temp__extra__ () Bool)
(assert (=> (= true false) __temp__extra__))"""),
]

refine_sat_tests = [
    ("simple-refine-once",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (not (p x)))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))"""), # note that this is just one of multiple resonable solutions

    ("simple-refine-twice",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (= x 2) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (not (p x)))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (<= x!1 0) (>= x!1 2)))"""), # note that this is just one of multiple resonable solutions

    ("simple-literal-head",
     """
(declare-fun p (Int) Bool)
(assert (p 0))
(assert (not (p 1)))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))"""),

    ("templ",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(declare-fun __pred__q (Int) Bool)
(declare-fun __temp__extra__ (Int) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (forall ((x Int)) (=> (p x) (q x))))
(assert (forall ((x Int)) (=> (= x 3) (q x))))
(assert (forall ((x Int)) (=> (not (= x 3)) (not (q x)))))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 1) (= x 2) (= x 3) (= x 4) (= x 5) (= x 6) (= x 7) (= x 8) (= x 9)) (__pred__p x))))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 1) (= x 2) (= x 3) (= x 4) (= x 5) (= x 6) (= x 7) (= x 8) (= x 9)) (__pred__q x))))
(assert (forall ((a Int)) (=> (and (>= a 0) (<= a 9)) (__temp__extra__ a))))
(assert (forall ((x Int) (a Int)) (=> (= x a) (__temp__p x a))))""",
     """
(define-fun p ((x!1 Int)) Bool (= x!1 3))
(define-fun q ((x!1 Int)) Bool (= x!1 3))"""),
]

refine_unsat_tests = [
    ("simple",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (and (p 0) (= x 1)) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (not (p x)))))"""),

    ("templ",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 7) (not (p x)))))
(assert (forall ((x Int)) (=> (>= x 7) (__pred__p x))))
(assert (forall ((x Int)) (=> (= x 7) (__temp__p x))))"""),
]

refine_unknown_tests = [
    ("non-linear",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (= (mod x 2) 0) (p x))))
(assert (forall ((x Int)) (=> (= (mod x 2) 1) (not (p x)))))""",
     "incomplete"),
]

allNames = set()

def write_test_smt2(testname, code, postsat_code):
    assert testname not in allNames
    allNames.add(testname)
    filename = testname + ".smt2"
    with open(filename, "w") as f:
        f.write("(set-logic HORN)\n")
        f.write(code + "\n\n")
        f.write("(check-sat)\n")
        f.write(postsat_code + "\n")

def write_sat_test_smt2(testname, code):
    write_test_smt2(testname, code, "(get-model)")

def write_unsat_test_smt2(testname, code):
    write_test_smt2(testname, code, "") # "(get-proof)" # XXX Proofs are not currently supported.

def write_unknown_test_smt2(testname, code):
    write_test_smt2(testname, code, "(get-info :reason-unknown)")

def write_test_out(testname, result, postsat_code):
    assert testname in allNames
    filename = testname + ".out"
    with open(filename, "w") as f:
        f.write(result + "\n")
        f.write(postsat_code + "\n")

def write_sat_test_out(testname, model):
    write_test_out(testname, "sat", "(model " + model + "\n)")

def write_unsat_test_out(testname):
    write_test_out(testname, "unsat", "")

def write_unknown_test_out(testname, errmsg):
    write_test_out(testname, "unknown", "(:reason-unknown " + errmsg + ")")

for test in inpval_tests:
    (name, code, errmsg) = test
    testname = "inpval-" + name
    write_unknown_test_smt2(testname, code)
    write_unknown_test_out(testname, errmsg)

for test in norefine_sat_tests:
    (name, code, model) = test
    testname = "norefine-sat-" + name
    write_sat_test_smt2(testname, code)
    write_sat_test_out(testname, model)

for test in norefine_unsat_tests:
    (name, code) = test
    testname = "norefine-unsat-" + name
    write_unsat_test_smt2(testname, code)
    write_unsat_test_out(testname)

for test in norefine_t_sat_tests:
    (name, code, model) = test
    testname = "norefine-templ-sat-" + name
    write_sat_test_smt2(testname, code)
    write_sat_test_out(testname, model)

for test in norefine_t_unsat_tests:
    (name, code) = test
    testname = "norefine-templ-unsat-" + name
    write_unsat_test_smt2(testname, code)
    write_unsat_test_out(testname)

for test in refine_sat_tests:
    (name, code, model) = test
    testname = "refine-sat-" + name
    write_sat_test_smt2(testname, code)
    write_sat_test_out(testname, model)

for test in refine_unsat_tests:
    (name, code) = test
    testname = "refine-unsat-" + name
    write_unsat_test_smt2(testname, code)
    write_unsat_test_out(testname)

for test in refine_unknown_tests:
    (name, code, errmsg) = test
    testname = "refine-unknown-" + name
    write_unknown_test_smt2(testname, code)
    write_unknown_test_out(testname, errmsg)
