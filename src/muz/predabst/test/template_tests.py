# This file contains tests that involve templates but do not involve WF
# predicate symbols.

sat_tests = [
    ("empty-true-constraint",
     """
(declare-fun __temp__extra__ () Bool)
(assert __temp__extra__)""",
     ""),

    # No extra template constraint present.
    ("no-extra",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) (> x 0))))
(assert (forall ((x Int)) (=> (= x 7) (__temp__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (= x!1 7))"""),

    # An extra template constraint is present, but it has no parameters.
    ("extra-no-params",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__extra__ () Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) (> x 0))))
(assert __temp__extra__)
(assert (forall ((x Int)) (=> (= x 7) (__temp__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (= x!1 7))"""),

    # The extra template constraint is present has a unique solution.
    ("extra-unique-solution",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__extra__ (Int Int) Bool)
(declare-fun __temp__p (Int Int Int) Bool)
(assert (forall ((x Int)) (=> (p x) (> x 0))))
(assert (forall ((a Int) (b Int)) (=> (and (= a 5) (= b 15)) (__temp__extra__ a b))))
(assert (forall ((x Int) (a Int) (b Int)) (=> (= (* a x) b) (__temp__p x a b))))""",
     """
(define-fun p ((x!1 Int)) Bool (= (* 5 x!1) 15))"""),

    # The extra template constraint has multiple solutions, but any one of them
    # will do.
    ("extra-any-solution",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__extra__ (Int Int) Bool)
(declare-fun __temp__p (Int Int Int) Bool)
(assert (forall ((x Int)) (=> (p x) (> x 0))))
(assert (forall ((a Int) (b Int)) (=> (and (> a 0) (> b 0)) (__temp__extra__ a b))))
(assert (forall ((x Int) (a Int) (b Int)) (=> (= (* a x) b) (__temp__p x a b))))""",
     """
(define-fun p ((x!1 Int)) Bool (= (* 1 x!1) 1))"""),

    # The extra template parameters are not integers.
    ("extra-non-int-params",
     """
(declare-fun p (Real Bool) Bool)
(declare-fun __temp__extra__ (Real Bool) Bool)
(declare-fun __temp__p (Real Bool Real Bool) Bool)
(assert (forall ((x Real) (y Bool)) (=> (p x y) (and (> x 0.0) (= y true)))))
(assert (forall ((a Real) (b Bool)) (=> (and (= a 5.0) (= b true)) (__temp__extra__ a b))))
(assert (forall ((x Real) (y Bool) (a Real) (b Bool)) (=> (and (> x a) (= y b)) (__temp__p x y a b))))""",
     """
(define-fun p ((x!1 Real) (x!2 Bool)) Bool (and (= x!2 true) (> x!1 5.0)))"""),

    # A templated predicate symbol appears at the head of a rule.
    ("head",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (>= x 3) (p x))))
(assert (forall ((x Int)) (=> (>= x 0) (__temp__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (>= x!1 0))"""),

    ("refine-preds-other",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (> x 0) (q x))))
(assert (forall ((x Int)) (=> (and (p x) (q x)) false)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))""",
     """
(define-fun q ((x!1 Int)) Bool (> x!1 0))
(define-fun p ((x!1 Int)) Bool (= x!1 0))"""),

    ("refine-head",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__extra__ (Int) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 3) (p x))))
(assert (forall ((a Int)) (=> (= true true) (__temp__extra__ a))))
(assert (forall ((x Int) (a Int)) (=> (= x a) (__temp__p x a))))""",
     """
(define-fun p ((x!1 Int)) Bool (= x!1 3))"""),

    # Multiple predicates with the same name but different arity and/or argument
    # types should be allowed.
    ("misc-preds-same-name",
     """
(declare-fun p () Bool)
(declare-fun p (Int) Bool)
(declare-fun p (Real) Bool)
(declare-fun p (Int Int) Bool)
(declare-fun __temp__p () Bool)
(declare-fun __temp__p (Int) Bool)
(declare-fun __temp__p (Real) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (=> (= true false) (as p (Bool))))
(assert (forall ((x Int)) (=> (= true false) (p x))))
(assert (forall ((x Real)) (=> (= true false) (p x))))
(assert (forall ((x Int) (y Int)) (=> (= true false) (p x y))))
(assert (as __temp__p (Bool)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))
(assert (forall ((x Real)) (=> (= x 1.0) (__temp__p x))))
(assert (forall ((x Int) (y Int)) (=> (= x 2) (__temp__p x y))))""",
     """
(define-fun p () Bool true)
(define-fun p ((x!1 Int)) Bool (= x!1 0))
(define-fun p ((x!1 Real)) Bool (= x!1 1.0))
(define-fun p ((x!1 Int) (x!2 Int)) Bool (= x!1 2))"""),
]

unsat_tests = [
    # The extra template constraint has no solution.
    ("empty-false-constraint",
     """
(declare-fun __temp__extra__ () Bool)
(assert (=> (= true false) __temp__extra__))"""),

    # Unsatisfiable, and no template refinement is possible.
    ("refine",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 7) (not (p x)))))
(assert (forall ((x Int)) (=> (= x 7) (__temp__p x))))"""),
]

unknown_tests = [
    # The extra template constraint has a solution, but one which the solver is
    # unable to find.
    ("empty-pythagoras-constraint",
     """
(declare-fun __temp__extra__ (Int Int Int) Bool)
(assert (forall ((a Int) (b Int) (c Int)) (=> (and (> a 0) (> b 0) (> c 0) (= (+ (* a a) (* b b)) (* c c))) (__temp__extra__ a b c))))""",
     "(underlying-solver (incomplete (theory arithmetic)))"),
]

template_tests = (sat_tests, unsat_tests, unknown_tests)
