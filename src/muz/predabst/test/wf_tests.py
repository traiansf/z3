# This file contains tests that involve WF predicate symbols (and may also
# involve templates).

sat_tests = [
    ("arity-0",
     """
(declare-fun __wf__p () Bool)
(assert (not __wf__p))""",
     """
(define-fun __wf__p () Bool false)"""),

    ("trivial-always-false",
     """
(declare-fun __wf__p (Int Int) Bool)
(assert (forall ((x Int) (x_ Int)) (not (__wf__p x x_))))""",
     """
(define-fun __wf__p ((x!1 Int) (x!2 Int)) Bool false)"""),

    ("simple",
     """
(declare-fun __wf__p (Int Int) Bool)
(declare-fun __pred____wf__p (Int Int) Bool)
(assert (forall ((x Int) (x_ Int)) (=> (and (>= x 0) (< x_ x)) (__wf__p x x_))))
(assert (forall ((x Int) (x_ Int)) (=> (and (>= x 0) (< x_ x)) (__pred____wf__p x x_))))""",
     """
(define-fun __wf__p ((x!1 Int) (x!2 Int)) Bool (and (< x!2 x!1) (>= x!1 0)))"""),

    # The explicit arguments are irrelevant for proving well-foundedness.
    ("simple-exp-args-irrelevant",
     """
(declare-fun __wf__p (Int Int Int Int) Bool)
(declare-fun __expargs____wf__p (Int Int Int Int) Bool)
(declare-fun __pred____wf__p (Int Int Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (x_ Int)) (=> (and (>= x 0) (< x_ x)) (__wf__p x 0 x_ 0))))
(assert (forall ((x Int) (y Int) (x_ Int) (y_ Int)) (=> (and (__exparg__ y) (__exparg__ y_)) (__expargs____wf__p x y x_ y_))))
(assert (forall ((x Int) (y Int) (x_ Int) (y_ Int)) (=> (and (>= x 0) (< x_ x)) (__pred____wf__p x y x_ y_))))""",
     """
(define-fun __wf__p ((x!1 Int) (x!2 Int) (x!3 Int) (x!4 Int)) Bool (and (= x!2 0) (= x!4 0) (< x!3 x!1) (>= x!1 0)))"""),

    # The explicit arguments are essential for proving well-foundedness.
    ("simple-exp-args-essential",
     """
(declare-fun __wf__p (Int Int Int Int) Bool)
(declare-fun __expargs____wf__p (Int Int Int Int) Bool)
(declare-fun __pred____wf__p (Int Int Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (x_ Int)) (=> (and (>= x 0) (< x x_)) (__wf__p x 0 x_ 1))))
(assert (forall ((x Int) (y Int) (x_ Int) (y_ Int)) (=> (and (__exparg__ y) (__exparg__ y_)) (__expargs____wf__p x y x_ y_))))
(assert (forall ((x Int) (y Int) (x_ Int) (y_ Int)) (=> (and (>= x 0) (> x_ x)) (__pred____wf__p x y x_ y_))))""",
     """
(define-fun __wf__p ((x!1 Int) (x!2 Int) (x!3 Int) (x!4 Int)) Bool (and (= x!2 0) (= x!4 1) (< x!1 x!3) (>= x!1 0)))"""),

    ("refine",
     """
(declare-fun __wf__p (Int Int) Bool)
(assert (forall ((x Int) (x_ Int)) (=> (and (>= x 0) (< x_ x)) (__wf__p x x_))))""",
     """
(define-fun __wf__p ((x!1 Int) (x!2 Int)) Bool (and (>= x!1 0) (< x!2 x!1)))"""),

    ("refine-evars",
     """
(declare-fun __wf__p (Int Int) Bool)
     (assert (forall ((x Int) (x_ Int) (y Int)) (=> (and (>= x 0) (< x_ y) (<= y x)) (__wf__p x x_))))""",
     """
(define-fun __wf__p ((x!1 Int) (x!2 Int)) Bool (and (>= x!1 0) (< x!2 x!1)))"""),
]

unsat_tests = [
    ("arity-0",
     """
(declare-fun __wf__p () Bool)
(assert __wf__p)"""),

    ("trivial-always-true",
     """
(declare-fun __wf__p (Int Int) Bool)
(assert (forall ((x Int) (x_ Int)) (__wf__p x x_)))"""),

    ("trivial-first-equal-zero",
     """
(declare-fun __wf__p (Int Int) Bool)
(assert (forall ((x Int) (x_ Int)) (=> (= x 0) (__wf__p x x_))))"""),

    ("trivial-second-equal-zero",
     """
(declare-fun __wf__p (Int Int) Bool)
(assert (forall ((x Int) (x_ Int)) (=> (= x_ 0) (__wf__p x x_))))"""),

    ("always-true-indirectly",
     """
(declare-fun __wf__p (Int Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int) (x_ Int)) (=> (and (q x) (q x_)) (__wf__p x x_))))
(assert (forall ((x Int)) (q x)))"""),

    ("templ-refine-non-head-vars",
     """
(declare-fun __wf__p (Int Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __temp__q (Int) Bool)
(assert (forall ((x Int) (x_ Int) (y Int) (y_ Int)) (=> (and (= x y) (= x_ y_)) (__wf__p x x_))))
(assert (forall ((x Int)) (=> (q x) (= true true))))
(assert (forall ((x Int)) (=> (= x 0) (__temp__q x))))"""),
]

unknown_tests = [
    ("non-linear",
     """
(declare-fun __wf__p (Int Int) Bool)
(assert (forall ((x Int) (x_ Int)) (=> (and (> x 2) (= x_ (mod x 2))) (__wf__p x x_))))""",
     "incomplete"),

    # The node is well-founded (the graph of p is {(1,1,1,0), (3,5,4,0), (4,5,3,0)}), but the solver
    # is not able to determine this.
    ("pythagoras-wf",
     """
(declare-fun __wf__p (Int Int Int Int) Bool)
(declare-fun __pred____wf__p (Int Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> z 0) (<= z 5) (= (+ (* x x) (* y y)) (* z z)))) (__wf__p x z y 0))))
(assert (forall ((x Int) (y Int) (z Int) (w Int)) (=> (and (> z 0) (<= z 5) (= (+ (* x x) (* y y)) (* z z)))) (__pred____wf__p x z y w))))""",
     "underlying solver incomplete"),

    # The node is not well-founded (the graph of p is {(1,1,1,5), (3,5,4,5), (4,5,3,5)}, which
    # admits a cycle), but the solver is not able to determine this.
    ("pythagoras-not-wf",
     """
(declare-fun __wf__p (Int Int Int Int) Bool)
(declare-fun __pred____wf__p (Int Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> z 0) (<= z 5) (= (+ (* x x) (* y y)) (* z z)))) (__wf__p x z y 5))))
(assert (forall ((x Int) (y Int) (z Int) (w Int)) (=> (and (> z 0) (<= z 5) (= (+ (* x x) (* y y)) (* z z)))) (__pred____wf__p x z y w))))""",
     "underlying solver incomplete"),

    # The node is reachable without abstraction (>>> obvious?); however it is not well-founded
    # without abstraction (the graph of p is {(1,1,1,0), (3,5,4,0), (4,5,3,0)}), but the solver is
    # not able to determine this.
    ("pythagoras-refine-wf",
     """
(declare-fun __wf__p (Int Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> z 0) (<= z 5) (= (+ (* x x) (* y y)) (* z z)))) (__wf__p x z y 0))))""",
     "underlying solver incomplete"),

    # The node is reachable without abstraction (>>> obvious?); however it is not well-founded
    # without abstraction (the graph of p is {(1,1,1,5), (3,5,4,5), (4,5,3,5)}, which admits a
    # cycle), but the solver is not able to determine this.
    ("pythagoras-refine-not-wf",
     """
(declare-fun __wf__p (Int Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> z 0) (<= z 5) (= (+ (* x x) (* y y)) (* z z)))) (__wf__p x z y 5))))""",
     "underlying solver incomplete"),
]

wf_tests = (sat_tests, unsat_tests, unknown_tests)
