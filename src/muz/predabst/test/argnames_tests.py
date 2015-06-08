# This file contains tests that involve argument names.  Each of the test cases
# involves two predicates p and q, some of whose arguments are named; predicate
# refinement generates a predicate for p, which may or may not be translated to
# a predicate for q depending on the argument naming used in the test case.

sat_tests = [
    # p and q have a single argument with the same name; the predicate should be
    # copied.
    ("one-arg-same-name",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __name__a (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
(assert (forall ((x Int)) (=> (> x 0) (not (p x)))))
(assert (forall ((x Int)) (=> (<= x 0) (q x))))
(assert (forall ((x Int)) (=> (__name__a x) (__names__p x))))
(assert (forall ((x Int)) (=> (__name__a x) (__names__q x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))
(define-fun q ((x!1 Int)) Bool (<= x!1 0))"""),

    # p and q have a single argument with different names; the predicate should
    # not be copied.
    ("one-arg-different-name",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__b (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
(assert (forall ((x Int)) (=> (> x 0) (not (p x)))))
(assert (forall ((x Int)) (=> (<= x 0) (q x))))
(assert (forall ((x Int)) (=> (__name__a x) (__names__p x))))
(assert (forall ((x Int)) (=> (__name__b x) (__names__q x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))
(define-fun q ((x!1 Int)) Bool true)"""),

    # p and q have a single argument but q's argument is unnamed; the predicate
    # should not be copied.
    ("one-arg-no-name",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __name__a (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
(assert (forall ((x Int)) (=> (> x 0) (not (p x)))))
(assert (forall ((x Int)) (=> (<= x 0) (q x))))
(assert (forall ((x Int)) (=> (__name__a x) (__names__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))
(define-fun q ((x!1 Int)) Bool true)"""),

    # p and q have two arguments with the same names; the predicate (which uses
    # both arguments) should be copied.
    ("two-args-same-names",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__b (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (<= x y) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (> x y) (not (p x y)))))
(assert (forall ((x Int) (y Int)) (=> (<= x y) (q x y))))
(assert (forall ((x Int) (y Int)) (=> (and (__name__a x) (__name__b y)) (__names__p x))))
(assert (forall ((x Int) (y Int)) (=> (and (__name__a x) (__name__b y)) (__names__q x))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (<= x!1 x!2))
(define-fun q ((x!1 Int) (x!2 Int)) Bool (<= x!1 x!2))"""),

    # p and q have two arguments which share one name but not the second; the
    # predicate (which uses both arguments) should not be copied.
    ("two-args-one-name-different",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__b (Int) Bool)
(declare-fun __name__c (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (<= x y) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (> x y) (not (p x y)))))
(assert (forall ((x Int) (y Int)) (=> (<= x y) (q x y))))
(assert (forall ((x Int) (y Int)) (=> (and (__name__a x) (__name__b y)) (__names__p x))))
(assert (forall ((x Int) (y Int)) (=> (and (__name__a x) (__name__c y)) (__names__q x))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (<= x!1 x!2))
(define-fun q ((x!1 Int) (x!2 Int)) Bool true)"""),

    # p and q have two arguments with the same names but swapped; the predicate
    # (which uses both arguments) should be translated.
    ("two-args-swapped-names",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__b (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (<= x y) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (> x y) (not (p x y)))))
(assert (forall ((x Int) (y Int)) (=> (<= y x) (q x y))))
(assert (forall ((x Int) (y Int)) (=> (and (__name__a x) (__name__b y)) (__names__p x))))
(assert (forall ((x Int) (y Int)) (=> (and (__name__b x) (__name__a y)) (__names__q x))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (<= x!1 x!2))
(define-fun q ((x!1 Int) (x!2 Int)) Bool (<= x!2 x!1))"""),

    # p and q have two arguments but only one of p's arguments is named; the
    # predicate (which uses both arguments) should not be copied.
    ("pred-uses-unnamed-arg",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__b (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (<= x y) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (> x y) (not (p x y)))))
(assert (forall ((x Int) (y Int)) (=> (<= x y) (q x y))))
(assert (forall ((x Int) (y Int)) (=> (__name__a x) (__names__p x))))
(assert (forall ((x Int) (y Int)) (=> (and (__name__a x) (__name__b y)) (__names__q x))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (<= x!1 x!2))
(define-fun q ((x!1 Int) (x!2 Int)) Bool true)"""),

    # p and q have two arguments but only one of p's arguments is named; the
    # predicate (which uses only the named argument) should be copied.
    ("pred-uses-only-named-arg",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__b (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (<= x 0) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (> x 0) (not (p x y)))))
(assert (forall ((x Int) (y Int)) (=> (<= x 0) (q x y))))
(assert (forall ((x Int) (y Int)) (=> (__name__a x) (__names__p x))))
(assert (forall ((x Int) (y Int)) (=> (and (__name__a x) (__name__b y)) (__names__q x))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (<= x!1 0))
(define-fun q ((x!1 Int) (x!2 Int)) Bool (<= x!1 0))"""),

    # Multiple argument name lists (with lengths 0, 1, >1) should be allowed for
    # a single predicate symbol.
    ("multiple-argument-name-lists",
     """
(declare-fun p (Int Int Int) Bool)
(declare-fun q (Int Int Int) Bool)
(declare-fun __names__p (Int Int Int) Bool)
(declare-fun __names__q (Int Int Int) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__b (Int) Bool)
(declare-fun __name__c (Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (<= x y) (<= y z)) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (or (> x y) (> y z)) (not (p x y z)))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (<= x y) (<= y z)) (q x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (__names__p x y z)))
(assert (forall ((x Int) (y Int) (z Int)) (=> (__name__a x) (__names__p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (__name__b y) (__name__c z)) (__names__p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (__name__a x) (__name__b y) (__name__c z)) (__names__q x y z))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int) (x!3 Int)) (and (<= x!1 x!2) (<= x!2 x!3)) true)
(define-fun q ((x!1 Int) (x!2 Int) (x!3 Int)) (and (<= x!1 x!2) (<= x!2 x!3)) true)"""),

    # Names of arguments of one type come from a different namespace to names of
    # arguments of different types.
    ("same-name-different-types",
     """
(declare-fun p (Int Real Bool) Bool)
(declare-fun q (Int Real Bool) Bool)
(declare-fun __names__p (Int Real Bool) Bool)
(declare-fun __names__q (Int Real Bool) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__a (Real) Bool)
(declare-fun __name__a (Bool) Bool)
(assert (forall ((x Int) (y Real) (z Bool)) (=> (and (<= x 0) (<= y 0.0) z) (p x y z))))
(assert (forall ((x Int) (y Real) (z Bool)) (=> (or (> x 0) (> y 0.0) (not z)) (not (p x y z)))))
(assert (forall ((x Int) (y Real) (z Bool)) (=> (and (<= x 0) (<= y 0.0) z) (q x y z))))
(assert (forall ((x Int) (y Real) (z Bool)) (=> (and (__name__a x) (__name__a y) (__name__a z)) (__names__p x y z))))
(assert (forall ((x Int) (y Real) (z Bool)) (=> (and (__name__a x) (__name__a y) (__name__a z)) (__names__q x y z))))""",
     """
(define-fun p ((x!1 Int) (x!2 Real) (x!3 Bool)) (and (<= x!1 0) (<= x!2 0.0) x!3) true)
(define-fun p ((x!1 Int) (x!2 Real) (x!3 Bool)) (and (<= x!1 0) (<= x!2 0.0) x!3) true)"""),

    # p and q have a single argument with the same name, but q's argument is
    # explicit; the argument name should be ignored so the predicate should not
    # be copied.
    ("explicit-arg",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun __expargs__q (Int) Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__q (Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(declare-fun __name__a (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
(assert (forall ((x Int)) (=> (> x 0) (not (p x)))))
(assert (forall ((x Int)) (=> (<= x 0) (q x))))
(assert (forall ((x Int)) (=> (__exparg__ x) (__expargs__q x))))
(assert (forall ((x Int)) (=> (__name__a x) (__names__p x))))
(assert (forall ((x Int)) (=> (__name__a x) (__names__q x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))
(define-fun q ((x!1 Int)) Bool (= x!1 0))"""),

    # Multiple predicates with the same name but different arity and/or argument
    # types should be allowed.
    ("preds-same-name",
     """
(declare-fun p () Bool)
(declare-fun p (Int) Bool)
(declare-fun p (Real) Bool)
(declare-fun p (Int Int) Bool)
(declare-fun __names__p () Bool)
(declare-fun __names__p (Int) Bool)
(declare-fun __names__p (Real) Bool)
(declare-fun __names__p (Int Int) Bool)
(declare-fun __name__a (Int) Bool)
(declare-fun __name__b (Real) Bool)
(declare-fun __name__c (Int) Bool)
(assert p)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Real)) (p x)))
(assert (forall ((x Int) (y Int)) (p x y)))
(assert __names__p)
(assert (forall ((x Int)) (=> (__name__a x) (__names__p x))))
(assert (forall ((x Real)) (=> (__name__b x) (__names__p x))))
(assert (forall ((x Int) (y Int)) (=> (__name__c x) (__names__p x y))))""",
     """
(define-fun p () Bool true)
(define-fun p ((x!1 Int)) Bool true)
(define-fun p ((x!1 Real)) Bool true)
(define-fun p ((x!1 Int) (x!2 Int)) Bool true)"""),
]

argnames_tests = (sat_tests, [], [])
