# This file contains tests that involve neither templates nor WF predicate
# symbols nor argument names.

# Nomenclature
# ------------
# empty:   no rules.
# trivial: rules have no uninterpreted body (so the node graph has no edges),
#          and no predicates or explicit arguments (so each cube is either true
#          or false).
# simple:  rules have no uninterpreted body (so the node graph has no edges),
#          but either predicates and/or explicit arguments.
# infer:   rules have uninterpreted body (so the node graph has edges).
# refine:  predicate refinement is necessary.

# >>> for each of these, should also have the test where the predicate is supplied up-front.
# >>> including when it won't be discovered by refinement.
def make_pred_refine_test(name, arity, pred, modelPred, argType="Int"):
    def arg(i):
        return chr(ord("x") + i)
    types = " ".join([argType for i in range(arity)])
    binders = " ".join(["(%s %s)" % (arg(i), argType) for i in range(arity)])
    args = " ".join([arg(i) for i in range(arity)])

    def modelName(i):
        return ("x!%d" % (i + 1))
    modelBinders = " ".join(["(%s %s)" % (modelName(i), argType) for i in range(arity)])

    code = """
(declare-fun p (%s) Bool)
(assert (forall (%s) (=> %s (p %s))))
(assert (forall (%s) (=> (not %s) (not (p %s)))))""" % (types, binders, pred, args, binders, pred, args)

    if modelPred:
        model = """
(define-fun p (%s) Bool %s)""" % (modelBinders, modelPred)
        return ("refine-pred-%s" % name, code, model)
    else:
        return ("refine-pred-%s" % name, code, "incomplete")

sat_tests = [
    ("empty", # >>> check that this goes to predabst
     "",
     ""),

    # The predicate symbols (of arity 0, 1, 2) are unconstrained.
    ("trivial-unconstrained",
     """
(declare-fun p0 () Bool)
(declare-fun p1 (Int) Bool)
(declare-fun p2 (Int Int) Bool)
(assert (=> (= true false) p0))
(assert (forall ((x Int)) (=> (= true false) (p1 x))))
(assert (forall ((x Int) (y Int)) (=> (= true false) (p2 x y))))""",
     """
(define-fun p0 () Bool false)
(define-fun p1 ((x!1 Int)) Bool false)
(define-fun p2 ((x!1 Int) (x!2 Int)) Bool false)"""),

    # The predicate symbols (of arity 0, 1, 2) are constrained to be true over
    # all values in their domain.
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

    # The predicate symbols (of arity 1, 2) are constrained to be true for some
    # values in their domain.
    ("trivial-some-true",
     """
(declare-fun p1 (Int) Bool)
(declare-fun p2 (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p1 x))))
(assert (forall ((x Int) (y Int)) (=> (= x 0) (p2 x y))))""",
     """
(define-fun p1 ((x!1 Int)) Bool true)
(define-fun p2 ((x!1 Int) (x!2 Int)) Bool true)"""),

    # The predicate symbols (of arity 1, 2) are constrained to be false for some
    # values in their domain.
    ("trivial-some-false",
     """
(declare-fun p1 (Int) Bool)
(declare-fun p2 (Int Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (not (p1 x)))))
(assert (forall ((x Int) (y Int)) (=> (= x 0) (not (p2 x y)))))""",
     """
(define-fun p1 ((x!1 Int)) Bool false)
(define-fun p2 ((x!1 Int) (x!2 Int)) Bool false)"""),

    # The predicate symbols (of arity 0, 1, 2) are constrained to be false for
    # all values in their domain.
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

    # Multiple predicate lists (with lengths 0, 1, >1) should be allowed for a
    # single predicate symbol.
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

    # Duplicate predicates should be eliminated.
    ("simple-duplicate-preds",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 0) (= x 0)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (= x!1 0))"""),

    # Equivalent predicates should be normalized and eliminated.
    ("simple-equivalent-preds",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
     (assert (forall ((x Int)) (=> (and (<= x 0) (>= 0 x) (< x 1) (> 1 x) (<= (+ x 1) 1) (>= (- x) 0)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))"""),

    # Rules with a literal head argument.
    ("simple-literal-head",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p 0)))
(assert (forall ((x Int)) (p 1)))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 1)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (= x!1 0) (= x!1 1)))"""),

    # A rule with the same variable used multiple times as a head argument.
    ("simple-duplicate-var-head",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int)) (p x x)))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (= x!1 x!2))"""),

    # A rule that generates a cube that is a conjunction of multiple predicates.
    ("simple-complex-body",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (<= x 5) (>= y 3) (<= y 7)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (<= x 5) (>= y 3) (<= y 7)) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (and (<= x!1 5) (>= x!1 0) (<= x!2 7) (>= x!2 3)))"""),

    # Two rules that generate identical cubes.
    ("simple-identical-cubes",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
(assert (forall ((x Int)) (=> (<= x 0) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))"""),

    # Multiple rules that generate cubes that subsume one another.
    ("simple-overlapping-preds-1",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 1) (p x))))
(assert (forall ((x Int)) (=> (= x 2) (p x))))
(assert (forall ((x Int)) (=> (<= x 3) (p x))))
(assert (forall ((x Int)) (=> (<= x 4) (p x))))
(assert (forall ((x Int)) (=> (and (= x 1) (= x 2) (<= x 3) (<= x 4)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 4))"""),

    # As above, but with the rules listed (and therefore (hopefully) with the
    # cubes generated) in the opposite order.
    ("simple-overlapping-preds-2",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 4) (p x))))
(assert (forall ((x Int)) (=> (<= x 3) (p x))))
(assert (forall ((x Int)) (=> (= x 2) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (p x))))
(assert (forall ((x Int)) (=> (and (= x 1) (= x 2) (<= x 3) (<= x 4)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 4))"""),

    # A predicate symbol with non-integer arguments.
    ("simple-non-integers",
     """
(declare-fun p (Bool Real) Bool)
(declare-fun __pred__p (Bool Real) Bool)
(assert (p true 0.0))
(assert (forall ((x Bool) (y Real)) (=> (and (not x) (= y 1.0)) (p x y))))
(assert (forall ((x Bool) (y Real)) (=> (and x (not x) (<= y 0.0) (>= y 1.0)) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Bool) (x!2 Real)) Bool (or (and x!1 (<= x!2 0.0)) (and (not x!1) (>= x!2 1.0))))"""),

    # A predicate symbol with a single explicit argument.
    ("simple-exp-eval-single",
     """
(declare-fun p (Int) Bool)
(declare-fun __expargs__p (Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (p x))))
(assert (forall ((x Int)) (=> (__exparg__ x) (__expargs__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (= x!1 0) (= x!1 1)))"""),

    # A predicate symbol with multiple explicit arguments.
    ("simple-exp-eval-multiple",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 2)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 1) (= y 3)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (__exparg__ x) (__exparg__ y)) (__expargs__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (or (and (= x!1 0) (= x!2 2)) (and (= x!1 1) (= x!2 3))))"""),

    # A predicate symbol with one explicit and one non-explicit argument.
    ("simple-exp-eval-mixed",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (>= y 0)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 1) (<= y 0)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (>= y 0) (<= y 0)) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (or (and (= x!1 0) (>= x!2 0)) (and (= x!1 1) (<= x!2 0))))"""),

    # A predicate symbol with explicit non-integer arguments.
    ("simple-exp-eval-non-integers",
     """
(declare-fun p (Bool Real) Bool)
(declare-fun __expargs__p (Bool Real) Bool)
(declare-fun __exparg__ (Bool) Bool)
(declare-fun __exparg__ (Real) Bool)
(assert (p true 0.0))
(assert (forall ((x Bool) (y Real)) (=> (and (not x) (= y 1.0)) (p x y))))
(assert (forall ((x Bool) (y Real)) (=> (and (__exparg__ x) (__exparg__ y)) (__expargs__p x y))))""",
     """
(define-fun p ((x!1 Bool) (x!2 Real)) Bool (or (and (= x!1 true) (= x!2 0.0)) (and (= x!1 false) (= x!2 1.0))))"""),

    # The node graph forms a linear sequence.
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

    # The node graph forms a tree; multiple rules use a single reachable
    # predicate symbol.
    ("infer-constants-tree-out",
     """
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun s () Bool)
(assert p)
(assert (=> p q))
(assert (=> p r))
(assert (not s))""",
     """
(define-fun p () Bool true)
(define-fun q () Bool true)
(define-fun r () Bool true)
(define-fun s () Bool false)"""),

    # The node graph forms a tree; a single rule uses multiple reachable
    # predicate symbols.
    ("infer-constants-tree-in",
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

    # A rule uses one reachable predicate symbol and one unreachable predicate
    # symbol.
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
(define-fun r () Bool false)
(define-fun q () Bool false)
(define-fun s () Bool false)"""),

    # A recursive predicate symbol, but with a finite set of true values.
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

    # A recursive predicate symbol, with an infinite set of true values
    # summarized by a > predicate.
    ("infer-infinite",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (p 0))
(assert (forall ((x Int)) (=> (p x) (p (+ x 1)))))
(assert (forall ((x Int)) (=> (and (= x 0) (> x 0)) (__pred__p x))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (= x!1 0) (> x!1 0)))"""),

    # A rule with multiple uninterpreted body predicates (actually just a single
    # predicate, but appearing multiple times), with multiple possible parent
    # nodes for each body predicate.
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

    # Multiple rules that generate cubes that subsume one another, at different
    # depths of the search space.
    ("infer-overlapping-preds-1",
     """
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun p3 () Bool)
(declare-fun p4 () Bool)
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert p1)
(assert (=> p1 p2))
(assert (=> p2 p3))
(assert (=> p3 p4))
(assert (forall ((x Int)) (=> (and p1 (= x 1)) (p x))))
(assert (forall ((x Int)) (=> (and p2 (= x 2)) (p x))))
(assert (forall ((x Int)) (=> (and p3 (<= x 3)) (p x))))
(assert (forall ((x Int)) (=> (and p4 (<= x 4)) (p x))))
(assert (forall ((x Int)) (=> (and (= x 1) (= x 2) (<= x 3) (<= x 4)) (__pred__p x))))""",
     """
(define-fun p1 () Bool true)
(define-fun p2 () Bool true)
(define-fun p3 () Bool true)
(define-fun p4 () Bool true)
(define-fun p ((x!1 Int)) Bool (<= x!1 4))"""),

    # As above, but with the cubes generated in the opposite order.
    ("infer-overlapping-preds-2",
     """
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun p3 () Bool)
(declare-fun p4 () Bool)
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert p1)
(assert (=> p1 p2))
(assert (=> p2 p3))
(assert (=> p3 p4))
(assert (forall ((x Int)) (=> (and p1 (<= x 4)) (p x))))
(assert (forall ((x Int)) (=> (and p2 (<= x 3)) (p x))))
(assert (forall ((x Int)) (=> (and p3 (= x 2)) (p x))))
(assert (forall ((x Int)) (=> (and p4 (= x 1)) (p x))))
(assert (forall ((x Int)) (=> (and (= x 1) (= x 2) (<= x 3) (<= x 4)) (__pred__p x))))""",
     """
(define-fun p1 () Bool true)
(define-fun p2 () Bool true)
(define-fun p3 () Bool true)
(define-fun p4 () Bool true)
(define-fun p ((x!1 Int)) Bool (<= x!1 4))"""),

    # Inference performed on predicates with non-integer arguments.
    ("infer-non-integers",
     """
(declare-fun p (Bool Real) Bool)
(declare-fun __pred__p (Bool Real) Bool)
(assert (p true 0.0))
(assert (forall ((y Real)) (=> (p true y) (p false (- 1.0 y)))))
(assert (forall ((x Bool) (y Real)) (=> (and x (not x) (<= y 0.0) (>= y 1.0)) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Bool) (x!2 Real)) Bool (or (and x!1 (<= x!2 0.0)) (and (not x!1) (>= x!2 1.0))))"""),

    # >>>
    ("infer-exp-eval",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= x 0) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (= x 1) (not (p x y)))))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (= x!1 0))"""),

    # >>>
    ("infer-exp-eval-literal-head",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((y Int)) (p 0 y)))
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (p x y)) (p 1 y))))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (or (= x!1 0) (= x!1 1)))"""),

    # >>>
    ("infer-exp-eval-literal-body",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= x 0) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 1) (p 0 y)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (or (= x!1 0) (= x!1 1)))"""),

    # >>> Important because head argument is not known in advance.
    ("infer-exp-eval-iterate",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((y Int)) (p 0 y)))
(assert (forall ((x Int) (y Int)) (=> (and (< x 2) (p x y)) (p (+ x 1) y))))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (or (= x!1 0) (= x!1 1) (= x!1 2)))"""),

    # Inference performed on predicates with non-integer explicit arguments.
    # >>> why is only one of them explicit?
    ("infer-exp-eval-non-integers",
     """
(declare-fun p (Bool Real) Bool)
(declare-fun __expargs__p (Bool Real) Bool)
(declare-fun __exparg__ (Real) Bool)
(declare-fun __pred__p (Bool Real) Bool)
(assert (p true 0.0))
(assert (forall ((y Real)) (=> (p true y) (p false (- 1.0 y)))))
(assert (forall ((x Bool) (y Real)) (=> (__exparg__ y) (__expargs__p x y))))
(assert (forall ((x Bool) (y Real)) (=> (and x (not x)) (__pred__p x y))))""",
     """
(define-fun p ((x!1 Bool) (x!2 Real)) Bool (or (and (= x!2 0.0) x!1) (and (= x!2 1.0) (not x!1))))"""),

    # One round of predicate refinement is necessary to generate the predicate
    # (x <= 0).
    ("refine-once",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
(assert (forall ((x Int)) (=> (>= x 1) (not (p x)))))""",
     """
(define-fun p ((x!1 Int)) Bool (<= x!1 0))"""),

    # Two rounds of predicate refinement are necessary to generate the predicate
    # (x <= 0) and then the predicate (x >= 2).
    ("refine-twice",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (<= x 0) (p x))))
(assert (forall ((x Int)) (=> (>= x 2) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (not (p x)))))""",
     """
(define-fun p ((x!1 Int)) Bool (or (<= x!1 0) (>= x!1 2)))"""),

    # The leaves of the tree are irrelevant for the purposes of predicate
    # refinement.
    ("refine-not-leaves",
     """
(declare-fun p (Int) Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert q)
(assert r)
(assert (forall ((x Int)) (=> (and (<= x 0) q r) (p x))))
(assert (forall ((x Int)) (=> (>= x 1) (not (p x)))))""",
     """
(define-fun q () Bool true)
(define-fun r () Bool true)
(define-fun p ((x!1 Int)) Bool (<= x!1 0))"""),

    # One side of the tree is irrelevant for the purposes of predicate
    # refinement.
    ("refine-one-side",
     """
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun r () Bool)
(assert (forall ((x Int)) (=> (<= x 0) (q x))))
(assert r)
(assert (forall ((x Int)) (=> (and (>= x 1) (q x) r) (p x))))
(assert (forall ((x Int)) (not (p x))))""",
     """
(define-fun r () Bool true)
(define-fun q ((x!1 Int)) Bool (<= x!1 0))
(define-fun p ((x!1 Int)) Bool false)"""),

    # Predicate refinement of rules with a literal head argument.
    ("refine-literal-head",
     """
(declare-fun p (Int) Bool)
(assert (p 0))
(assert (not (p 1)))""",
     """
(define-fun p ((x!1 Int)) Bool (= x!1 0))"""),

    # >>> why is this significant?
    ("refine-arity-0",
     """
(declare-fun p () Bool)
(declare-fun q (Int) Bool)
(assert p)
(assert (forall ((x Int)) (=> (> x 0) (q x))))
(assert (forall ((x Int)) (=> (and (<= x 0) p) (not (q x)))))""",
     """
(define-fun p () Bool true)
(define-fun q ((x!1 Int)) Bool (> x!1 0))"""),

    # Predicate refinement generates a predicate that is a non-trivial linear
    # combination of the inequalities in the input.
    ("refine-farkas",
     """
(declare-fun p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (<= (+ (* 3 y) (* -2 x)) 0) (<= (+ (* 2 y) (* 3 x)) 0)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (>= (+ (* 7 y) (* 6 x)) 20) (p x y)) false)))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (<= (+ (* 78 x!1) (* 91 x!2)) 0))"""),

    # Predicate refinement with explicit arguments.
    ("refine-exp-eval",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (>= y 0)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 1) (<= y 0)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (< y 0)) (not (p x y)))))
(assert (forall ((x Int) (y Int)) (=> (and (= x 1) (> y 0)) (not (p x y)))))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (or (and (= x!1 0) (>= x!2 0)) (and (= x!1 1) (<= x!2 0))))"""),

    # Predicate refinement with explicit arguments and literals in the head arguments.
    ("refine-exp-eval-literal-head",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (>= y 0) (p 0 y))))
(assert (forall ((x Int) (y Int)) (=> (<= y 0) (p 1 y))))
(assert (forall ((x Int) (y Int)) (=> (< y 0) (not (p 0 y)))))
(assert (forall ((x Int) (y Int)) (=> (> y 0) (not (p 1 y)))))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))""",
     """
(define-fun p ((x!1 Int) (x!2 Int)) Bool (or (and (= x!1 0) (>= x!2 0)) (and (= x!1 1) (<= x!2 0))))"""),

    make_pred_refine_test("ge", 1, "(>= x 0)", "(>= x!1 0)"),
    make_pred_refine_test("le", 1, "(<= x 0)", "(<= x!1 0)"),
    make_pred_refine_test("gt", 1, "(> x 0)", "(> x!1 0)"),
    make_pred_refine_test("lt", 1, "(< x 0)", "(< x!1 0)"),
    make_pred_refine_test("eq", 1, "(= x 0)", "(= x!1 0)"),
    make_pred_refine_test("eq3", 3, "(= x y z)", "(and (= x!2 x!1) (= x!3 x!2))"),

    make_pred_refine_test("not-ge", 1, "(not (>= x 0))", "(< x!1 0)"),
    make_pred_refine_test("not-le", 1, "(not (<= x 0))", "(> x!1 0)"),
    make_pred_refine_test("not-gt", 1, "(not (> x 0))", "(<= x!1 0)"),
    make_pred_refine_test("not-lt", 1, "(not (< x 0))", "(>= x!1 0)"),
    make_pred_refine_test("not-eq", 1, "(not (= x 0))", "(or (< x!1 0) (> x!1 0))"),
    make_pred_refine_test("not-eq3", 3, "(not (= x y z))", "(or (< x!1 x!2) (< x!2 x!1) (< x!2 x!3) (< x!3 x!2))"),

    make_pred_refine_test("not-not", 1, "(not (not (<= x 0)))", "(<= x!1 0)"),

    make_pred_refine_test("add1", 1, "(<= (+ x) 0)", "(<= x!1 0)"),
    make_pred_refine_test("add2", 2, "(<= (+ x y) 0)", "(<= (+ x!1 x!2) 0)"),
    make_pred_refine_test("add3", 3, "(<= (+ x y z) 0)", "(<= (+ x!1 x!2 x!3) 0)"),
    make_pred_refine_test("sub", 2, "(<= (- x y) 0)", "(<= x!1 x!2)"),
    make_pred_refine_test("neg", 1, "(<= (- x) 0)", "(>= x!1 0)"),

    make_pred_refine_test("and", 2, "(and (<= x 0) (<= y 1))", "(and (<= x!1 0) (<= x!2 1))"),
    make_pred_refine_test("or", 2, "(or (<= x 0) (<= y 1))", "(or (<= x!1 0) (<= x!2 1))"),

    # Multiple predicates with the same name but different arity and/or argument
    # types should be allowed.
    ("misc-preds-same-name",
     """
(declare-fun p () Bool)
(declare-fun p (Int) Bool)
(declare-fun p (Real) Bool)
(declare-fun p (Int Int) Bool)
(declare-fun __expargs__p () Bool)
(declare-fun __expargs__p (Int) Bool)
(declare-fun __expargs__p (Real) Bool)
(declare-fun __expargs__p (Int Int) Bool)
(declare-fun __pred__p () Bool)
(declare-fun __pred__p (Int) Bool)
(declare-fun __pred__p (Real) Bool)
(declare-fun __pred__p (Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (as p (Bool)))
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Real)) (=> (= x 1.0) (p x))))
(assert (forall ((x Int) (y Int)) (=> (= x 2) (= y 3) (p x y))))
(assert (as __expargs__p (Bool)))
(assert (forall ((x Int)) (__expargs__p x)))
(assert (forall ((x Real)) (__expargs__p x)))
(assert (forall ((x Int) (y Int)) (=> (__exparg__ x) (__expargs__p x y))))
(assert (as __pred__p (Bool)))
(assert (forall ((x Int)) (=> (= x 0) (__pred__p x))))
(assert (forall ((x Real)) (=> (= x 1.0) (__pred__p x))))
(assert (forall ((x Int) (y Int)) (=> (and (= y 3)) (__pred__p x y))))""",
     """
(define-fun p () Bool true)
(define-fun p ((x!1 Int)) Bool (= x!1 0))
(define-fun p ((x!1 Real)) Bool (= x!1 1.0))
(define-fun p ((x!1 Int) (x!2 Int)) Bool (and (= x!1 2) (= x!2 3)))"""),
]

unsat_tests = [
    ("empty", # >>> check that this goes to predabst
     """
(assert false)"""),

    # The predicate symbol (of arity 0) is constrained to be both true and
    # false.
    ("trivial-0",
     """
(declare-fun p () Bool)
(assert p)
(assert (not p))"""),

    # The predicate symbol (of arity 1) is constrained to be both true and false
    # over all values in its domain.
    ("trivial-1",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (not (p x))))"""),

    # The predicate symbol (of arity 2) is constrained to be both true and false
    # over all values in its domain.
    ("trivial-2",
     """
(declare-fun p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int) (y Int)) (not (p x y))))"""),

    # >>>
    ("infer-discrete",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (p 0))
(assert (=> (p 0) (p 2)))
(assert (=> (p 2) (p 4)))
(assert (not (p 4)))
(assert (forall ((x Int)) (=> (and (= x 0) (= x 1) (= x 2) (= x 3) (= x 4)) (__pred__p x))))"""),

    # >>>
    ("non-head-vars",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (= x 0) (= y x) (= z y)) (p z))))
(assert (not (p 0)))"""),

    # Predicate refinement separates the sets (x = 0) and (x = 1), but the
    # problem is still unsatisfiable.
    ("refine",
     """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (and (p 0) (= x 1)) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (not (p x)))))"""),
]

unknown_tests = [
    # The node is reachable (with (x,y,z) := (3,4,5)), but the solver is unable
    # to determine this.
    ("pythagoras-reach",
     """
(declare-fun p (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> x 0) (> y 0) (> z 1) (= (+ (* x x) (* y y)) (* z z))) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (not (p x y z))))""",
     "(underlying-solver (incomplete (theory arithmetic)))"),

    # As above, but x, y and z are explicit arguments.
    ("pythagoras-reach-exp-args",
     """
(declare-fun p (Int Int Int) Bool)
(declare-fun __expargs__p (Int Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> x 0) (> y 0) (> z 1) (= (+ (* x x) (* y y)) (* z z))) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (not (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (__exparg__ x) (__exparg__ y) (__exparg__ z)) (__expargs__p x y z))))""",
     "(underlying-solver (incomplete (theory arithmetic)))"),

    # The node is not reachable, but the solver is unable to determine this.
    ("pythagoras-unreach",
     """
(declare-fun p (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> x 0) (> y 0) (> z 1) (= (+ (* x x x) (* y y y)) (* z z z))) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (not (p x y z))))""",
     "(underlying-solver (incomplete (theory arithmetic)))"),

    # As above, but x, y and z are explicit arguments.
    ("pythagoras-unreach-exp-args",
     """
(declare-fun p (Int Int Int) Bool)
(declare-fun __expargs__p (Int Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> x 0) (> y 0) (> z 1) (= (+ (* x x x) (* y y y)) (* z z z))) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (not (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (__exparg__ x) (__exparg__ y) (__exparg__ z)) (__expargs__p x y z))))""",
     "(underlying-solver (incomplete (theory arithmetic)))"),

    # The head predicate is not implied by the body, but the solver is unable to
    # prove this.
    ("pythagoras-head-false",
     """
(declare-fun p (Int Int Int) Bool)
(declare-fun __pred__p (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> x 0) (> y 0) (> z 0) (= (+ (* x x) (* y y)) (* z z))) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (= z 1) (__pred__p x y z))))""",
     "(underlying-solver (incomplete (theory arithmetic)))"),

    # The head predicate is implied by the body, but the solver is unable to
    # prove this.
    ("pythagoras-head-true",
     """
(declare-fun p (Int Int Int) Bool)
(declare-fun __pred__p (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (> x 0) (> y 0) (> z 0) (= (+ (* x x x) (* y y y)) (* z z z))) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (= z 1) (__pred__p x y z))))""",
    "(underlying-solver (incomplete (theory arithmetic)))"),

    # The node is obviously reachable (with (x,y,z) := (0,0,0) or
    # (1,1,1), say), but the solver is unable to determine whether the
    # values of explicit arguments are unique.
    ("pythagoras-exp-values",
     """
(declare-fun p (Int Int Int) Bool)
(declare-fun __expargs__p (Int Int Int) Bool)
(declare-fun __exparg__ (Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (>= x 0) (>= y 0) (>= z 0) (= (+ (* x x x) (* y y y)) (* z z z))) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (__exparg__ x) (__exparg__ y) (__exparg__ z)) (__expargs__p x y z))))""",
     "values of explicit arguments for p were not uniquely determined"),

    # The node is reachable without abstraction (with (x,y,z) := (3,4,5)), but
    # the solver is unable to determine this.
    ("pythagoras-refine-reach",
     """
(declare-fun sq (Int Int) Bool)
(declare-fun p (Int Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= (* x x) y) (sq x y))))
(assert (forall ((x Int) (y Int) (z Int) (a Int) (b Int) (c Int)) (=> (and (> x 0) (> y 0) (> z 1) (= (+ a b) c) (sq x a) (sq y b) (sq z c)) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (not (p x y z))))""",
     "(underlying-solver (incomplete (theory arithmetic)))"),

    # The node is not reachable without abstraction, but the solver is unable to
    # determine this.
    ("pythagoras-refine-unreach",
     """
(declare-fun cube (Int Int) Bool)
(declare-fun p (Int Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= (* x x x) y) (cube x y))))
(assert (forall ((x Int) (y Int) (z Int) (a Int) (b Int) (c Int)) (=> (and (> x 0) (> y 0) (> z 1) (= (+ a b) c) (cube x a) (cube y b) (cube z c)) (p x y z))))
(assert (forall ((x Int) (y Int) (z Int)) (not (p x y z))))""",
     "(underlying-solver (incomplete (theory arithmetic)))"),

    # Predicate refinement fails because Farkas is incomplete on integers.
    ("refine-farkas-incomplete",
     """
(declare-fun p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (> x 0) (> y 0)) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (< (+ x y) 1) (not (p x y)))))""",
     "incomplete"),

    # Predicate refinement (>>> or determination of reachability without abstraction?) fails due to a non-linear expression.
    make_pred_refine_test("mul", 2, "(<= (* x y) 2)", None),
    make_pred_refine_test("div", 2, "(<= (div x y) 2)", None),
    make_pred_refine_test("mod", 1, "(<= (mod x 2) 0)", None),
    make_pred_refine_test("distinct", 1, "(distinct x 0)", None),
    make_pred_refine_test("xor", 2, "(xor (<= x 0) (<= y 1))", None),
    make_pred_refine_test("implies", 2, "(=> (<= x 0) (<= y 1))", None),
    make_pred_refine_test("iff", 2, "(= (<= x 0) (<= y 1))", None),
    make_pred_refine_test("ite", 2, "(ite (<= x 0) (<= y 1) (<= y 2))", None),

    # Predicate refinement fails due to a non-integer expression.
    make_pred_refine_test("real", 1, "(>= x 0)", None, argType="Real"),
    make_pred_refine_test("bool", 1, "x", None, argType="Bool"),
]

basic_tests = (sat_tests, unsat_tests, unknown_tests)
