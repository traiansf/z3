inpval_tests = [
    ("wf-odd-arity",
     """
(declare-fun __wf__p (Int) Bool)
(assert (forall ((x Int)) (__wf__p x)))
""",
     "WF predicate symbol __wf__p has odd arity"),

    ("wf-mismatching-args",
     """
(declare-fun __wf__p (Int Real) Bool)
(assert (forall ((x Int) (y Real)) (__wf__p x y)))
""",
     "WF predicate symbol __wf__p has mismatching argument types"),

    ("wf-non-int-args",
     """
(declare-fun __wf__p (Real Real) Bool)
(assert (forall ((x Real) (y Real)) (__wf__p x y)))
""",
     "WF predicate symbol __wf__p has non-integer argument types"),

    ("plist-no-query",
     """
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (__pred__p x))))
""",
     "found predicate list for non-existent query symbol p"),
# XXX What about a similar case where a predicate with the same name but different arity/types exists?

    ("plist-in-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (__pred__p x) false)))
""",
     "found predicate list __pred__p in non-head position"),

    ("plist-uninterp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (p x) (__pred__p x))))
""",
     "predicate list for p has an uninterpreted tail"),

    ("plist-non-var-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (=> (= x 0) (__pred__p x 0))))
""",
     "predicate list for p has invalid argument list"),

    ("plist-non-unique-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __pred__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (p x y)))
(assert (forall ((x Int)) (=> (= x 0) (__pred__p x x))))
""",
     "predicate list for p has invalid argument list"),

    ("plist-free-vars",
     """
(declare-fun p (Int) Bool)
(declare-fun __pred__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__pred__p x))))
""",
     "predicate for p has free variables"),

     ("extra-multiple-same-type",
     """
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((a Int)) (=> (= a 0) (__temp__extra__ a))))
(assert (forall ((a Int)) (=> (= a 1) (__temp__extra__ a))))
""",
     "found multiple extra template constraints"),

     ("extra-multiple-different-type",
     """
(declare-fun __temp__extra__ (Int) Bool)
(declare-fun __temp__extra__ (Int Int) Bool)
(assert (forall ((a Int)) (=> (= a 0) (__temp__extra__ a))))
(assert (forall ((a Int) (b Int)) (=> (= b 1) (__temp__extra__ a b))))
""",
     "found multiple extra template constraints"),

    ("extra-in-body",
     """
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((a Int)) (=> (__temp__extra__ a) false)))
""",
     "found extra template constraint in non-head position"),

    ("extra-uninterp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((a Int)) (=> (p a) (__temp__extra__ a))))
""",
     "extra template constraint has an uninterpreted tail"),

    ("extra-non-var-args",
     """
(declare-fun __temp__extra__ (Int Int) Bool)
(assert (forall ((a Int)) (=> (= a 0) (__temp__extra__ a 0))))
""",
     "extra template constraint has invalid argument list"),

    ("extra-non-unique-args",
     """
(declare-fun __temp__extra__ (Int Int) Bool)
(assert (forall ((a Int)) (=> (= a 0) (__temp__extra__ a a))))
""",
     "extra template constraint has invalid argument list"),

    ("extra-free-vars",
     """
(declare-fun __temp__extra__ (Int) Bool)
(assert (forall ((a Int) (b Int)) (=> (= a b) (__temp__extra__ a))))
""",
     "extra template constraint has free variables"),

    ("templ-insufficient-args",
     """
(declare-fun __temp__extra__ (Int Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((a Int) (b Int)) (=> (= a b) (__temp__extra__ a b))))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))
""",
     "template for p has insufficient parameters"),

    ("templ-mismatching-args",
     """
(declare-fun __temp__extra__ (Int Real) Bool)
(declare-fun __temp__p (Real Int) Bool)
(assert (forall ((a Int) (b Real)) (=> (= a 0) (__temp__extra__ a b))))
(assert (forall ((a Real) (b Int)) (=> (= b 0) (__temp__p a b))))
""",
     "extra parameter to template for p is of wrong type"),

    ("templ-no-query",
     """
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))
""",
     "found template for non-existent query symbol p"),
# XXX What about a similar case where a predicate with the same name but different arity/types exists?

    ("templ-multiple",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) false)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))
(assert (forall ((x Int)) (=> (= x 1) (__temp__p x))))
""",
     "found multiple templates for p"),
# XXX What about a similar (non-error) case where templates exist for two predicates with the same name but different arities/types?

    ("templ-in-body",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) false)))
(assert (forall ((x Int)) (=> (__temp__p x) false)))
""",
     "found template __temp__p in non-head position"),

    ("templ-uninterp-tail",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) false)))
(assert (forall ((x Int)) (=> (p x) (__temp__p x))))
""",
     "template for p has an uninterpreted tail"),

    ("templ-non-var-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (p x y) false)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x 0))))
""",
     "template for p has invalid argument list"),

    ("templ-non-unique-args",
     """
(declare-fun p (Int Int) Bool)
(declare-fun __temp__p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (p x y) false)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x x))))
""",
     "template for p has invalid argument list"),

    ("templ-free-vars",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) false)))
(assert (forall ((x Int) (y Int)) (=> (= x y) (__temp__p x))))
""",
     "template for p has free variables"),

    ("templ-and-rule",
     """
(declare-fun p (Int) Bool)
(declare-fun __temp__p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (forall ((x Int)) (=> (= x 0) (__temp__p x))))
""",
     "both rule and template for p"),
]

for test in inpval_tests:
    (name, code, errmsg) = test

    in_filename = "inpval-" + name + ".smt2"
    with open(in_filename, "w") as f:
        f.write("(set-logic HORN)\n")
        f.write(code)
        f.write("\n(check-sat)\n")
        f.write("(get-info :reason-unknown)\n")

    out_filename = "inpval-" + name + ".out"
    with open(out_filename, "w") as f:
        f.write("unknown\n")
        f.write("(:reason-unknown " + errmsg + ")\n")
