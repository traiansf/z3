from z3 import *
import itertools
import functools
import random
import numpy.random

random.seed(67234867238)

fname_counter = 0
def new_fname():
    global fname_counter
    name = "f%d" % fname_counter
    fname_counter += 1
    return name

def new_f(arity):
    arg_ret_sorts = [IntSort() for _ in range(arity)] + [BoolSort()]
    return Function(new_fname(), *arg_ret_sorts)

aname_counter = 0
def new_aname():
    global aname_counter
    name = "a%d" % aname_counter
    aname_counter += 1
    return name

def new_a():
    return Int(new_aname())

def random_cluster(xs, n):
    xss = [[] for _ in range(n)]
    for x in xs:
        random.choice(xss).append(x)
    return xss

def random_tree(n):
    assert n > 0
    roots = [[] for _ in range(n)]
    while len(roots) > 1:
        random.shuffle(roots)
        degree = min(1 + numpy.random.poisson(2), len(roots))
        roots = [roots[degree:]] + roots[:degree]
    return roots[0]

def sum_pos(xs):
    if random.random() < 0.5:
        return Sum(xs + [random.randint(0, 9)])
    else:
        return Sum(xs)

def sum_neg(xs):
    if random.random() < 0.5:
        return Sum(xs + [random.randint(-9, 0)])
    else:
        return Sum(xs)

def exparg_fn():
    return Function("__exparg__", IntSort(), BoolSort())
def expargs_fn(pred):
    return Function("__expargs__" + pred.name(), *pred.types())
def name_fn(n):
    return Function("__name__" + n, IntSort(), BoolSort())
def names_fn(pred):
    return Function("__names__" + pred.name(), *pred.types())

# The rules generate a node graph that is a tree, where each node is associated
# with a distinct predicate symbol.
#
# Each rule is of the form:
#
#   P1(e,...,e) and ... and Pn(e,...,e) and
#    (e <= e) and ... and (e <= e)
#    => P(e,...,e)
#
# where:
# -  each e is a sum of (0 or more) variables and (optionally) a constant
# -  each variable that appears in the head predicate application appears
#    somewhere on the LHS of a <= constraint
# -  each variable that appears in a body predicate application appears
#    somewhere on the RHS of a <= constraint
#
# There is an additional rule (P0(x1,...,xn) and (x1 + ... + xn < 0) => false),
# where P0 is the root node.
def make_random_sat_test(name, num_nodes, harity,
                         unique_preds_probability=1.0,
                         use_explicit_args=False,
                         use_arg_names=False):
    s = SimpleSolver()

    preds = {}
    def pred(arity):
        if random.random() < unique_preds_probability:
            pred = new_f(arity)
            if use_arg_names:
                names = map(str, range(arity))
                random.shuffle(names)
                vars = [new_a() for _ in range(arity)]
                s.add(Forall(vars), Implies(And(name_fn(names[i])(vars[i]) for i in range(arity)), names_fn(pred)(*vars)))
            return pred
        else:
            if arity not in preds:
                pred = new_f(arity + 1)
                if use_explicit_args:
                    vars = [new_a() for _ in range(arity + 1)]
                    s.add(Forall(vars), Implies(exparg_fn()(vars[0]), expargs_fn(pred)(*vars)))
                if use_arg_names:
                    names = map(str, range(arity))
                    random.shuffle(names)
                    vars = [new_a() for _ in range(arity)]
                    s.add(Forall(vars), Implies(And(name_fn(names[i])(vars[i + 1]) for i in range(arity)), names_fn(pred)(*vars)))
                preds[arity] = (pred, 0)
            (pred, n) = preds[arity]
            preds[arity] = (pred, n + 1)
            return functools.parital(pred, n)

    def node(hnode, harity):
        # Generate a random number of head variables (with mean 1.25 * N), and
        # group these into N disjoint sums to form the head arguments (where N
        # is the arity of the head predicate).
        hvars = [new_a() for _ in range(numpy.random.poisson(1.25 * harity))]
        hargs = map(sum_pos, random_cluster(hvars, harity))

        # Generate a fresh head predicate, and form the head application.
        hpred = pred(harity)
        happ = hpred(*hargs)

        # Generate a random number of body variables (with mean 1.25 * M), and
        # group these into M disjoint sums to form the body arguments (where M
        # is the sum of the (randomly-chosen) arities of the body predicates).
        baritys = [numpy.random.poisson(3) for _ in range(len(tnode))]
        bvars = [new_a() for _ in range(numpy.random.poisson(1.25 * sum(baritys)))]
        bargs = map(sum_neg, random_cluster(hvars, sum(baritys)))

        # Recursively generate k body predicates, and form the body
        # applications.
        bapps = []
        for bnode, barity in zip(hnode, barities):
            bpred = node(bnode, barity)
            bapps.append(bpred(*bargs[:barity]))
            bargs = bargs[barity:]

        # Generate a random number of constraints, each relating a sum of head
        # variables to a sum of body variables.
        nconstraints = 1 + random.randint(0, min(len(hargs), len(bargs)))
        lvarss = random_cluster(hvars, nconstraints)
        rvarss = random_cluster(bvars, nconstraints)
        constraints = []
        for lvars, rvars in zip(lvarss, rvarss):
            if not lvars and not rvars:
                continue
            lhs = sum_neg(lvars)
            rhs = sum_pos(rvars)
            r = random.random()
            if r < 0.45:
                constraints.append(lhs >= rhs)
            elif r < 0.90:
                constraints.append(lhs > rhs)
            else:
                constraints.append(lhs == rhs)

        s.add(ForAll(bvars + hvars, Implies(And(*(bapps + constraints)), happ)))
        return hpred

    root = random_tree(num_nodes)
    vars = [new_a() for _ in range(num_vars)]
    head = BoolVal(False)
    body = And(node(root, len(vars))(vars), Sum(vars) < 0)
    s.add(ForAll(vars, Implies(body, head)))
    code = s.dump()
    return (name, code, None)

sat_tests = [
    make_random_sat_test("unique-%d" % i, 30, 3) for i in range(10)
] + [
    make_random_sat_test("mixed-%d" % i, 30, 3,
                         unique_preds_probability=0.5) for i in range(10)
] + [
    make_random_sat_test("expargs-%d" % i, 30, 3,
                         unique_preds_probability=0.0,
                         use_explicit_args=True) for i in range(10)
] + [
    make_random_sat_test("names-%d" % i, 30, 3,
                         use_arg_names=True) for i in range(10)
]

random_tests = (sat_tests, [], [])
