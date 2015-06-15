from z3 import *
import itertools
import random
import re

try:
    import numpy.random
    random_poisson = numpy.random.poisson
except ImportError:
    def random_poisson(lambd):
        return int(random.random() * lambd * 2)

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

def sum_with(xs, c):
    if xs:
        return Sum(xs + [c])
    else:
        return c

def random_cluster(xs, n, minsize=0):
    xs = xs[:] # make a copy
    random.shuffle(xs)
    xss = [[] for _ in range(n)]
    for i in range(n):
        for j in range(minsize):
            xss[i].append(xs.pop(0))
    for x in xs:
        random.choice(xss).append(x)
    return xss

def random_tree(nleaves):
    assert nleaves > 0
    tree = {i:[] for i in range(nleaves)}
    roots = tree.keys()
    while len(roots) > 1:
        random.shuffle(roots)
        degree = min(1 + random_poisson(2), len(roots))
        n = len(tree)
        tree[n] = roots[:degree]
        roots = [n] + roots[degree:]
    return tree

def random_dag(nnodes):
    assert nnodes > 0
    dag = {}
    for i in range(nnodes):
        degree = min(random_poisson(2), len(dag))
        dag[i] = random.sample(dag.keys(), degree)
    return dag

def pred_fn(pred):
    return Function("__pred__" + pred.name(), *([pred.domain(i) for i in range(pred.arity())] + [pred.range()]))
def template_fn(pred, ntemplates):
    return Function("__temp__" + pred.name(), *([pred.domain(i) for i in range(pred.arity())] + [IntSort() for _ in range(ntemplates)] + [pred.range()]))
def template_extra_fn(ntemplates):
    return Function("__temp__extra__", *([IntSort() for _ in range(ntemplates)] + [BoolSort()]))
def exparg_fn():
    return Function("__exparg__", IntSort(), BoolSort())
def expargs_fn(pred):
    return Function("__expargs__" + pred.name(), *([pred.domain(i) for i in range(pred.arity())] + [pred.range()]))
def name_fn(n):
    return Function("__name__" + n, IntSort(), BoolSort())
def names_fn(pred):
    return Function("__names__" + pred.name(), *([pred.domain(i) for i in range(pred.arity())] + [pred.range()]))

def Partial(f, argmap):
    def wrapper(*args):
        args = list(args)
        all_args = []
        for i in range(len(argmap) + len(args)):
            if i in argmap:
                all_args.append(argmap[i])
            else:
                all_args.append(args.pop(0))
        return f(*all_args)
    return wrapper

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
def make_random_sat_test(name, dag,
                         shared_preds_probability=0.0,
                         initial_preds_probability=0.0,
                         templates_probability=0.0,
                         extra_template_constraint_probability=0.0,
                         explicit_args_probability=0.0,
                         arg_names_probability=0.0,
                         extra_constants_probability=0.9,
                         equalities_probability=0.1):
    s = SimpleSolver()

    preds = {}
    def declare_pred(arity):
        if random.random() < shared_preds_probability:
            if arity not in preds:
                nexpargs = random.randint(1, 3)
                positions = range(arity + nexpargs)
                random.shuffle(positions)
                regular_positions = positions[:arity]
                exparg_positions = positions[arity:]
                pred = new_f(arity + nexpargs)
                if random.random() < explicit_args_probability:
                    vars = [new_a() for _ in range(arity + nexpargs)]
                    body = And(*(exparg_fn()(vars[i]) for i in exparg_positions))
                    head = expargs_fn(pred)(*vars)
                    s.add(ForAll(vars, Implies(body, head)))
                if (random.random() < arg_names_probability) and arity:
                    names = map(str, range(arity))
                    random.shuffle(names)
                    vars = [new_a() for _ in range(arity + nexpargs)]
                    body = And(*(name_fn(name)(vars[i]) for i, name in zip(regular_positions, names)))
                    head = names_fn(pred)(*vars)
                    s.add(ForAll(vars, Implies(body, head)))
                preds[arity] = (pred, exparg_positions, 0)
            (pred, exparg_positions, n) = preds[arity]
            preds[arity] = (pred, exparg_positions, n + 1)
            return Partial(pred, dict(zip(exparg_positions, [n] + [random.randint(0, 2) for _ in range(len(exparg_positions) - 1)])))
        else:
            pred = new_f(arity)
            if (random.random() < arg_names_probability) and arity:
                names = map(str, range(arity))
                random.shuffle(names)
                vars = [new_a() for _ in range(arity)]
                body = And(*(name_fn(names[i])(vars[i]) for i in range(arity)))
                head = names_fn(pred)(*vars)
                s.add(ForAll(vars, Implies(body, head)))
            return pred

    def random_int():
        if random.random() < extra_constants_probability:
            return random.randint(-9, 9)
        else:
            return 0

    def declare_rule(hnode_id):
        # Generate a random number of head variables (with mean 1.25 * N),
        # and group these into N disjoint sums to form the head arguments
        # (where N is the arity of the head predicate).
        harity = arity[hnode_id]
        nhvars = (harity + random_poisson(0.5 * harity)) if harity else 0
        hvars = [new_a() for _ in range(nhvars)]
        hconsts = [random_int() for _ in range(harity)]
        hargs = map(sum_with, random_cluster(hvars, harity, minsize=1), hconsts)

        # Generate a fresh head predicate, and form the head application.
        happ = pred[hnode_id](*hargs)

        # Generate a random number of body variables (with mean 1.25 * M), and
        # group these into M disjoint sums to form the body arguments (where M
        # is the sum of the (randomly-chosen) arities of the body predicates).
        barity = sum(arity[bnode_id] for bnode_id in dag[hnode_id])
        nbvars = (barity + random_poisson(0.5 * barity)) if barity else 0
        bvars = [new_a() for _ in range(nbvars)]
        bconsts = [random_int() for _ in range(barity)]
        bargs = map(sum_with, random_cluster(bvars, barity, minsize=1), bconsts)

        # Recursively generate k body predicates, and form the body
        # applications.
        bapps = []
        for bnode_id in dag[hnode_id]:
            bapps.append(pred[bnode_id](*bargs[:arity[bnode_id]]))
            bargs = bargs[arity[bnode_id]:]

        # Generate a random number of constraints, each relating a sum of (one
        # or more) head variables to a sum of (zero or more) body variables.
        # Note that we could allow constraints with zero hvars, but if we want
        # to avoid cutting part of the tree off from the head constraint then
        # we'd need to ensure that for each body predicate, at least one
        # variable used by that predicate appears in some constraint with at
        # least one head predicate.
        nconstraints = random.randint(1, len(hargs))
        lvarss = random_cluster(bvars, nconstraints)
        rvarss = random_cluster(hvars, nconstraints, minsize=1)
        lconsts = [random_int() for _ in range(nconstraints)]
        rconsts = [random_int() for _ in range(nconstraints)]
        constraints = []
        for lvars, rvars, lconst, rconst in zip(lvarss, rvarss, lconsts, rconsts):
            assert rvars
            lhs = sum_with(lvars, lconst)
            rhs = sum_with(rvars, rconst)
            if lvars and (random.random() < equalities_probability):
                constraints.append(lhs == rhs)
            else:
                constraints.append(lhs <= rhs)

        if bvars + hvars:
            s.add(ForAll(bvars + hvars, Implies(And(bapps + constraints), happ)))
        else:
            s.add(Implies(And(bapps + constraints), happ))

        return sum(bounds[bnode_id] for bnode_id in dag[hnode_id]) - sum(bconsts) + sum(lconsts) - sum(rconsts) + sum(hconsts)

    arity = {}
    pred = {}
    bounds = {}
    for i in sorted(dag):
        # Note that we ensure the arity is non-zero to prevent cutting part of
        # the tree off from the head constraint.
        arity[i] = 1 + random_poisson(2)
        pred[i] = declare_pred(arity[i])
        bounds[i] = declare_rule(i)

    root_ids = [i for i in dag if not any(i in dag[j] for j in dag)]
    for root_id in root_ids:
        vars = [new_a() for _ in range(arity[root_id])]
        head = BoolVal(False)
        body = And(pred[root_id](*vars), Sum(vars) < bounds[root_id])
        s.add(ForAll(vars, Implies(body, head)))

    def declare_initial_preds(pred, arity, bounds):
        vars = [new_a() for _ in range(arity)]
        body = And(*(Sum(vars) >= bounds - random.randint(-1, 30) for _ in range(10)))
        head = pred_fn(pred)(*vars)
        s.add(ForAll(vars, Implies(body, head)))

    for i in sorted(dag):
        if random.random() < initial_preds_probability:
            assert shared_preds_probability == 0.0
            declare_initial_preds(pred[i], arity[i], bounds[i])

    def declare_template(pred, arity, ntemplates, param_id):
        vars = [new_a() for _ in range(arity + ntemplates)]
        body = Sum(vars[:arity]) >= vars[arity + param_id]
        head = template_fn(pred, ntemplates)(*vars)
        s.add(ForAll(vars, Implies(body, head)))

    templates = []
    for i in sorted(dag):
        if random.random() < templates_probability:
            assert shared_preds_probability == 0.0
            assert initial_preds_probability == 0.0
            templates.append(i)

    for param_id, node_id in enumerate(templates):
        declare_template(pred[node_id], arity[node_id], len(templates), param_id)

    def declare_extra_template_constraint(ntemplates):
        vars = [new_a() for _ in range(ntemplates)]
        bound = sum(bounds[i] for i in templates)
        if random.random() < extra_template_constraint_probability:
            if random.random() < 0.5:
                body = Sum(vars) >= bound - random.randint(0, 2)
            else:
                body = Sum(vars) <= bound + random.randint(0, 2)
        else:
            body = BoolVal(True)
        head = template_extra_fn(ntemplates)(*vars)
        s.add(ForAll(vars, Implies(body, head)))

    if templates:
        declare_extra_template_constraint(len(templates))

    #print name
    #for i in sorted(dag):
    #    print i, pred[i], arity[i], dag[i], bounds[i]

    code = s.to_smt2()
    assert '(check-sat)' in code
    code = code[:code.index('(check-sat)')]

    if (shared_preds_probability == 0.0) and (initial_preds_probability == 0.0) and (arg_names_probability == 0.0) and (templates_probability == 0.0): # >>> :(
        def sum_expr(xs):
            assert len(xs) > 0
            if len(xs) == 1:
                return xs[0]
            else:
                return "(+ " + " ".join(xs) + ")"
        def make_model(i):
            xs = ["x!%d" % (j + 1) for j in range(arity[i])]
            if (i in templates) or (bounds[i] > 1):
                s = "(>= %s %d)" % (sum_expr(xs), bounds[i])
            elif bounds[i] == 1:
                s = "(> %s 0)" % sum_expr(xs)
            elif bounds[i] == 0:
                s = "(>= %s 0)" % sum_expr(xs)
            else:
                assert bounds[i] < 0
                s = "(>= %s 0)" % sum_expr(xs + [str(-bounds[i])])
            return "(define-fun %s (%s) Bool %s)" % (pred[i], " ".join("(x!%d Int)" % (j + 1) for j in range(arity[i])), s)
        model = "\n" + "\n".join(make_model(i) for i in sorted(dag))
    else:
        model = None

    return (name, code, model)

sat_tests = [
    make_random_sat_test("simple", random_dag(3))
] + [
    make_random_sat_test("basic-%d" % i, random_dag(50)) for i in range(10)
] + [
    make_random_sat_test("shared-%d" % i, random_dag(50),
                         shared_preds_probability=1.0) for i in range(10)
] + [
    make_random_sat_test("preds-%d" % i, random_dag(50),
                         initial_preds_probability=1.0) for i in range(10)
] + [
    make_random_sat_test("templates-%d" % i, random_dag(50),
                         templates_probability=0.3,
                         extra_template_constraint_probability=0.3) for i in range(10)
] + [
    make_random_sat_test("expargs-%d" % i, random_dag(50),
                         shared_preds_probability=1.0,
                         explicit_args_probability=1.0) for i in range(10)
] + [
    make_random_sat_test("names-%d" % i, random_dag(50),
                         arg_names_probability=1.0) for i in range(10)
]

random_tests = (sat_tests, [], [])
