#include "farkas_util.h"
#include "smt2parser.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"

static expr_ref parse_fml(ast_manager& m, char const* str) {
    expr_ref result(m);
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ostringstream buffer;
    buffer << "(declare-const x Int)\n"
        << "(declare-const y Int)\n"
        << "(declare-const z Int)\n"
        << "(declare-const xp Int)\n"
        << "(declare-const yp Int)\n"
        << "(declare-const p1 Int)\n"
        << "(declare-const p2 Int)\n"
        << "(declare-const c Int)\n"
        << "(assert " << str << ")\n";
    std::istringstream is(buffer.str());
    VERIFY(parse_smt2_commands(ctx, is));
    SASSERT(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
    return result;
}

static char const* example1 = "(and (= (+ (* c x) (* 6 y)) 2) (= y 3) (or (= z (+ x 1)) (= z (- (* b x) 1)) (= z (+ x y))))";
static char const* example2 = "(and (< x y) (= xp (+ x 1)) (= yp y))";
static char const* example3 = "(< (+ (* p1 xp) (* p2 yp)) (+ (* p1 x) (* p2 y)))";
// XXX jchl No reference to example1 or example3?

void tst_farkas_app() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);

    expr_ref x(m.mk_const(symbol("x"), a.mk_int()), m);
    expr_ref y(m.mk_const(symbol("y"), a.mk_int()), m);
    expr_ref xp(m.mk_const(symbol("xp"), a.mk_int()), m);
    expr_ref yp(m.mk_const(symbol("yp"), a.mk_int()), m);
    expr_ref_vector vars1(m);
    expr_ref_vector vars2(m);
    vars1.push_back(x);
    vars1.push_back(y);
    vars2.push_back(xp);
    vars2.push_back(yp);

    expr_ref_vector values(m);
    expr_ref fml1(m);
    fml1 = parse_fml(m, example2);

    if (false /* well_founded(vars1, vars2, fml1, values) */) {
        std::cout << "===================================== \n";
        std::cout << "Formula is well-founded! \n";
        std::cout << "===================================== \n";

        expr_ref_vector bound_values(values);
        expr_ref delta0(values[0].get(), m);
        bound_values.reverse();
        bound_values.pop_back();
        bound_values.reverse();
        // XXX jchl farkas_pred is no longer exported by farkas_util.h
        //farkas_pred bound(vars1, bound_values, 2, delta0);
        //bound.display();
    }
    else {
        std::cout << "===================================== \n";
        std::cout << "Formula is not well-founded! \n";
        std::cout << "===================================== \n";
    }
}
