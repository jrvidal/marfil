#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(grammar);
mod ast;
mod eval;
mod typeck;

fn main() {
    env_logger::init();
    let cmd = std::env::args().skip(1).next().unwrap();
    let path = std::env::args().skip(2).next().unwrap();
    let source = std::fs::read_to_string(&path).expect(&format!("Error opening {}", path));

    let ast_result = grammar::ProgramParser::new().parse(&source);

    if cmd == "parse" {
        eprintln!("{:?}", ast_result);
        return;
    }

    let ast = ast_result.unwrap();

    if cmd == "free" {
        eprintln!("{:?}", ast.1.map(|expr| expr.free_vars()));
        return;
    }

    let typecheck_result = typeck::type_check(&ast);
    if cmd == "typeck" {
        eprintln!("{:?}", typecheck_result);
        return;
    }

    typecheck_result.unwrap();

    let compilation_result = eval::compile(ast);

    if cmd == "compile" {
        eprintln!("{:?}", compilation_result);
        return;
    }

    let compilation = compilation_result.unwrap();

    let machine = eval::Machine::new(compilation);

    if cmd == "eval" {
        eprintln!("{:?}", machine.run());
    } else {
        panic!("Unknown command {}", cmd);
    }
}

#[test]
fn some_programs() {
    let programs = [
        r#"
        "abc";
    "#,
        r#"
        let x = 1;
    "#,
        r#"
        let foo = fn(x: int) => 3;
    "#,
        r#"
        let z = foo(false);
    "#,
        r#"
        1 + 2;
    "#,
        r#"
        1 * 2;
    "#,
        r#"
        1 + 3 * 2;
    "#,
        r#"
        !"ad";
    "#,
    ];

    for program in &programs {
        let result = grammar::ProgramParser::new().parse(program);
        assert!(result.is_ok(), "source: {}\n result: {:?}", program, result);
    }
}

#[test]
fn specificity() {
    let sum = expr("1 + 2 * 3");
    assert!(std::matches!(sum, ast::Expr::Plus(..)), "{:?}", sum);

    let prod = expr("(1 + 2) * 3");
    assert!(std::matches!(prod, ast::Expr::Prod(..)), "{:?}", prod);

    let sum2 = expr("!1 + 2");
    assert!(std::matches!(sum2, ast::Expr::Plus(..)), "{:?}", sum2);

    let prod2 = expr("!1 * 2");
    assert!(std::matches!(prod2, ast::Expr::Prod(..)), "{:?}", prod2);

    let prod3 = expr("1 * !2");
    assert!(std::matches!(prod3, ast::Expr::Prod(..)), "{:?}", prod3);

    let neg = expr("!(1 + 2)");
    assert!(std::matches!(neg, ast::Expr::Neg(..)), "{:?}", neg);

    let fun = expr("fn (x: int) => 1 + 2");
    assert!(std::matches!(fun, ast::Expr::Func{..}), "{:?}", fun);

    let fun2 = expr("fn (x: int) => 1 * 2");
    assert!(std::matches!(fun2, ast::Expr::Func{..}), "{:?}", fun2);
}

#[cfg(test)]
fn expr(source: &str) -> ast::Expr {
    grammar::ProgramParser::new()
        .parse(source)
        .expect(&format!("Parser error with {}", source))
        .1
        .unwrap()
}
