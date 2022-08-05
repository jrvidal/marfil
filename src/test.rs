use crate::{
    ast,
    eval::{self, Machine, Value},
    grammar, typeck,
};

#[test]
fn factorial() {
    assert_eq!(
        result(
            r"
      letrec factorial: int -> int = fn (n: int) => {
        if n == 0 { 1 } else {
          n * factorial(n - 1)
        }
      };

      factorial(10)
  "
        ),
        Value::Int(3628800)
    );
}

#[test]
fn array() {
    use Value::*;

    assert_eq!(
        result(
            r"
      let x = [2; 3];

      [...x]
    "
        ),
        Array(vec![Int(2), Int(2), Int(2)].into())
    );
}

#[test]
fn array_update() {
    use Value::*;

    assert_eq!(
        result(
            r"
              let x = [2; 3];

              let y = [...x; 1 = 7];

              [y[1] | 42, y[9] | 42]
            "
        ),
        Array(vec![Int(7), Int(42)].into())
    );
}

fn result(source: &str) -> Value {
    let mut interner = ast::Interner::default();

    let program = grammar::ProgramParser::new()
        .parse(&mut interner, source)
        .map_err(|error| format!("{:?}", error))
        .unwrap();

    typeck::type_check_program(&program, &interner).unwrap();

    let code = eval::compile(program).unwrap();

    let machine = Machine::new(code, interner);

    machine.run().unwrap()
}
