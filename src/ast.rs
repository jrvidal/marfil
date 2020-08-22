use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub struct Program(pub Vec<Declaration>, pub Option<Expr>);

#[derive(Debug)]
pub enum Expr {
    Bool(bool),
    String(String),
    Var(String),
    Int(i64),
    Func {
        arg: String,
        ty: Type,
        body: Box<Expr>,
    },
    Call(String, Box<Expr>),
    Neg(Box<Expr>),
    Plus(Box<Expr>, Box<Expr>),
    Minus(Box<Expr>, Box<Expr>),
    Prod(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    If {
        test: Box<Expr>,
        then: Box<Expr>,
        alt: Box<Expr>,
    },
    Block(Vec<Declaration>, Box<Expr>),
    Tuple(Vec<Expr>),
    TupleAccess(Box<Expr>, usize),
    Unit,
}

impl Expr {
    pub fn free_vars(&self) -> HashSet<String> {
        enum FreeVarsOp<'a> {
            Expr(&'a Expr),
            Pop,
            Push(&'a String),
        }
        let mut stack = Vec::new();
        stack.push(FreeVarsOp::Expr(self));
        let mut ctx = Vec::new();
        let mut ret = HashSet::new();

        while let Some(op) = stack.pop() {
            let expr = match op {
                FreeVarsOp::Expr(expr) => expr,
                FreeVarsOp::Pop => {
                    ctx.pop();
                    continue;
                }
                FreeVarsOp::Push(var) => {
                    ctx.push(var);
                    continue;
                }
            };
            match expr {
                Expr::Var(s) => {
                    if !ctx.contains(&s) {
                        ret.insert(s.clone());
                    }
                }
                Expr::Func { arg, body, .. } => {
                    ctx.push(arg);
                    stack.push(FreeVarsOp::Pop);
                    stack.push(FreeVarsOp::Expr(body));
                }
                Expr::Block(decls, expr) => {
                    let mut ops = vec![];
                    let mut vars = vec![];
                    ops.push(FreeVarsOp::Expr(&*expr));
                    for decl in decls.iter().rev() {
                        match decl {
                            Declaration::Expr(expr) => ops.push(FreeVarsOp::Expr(expr)),
                            Declaration::Let(var, expr) => {
                                ops.push(FreeVarsOp::Push(var));
                                vars.push(var);
                                ops.push(FreeVarsOp::Expr(expr));
                            }
                            Declaration::LetRec(var, _, expr) => {
                                ops.push(FreeVarsOp::Expr(expr));
                                ops.push(FreeVarsOp::Push(var));
                                vars.push(var);
                            }
                        }
                    }
                    stack.extend(vars.into_iter().map(|_| FreeVarsOp::Pop));
                    stack.extend(ops);
                }
                Expr::Neg(expr) => {
                    stack.push(FreeVarsOp::Expr(&*expr));
                }
                Expr::And(e1, e2)
                | Expr::Plus(e1, e2)
                | Expr::Minus(e1, e2)
                | Expr::Prod(e1, e2)
                | Expr::Div(e1, e2)
                | Expr::Eq(e1, e2)
                | Expr::Or(e1, e2) => {
                    stack.push(FreeVarsOp::Expr(&*e1));
                    stack.push(FreeVarsOp::Expr(&*e2));
                }
                Expr::Call(fun, arg) => {
                    if !ctx.contains(&fun) {
                        ret.insert(fun.clone());
                    }
                    stack.push(FreeVarsOp::Expr(&*arg));
                }
                Expr::If { test, then, alt } => {
                    stack.push(FreeVarsOp::Expr(&*test));
                    stack.push(FreeVarsOp::Expr(&*then));
                    stack.push(FreeVarsOp::Expr(&*alt));
                }
                Expr::Bool(..) | Expr::Int(..) | Expr::String(..) | Expr::Unit => {}
                Expr::Tuple(exprs) => {
                    stack.extend(exprs.iter().map(FreeVarsOp::Expr));
                }
                Expr::TupleAccess(expr, _) => {
                    stack.push(FreeVarsOp::Expr(&*expr));
                }
            }
        }

        ret
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Bool,
    String,
    Int,
    Func(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Unit,
}

#[derive(Debug)]
pub enum Declaration {
    Let(String, Expr),
    LetRec(String, Type, Expr),
    Expr(Expr),
}

#[allow(dead_code)]
#[derive(Default)]
pub struct Interner {
    strings: Vec<String>,
    from_string: HashMap<String, usize>,
}

#[allow(dead_code)]
impl Interner {
    fn insert(&mut self, s: String) -> InternerIndex {
        if let Some(&idx) = self.from_string.get(&s) {
            return InternerIndex(idx);
        }
        let index = self.strings.len();
        self.strings.push(s.clone());
        self.from_string.insert(s, index);
        InternerIndex(index)
    }

    fn get(&self, index: InternerIndex) -> &str {
        &self.strings[index.0]
    }
}

#[derive(Clone, Copy, PartialEq, Debug, Eq)]
struct InternerIndex(usize);
