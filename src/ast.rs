use std::{
    collections::{HashMap, HashSet},
    fmt,
};

#[derive(Debug)]
pub struct Program(pub Vec<Declaration>, pub Option<Expr>);

#[derive(Debug)]
pub enum Expr {
    Bool(bool),
    ArrayInit {
        elements: Vec<(Expr, bool)>,
        update: Option<Box<(Expr, Expr)>>
    },
    ImplicitArrayInit {
        init: Box<Expr>,
        length: Box<Expr>
    },
    ArrayAccess {
        array: StringIndex,
        index: Box<Expr>,
        default: Box<Expr>
    },
    String(String),
    Var(StringIndex),
    Int(i64),
    Func {
        arg: StringIndex,
        ty: Type,
        body: Box<Expr>,
    },
    Call(StringIndex, Box<Expr>),
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
    pub fn free_vars(&self) -> HashSet<StringIndex> {
        enum FreeVarsOp<'a> {
            Expr(&'a Expr),
            Pop,
            Push(StringIndex),
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
                    ctx.push(*arg);
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
                                ops.push(FreeVarsOp::Push(*var));
                                vars.push(var);
                                ops.push(FreeVarsOp::Expr(expr));
                            }
                            Declaration::LetRec(var, _, expr) => {
                                ops.push(FreeVarsOp::Expr(expr));
                                ops.push(FreeVarsOp::Push(*var));
                                vars.push(var);
                            }
                            Declaration::Type(..) => {}
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
                        ret.insert(*fun);
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
                Expr::ArrayInit { elements, update } => {
                    stack.extend(elements.iter().map(|(e, _)| FreeVarsOp::Expr(e)));
                    if let Some((index, value)) = update.as_deref() {
                        stack.push(FreeVarsOp::Expr(index));
                        stack.push(FreeVarsOp::Expr(value));
                    }
                }
                Expr::ImplicitArrayInit { init, length } => {
                    stack.push(FreeVarsOp::Expr(&*init));
                    stack.push(FreeVarsOp::Expr(&*length));
                }
                Expr::ArrayAccess { array, index, default } => {
                    if !ctx.contains(array) {
                        ret.insert(*array);
                    }
                    stack.push(FreeVarsOp::Expr(&*index));
                    stack.push(FreeVarsOp::Expr(&*default));
                }
            }
        }

        ret
    }
}

pub trait Visitor: Sized {
    fn visit_program(&mut self, program: &Program) {
        visit_program(self, program)
    }

    fn visit_declaration(&mut self, declaration: &Declaration) {
        visit_declaration(self, declaration)
    }

    fn visit_expr(&mut self, expr: &Expr) {
        visit_expr(self, expr)
    }
}

pub fn visit_program(v: &mut impl Visitor, program: &Program) {
    for decl in &program.0 {
        v.visit_declaration(decl);
    }
    program.1.iter().for_each(|expr| v.visit_expr(expr));
}

pub fn visit_declaration(v: &mut impl Visitor, declaration: &Declaration) {
    match declaration {
        Declaration::Expr(expr) => v.visit_expr(expr),
        Declaration::Let(_, expr) => v.visit_expr(expr),
        Declaration::LetRec(_, _, expr) => v.visit_expr(expr),
        Declaration::Type(..) => {}
    }
}

pub fn visit_expr(v: &mut impl Visitor, expr: &Expr) {
    match expr {
        Expr::Bool(_) | Expr::String(_) | Expr::Var(_) | Expr::Unit | Expr::Int(_) => {}
        Expr::Call(_, e) | Expr::Func { body: e, .. } | Expr::TupleAccess(e, _) | Expr::Neg(e) => {
            v.visit_expr(e)
        }
        Expr::Plus(e1, e2)
        | Expr::Minus(e1, e2)
        | Expr::Prod(e1, e2)
        | Expr::Div(e1, e2)
        | Expr::And(e1, e2)
        | Expr::Or(e1, e2)
        | Expr::Eq(e1, e2) => {
            v.visit_expr(e1);
            v.visit_expr(e2);
        }
        Expr::If { test, then, alt } => {
            v.visit_expr(test);
            v.visit_expr(then);
            v.visit_expr(alt);
        }
        Expr::Block(decls, e) => {
            decls.iter().for_each(|decl| v.visit_declaration(decl));
            v.visit_expr(e);
        }
        Expr::Tuple(exprs) => exprs.iter().for_each(|e| v.visit_expr(e)),
        Expr::ArrayInit { elements, update } => {
            elements.iter().for_each(|(ex, _)| v.visit_expr(ex));
            update.as_deref().iter().for_each(|(index, value)| {
                v.visit_expr(index);
                v.visit_expr(value);
            });
        }
        Expr::ImplicitArrayInit { init, length } => {
            v.visit_expr(init);
            v.visit_expr(length);
        }
        Expr::ArrayAccess { array, index, default } => {
            v.visit_expr(index);
            v.visit_expr(default);
        }
    }
}

impl Type {
    pub fn vars(&self) -> HashSet<TypeIndex> {
        let mut ret: HashSet<TypeIndex> = Default::default();
        let mut stack = vec![self];

        while let Some(ty) = stack.pop() {
            match ty {
                Type::Bool | Type::String | Type::Int | Type::Unit => {}
                Type::Var(name) => {
                    ret.insert(*name);
                }
                Type::Func(arg, out) => {
                    stack.push(arg);
                    stack.push(out);
                },
                Type::Array(ty) => {
                    stack.push(ty);
                },
                Type::Tuple(tys) => {
                    stack.extend(tys.iter());
                }
            }
        }

        ret
    }

    pub fn substitute(&mut self, var: TypeIndex, ty: Type) {
        match self {
            Type::Bool | Type::String | Type::Int | Type::Unit => {}
            Type::Func(arg, out) => {
                arg.substitute(var, ty.clone());
                out.substitute(var, ty);
            }
            Type::Tuple(tys) => {
                tys.iter_mut()
                    .for_each(|tuple_ty| tuple_ty.substitute(var, ty.clone()));
            }
            Type::Var(v) => {
                if var == *v {
                    *self = ty;
                }
            }
            Type::Array(array_ty) => array_ty.substitute(var, ty)
        }
    }

    pub fn has_default(&self) -> bool {
        let mut stack = vec![self];

        while let Some(ty) = stack.pop() {
            match ty {
                Type::Func(_, _) => return false,
                Type::Bool |
                Type::String |
                Type::Int |
                Type::Unit => {}
                Type::Array(array_ty) => {
                    stack.push(array_ty);
                }
                Type::Tuple(tys) => {
                    stack.extend(tys.iter());
                }
                Type::Var(_) => unreachable!()
            }
        }

        true
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Bool,
    String,
    Int,
    Func(Box<Type>, Box<Type>),
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Var(TypeIndex),
    Unit,
}

#[derive(Debug)]
pub enum Declaration {
    Let(StringIndex, Expr),
    LetRec(StringIndex, Type, Expr),
    Expr(Expr),
    Type(TypeIndex, Type),
}

#[derive(Default)]
pub struct Interner {
    strings: Vec<String>,
    from_string: HashMap<String, usize>,
}

impl Interner {
    pub fn insert(&mut self, s: String) -> StringIndex {
        StringIndex(self.insert_raw(s))
    }

    pub fn insert_type(&mut self, s: String) -> TypeIndex {
        TypeIndex(self.insert_raw(s))
    }

    fn insert_raw(&mut self, s: String) -> usize {
        if let Some(&idx) = self.from_string.get(&s) {
            return idx;
        }
        let index = self.strings.len();
        self.strings.push(s.clone());
        self.from_string.insert(s, index);
        index
    }

    pub fn get(&self, index: impl InternerIndex) -> &str {
        &self.strings[index.raw()]
    }
}

pub trait InternerIndex {
    fn raw(&self) -> usize;
}

macro_rules! index_type {
    ($name:ident, $display:ident) => {
        #[derive(Clone, Copy, PartialEq, Debug, Eq, Hash)]
        pub struct $name(usize);

        pub struct $display<'a> {
            index: $name,
            interner: &'a Interner,
        }

        impl $name {
            pub fn display<'a>(&self, interner: &'a Interner) -> $display<'a> {
                $display {
                    index: *self,
                    interner,
                }
            }
        }

        impl<'a> fmt::Display for $display<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(self.interner.get(self.index))
            }
        }

        impl InternerIndex for $name {
            fn raw(&self) -> usize {
                self.0
            }
        }
    };
}

index_type![StringIndex, StringIndexDisplay];
index_type![TypeIndex, TypeIndexDisplay];

// #[derive(Clone, Copy, PartialEq, Debug, Eq, Hash)]
// pub struct StringIndex(usize);

// pub struct StringIndexDisplay<'a> {
//     index: StringIndex,
//     interner: &'a Interner
// }

// impl StringIndex {
//     pub fn display<'a>(&self, interner: &'a Interner) -> StringIndexDisplay<'a> {
//         StringIndexDisplay {
//             index: *self,
//             interner
//         }
//     }
// }

// impl<'a> fmt::Display for StringIndexDisplay<'a> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         f.write_str(self.interner.get(self.index))
//     }
// }
