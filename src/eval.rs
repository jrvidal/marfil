use crate::ast::{self, Interner, StringIndex};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::{fmt, ops::Deref};

#[derive(Clone)]
pub struct Branch(Rc<Vec<Op>>);

impl fmt::Debug for Branch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Branch")
            .field(&format!("{:p}", self.0))
            .finish()
    }
}

impl Deref for Branch {
    type Target = [Op];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone)]
pub struct Env {
    vars: Rc<HashMap<StringIndex, Value>>,
}

impl fmt::Debug for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.vars.keys()).finish()
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Unit,
    Int(i64),
    String(Rc<String>),
    Bool(bool),
    Fn(Branch, Env),
    Tuple(Vec<Value>),
    Address(Branch, usize, Option<Env>),
    Self_,
}

type Step = usize;

#[derive(Debug)]
pub enum Op {
    PushSelf,
    PushInt(i64),
    PushString(Rc<String>),
    PushBool(bool),
    PushFn(Branch, HashSet<StringIndex>),
    PushUnit,
    Load(StringIndex),
    Store(StringIndex),
    Pop,
    PushEnv,
    PopEnv,
    JumpUnless(Step),
    JumpIf(Step),
    Jump(Step),
    Dup,
    Add,
    Substract,
    Multiply,
    Divide,
    Compare,
    Negate,
    Call,
    Ret,
    Tuple(usize),
    TupleAccess(usize),
}

pub fn compile(program: ast::Program) -> Result<Vec<Op>, String> {
    let mut buffer = vec![];
    for declaration in program.0 {
        compile_declaration(declaration, &mut buffer)?;
    }

    if let Some(expr) = program.1 {
        compile_expr(expr, &mut buffer)?;
    }

    Ok(buffer)
}

pub struct Machine {
    stack: Vec<Value>,
    envs: Vec<HashMap<StringIndex, Value>>,
    branch: Branch,
    pc: usize,
    self_: Option<Env>,
    interner: Interner,
}

impl Machine {
    pub fn new(ops: Vec<Op>, interner: Interner) -> Machine {
        Machine {
            pc: 0,
            envs: vec![HashMap::new()],
            stack: vec![],
            branch: Branch(Rc::new(ops)),
            self_: None,
            interner,
        }
    }

    pub fn run(mut self) -> Result<Value, String> {
        while self.pc < self.branch.len() {
            self.tick()?;
        }

        if self.stack.len() > 1 {
            Err("Unexpected multiple values")?
        } else {
            Ok(self.stack.pop().unwrap_or(Value::Unit))
        }
    }

    fn tick(&mut self) -> Result<(), String> {
        log::trace!(
            "\nPC={}\t{:?}\nLocals: {:?}\nStack: {:?}",
            self.pc,
            self.branch.0,
            self.envs,
            self.stack
        );
        let op = &self.branch[self.pc];

        match op {
            Op::PushUnit => self.stack.push(Value::Unit),
            Op::PushSelf => self.stack.push(Value::Self_),
            Op::PushString(s) => self.stack.push(Value::String(s.clone())),
            Op::PushInt(n) => self.stack.push(Value::Int(*n)),
            Op::PushBool(b) => self.stack.push(Value::Bool(*b)),
            Op::PushFn(fun, free_vars) => {
                let env = free_vars
                    .iter()
                    .filter_map(|var| self.read(*var).ok().map(|val| (var.clone(), val)))
                    .collect::<HashMap<_, _>>();
                self.stack
                    .push(Value::Fn(fun.clone(), Env { vars: Rc::new(env) }));
            }
            Op::Load(var) => {
                let val = self.read(*var)?;
                self.stack.push(val);
            }
            Op::Store(var) => {
                let var = var.clone();
                let val = self.pop()?;
                self.env().insert(var, val);
            }
            Op::Pop => {
                self.stack.pop();
            }
            Op::PushEnv => {
                self.envs.push(HashMap::new());
            }
            Op::PopEnv => {
                self.envs.pop();
                if self.envs.is_empty() {
                    Err("Envs should not be empty")?
                }
            }
            Op::Jump(step) => {
                self.pc += step;
                return Ok(());
            }
            Op::JumpUnless(step) => {
                let step = *step;
                let val = self.pop()?;
                if let Value::Bool(cond) = val {
                    if !cond {
                        self.pc += step;
                        return Ok(());
                    }
                } else {
                    Err("Expected bool")?
                }
            }
            Op::JumpIf(step) => {
                let step = *step;
                let val = self.pop()?;
                if let Value::Bool(cond) = val {
                    if cond {
                        self.pc += step;
                        return Ok(());
                    }
                } else {
                    Err("Expected bool")?
                }
            }
            Op::Add => {
                let val1 = self.pop()?;
                let val2 = self.pop()?;

                let result = match (val1, val2) {
                    (Value::Int(m), Value::Int(n)) => Value::Int(m + n),
                    (Value::String(s1), Value::String(s2)) => {
                        Value::String(Rc::new(String::new() + &s1 + &s2))
                    }
                    _ => Err("Invalid types for add")?,
                };

                self.stack.push(result);
            }
            Op::Substract => {
                let val1 = self.pop()?;
                let val2 = self.pop()?;

                let result = match (val1, val2) {
                    (Value::Int(m), Value::Int(n)) => Value::Int(n - m),
                    _ => Err("Invalid types for substract")?,
                };

                self.stack.push(result);
            }
            Op::Multiply => {
                let val1 = self.pop()?;
                let val2 = self.pop()?;

                let result = match (val1, val2) {
                    (Value::Int(m), Value::Int(n)) => Value::Int(m * n),
                    _ => Err("Invalid types for Multiply")?,
                };

                self.stack.push(result);
            }
            Op::Divide => {
                let val1 = self.pop()?;
                let val2 = self.pop()?;

                let result = match (val1, val2) {
                    (Value::Int(m), Value::Int(n)) => Value::Int(n / m),
                    _ => Err("Invalid types for Divide")?,
                };

                self.stack.push(result);
            }
            // Op::And => {
            //     let val1 = self.pop()?;
            //     let val2 = self.pop()?;

            //     let result = match (val1, val2) {
            //         (Value::Bool(b), Value::Bool(c)) => Value::Bool(b && c),
            //         _ => Err("Invalid types for And")?,
            //     };

            //     self.stack.push(result);
            // }
            Op::Negate => {
                let val1 = self.pop()?;

                let result = match val1 {
                    Value::Bool(b) => Value::Bool(!b),
                    _ => Err("Invalid types for Negate")?,
                };

                self.stack.push(result);
            }
            // Op::Or => {
            //     let val1 = self.pop()?;
            //     let val2 = self.pop()?;

            //     let result = match (val1, val2) {
            //         (Value::Bool(b), Value::Bool(c)) => Value::Bool(b || c),
            //         _ => Err("Invalid types for Or")?,
            //     };

            //     self.stack.push(result);
            // }
            Op::Compare => {
                let val1 = self.pop()?;
                let val2 = self.pop()?;

                let result = match (val1, val2) {
                    (Value::Bool(b), Value::Bool(c)) => Value::Bool(b == c),
                    (Value::Int(b), Value::Int(c)) => Value::Bool(b == c),
                    (Value::String(b), Value::String(c)) => Value::Bool(b == c),
                    _ => Err("Invalid types for Compare")?,
                };

                self.stack.push(result);
            }
            Op::Call => {
                let arg = self.pop()?;
                let fun = self.pop()?;
                let (new_branch, env) = match fun {
                    Value::Fn(branch, env) => (branch, env),
                    Value::Self_ => (
                        self.branch.clone(),
                        self.self_.clone().ok_or("Invalid self call")?,
                    ),
                    _ => Err("Unexpected non-callable value")?,
                };

                let ret = Value::Address(self.branch.clone(), self.pc + 1, self.self_.clone());
                self.stack.push(ret);
                self.stack.push(arg);
                let new_env = (&*env.vars).clone();
                self.envs.push(new_env);
                self.pc = 0;
                self.branch = new_branch;
                self.self_ = Some(env.clone());
                return Ok(());
            }
            Op::Ret => {
                let ret_value = self.pop()?;
                let ret_address = self.pop()?;
                self.envs.pop();
                let (branch, pc, env) = if let Value::Address(branch, pc, env) = ret_address {
                    (branch, pc, env)
                } else {
                    Err("Unable to find return address")?
                };
                self.stack.push(ret_value);
                self.branch = branch;
                self.pc = pc;
                self.self_ = env;
                return Ok(());
            }
            Op::Dup => {
                let val = self.pop()?;
                self.stack.push(val.clone());
                self.stack.push(val);
            }
            Op::Tuple(n) => {
                let mut vals = vec![];
                for _ in 0..*n {
                    let val = self.pop()?;
                    vals.push(val);
                }
                self.stack.push(Value::Tuple(vals))
            }
            Op::TupleAccess(index) => {
                let index = *index;
                let val = self.pop()?;
                match val {
                    Value::Tuple(vals) => {
                        let component = vals
                            .get(index)
                            .cloned()
                            .ok_or("Unexpected out of range index")?;
                        self.stack.push(component);
                    }
                    _ => Err("Unexpected index access for non-indexable value")?,
                }
            }
        }

        self.pc += 1;
        Ok(())
    }

    fn env(&mut self) -> &mut HashMap<StringIndex, Value> {
        self.envs.last_mut().unwrap()
    }

    fn read(&self, var: StringIndex) -> Result<Value, String> {
        for env in self.envs.iter().rev() {
            if let Some(val) = env.get(&var) {
                return Ok(val.clone());
            }
        }

        Err(format!(
            "Unable to find {} in environment",
            var.display(&self.interner)
        ))?
    }

    fn pop(&mut self) -> Result<Value, String> {
        self.stack
            .pop()
            .ok_or("Stack should not be empty".to_string())
    }
}

fn compile_expr(expr: ast::Expr, buffer: &mut Vec<Op>) -> Result<(), String> {
    match expr {
        ast::Expr::Bool(b) => buffer.push(Op::PushBool(b)),
        ast::Expr::String(s) => buffer.push(Op::PushString(Rc::new(s))),
        ast::Expr::Int(n) => buffer.push(Op::PushInt(n)),
        ast::Expr::Var(var) => buffer.push(Op::Load(var)),
        ast::Expr::Neg(op) => {
            compile_expr(*op, buffer)?;
            buffer.push(Op::Negate);
        }
        ast::Expr::Plus(op1, op2) => {
            compile_expr(*op1, buffer)?;
            compile_expr(*op2, buffer)?;
            buffer.push(Op::Add);
        }
        ast::Expr::Minus(op1, op2) => {
            compile_expr(*op1, buffer)?;
            compile_expr(*op2, buffer)?;
            buffer.push(Op::Substract);
        }
        ast::Expr::Prod(op1, op2) => {
            compile_expr(*op1, buffer)?;
            compile_expr(*op2, buffer)?;
            buffer.push(Op::Multiply);
        }
        ast::Expr::Div(op1, op2) => {
            compile_expr(*op1, buffer)?;
            compile_expr(*op2, buffer)?;
            buffer.push(Op::Divide);
        }
        ast::Expr::And(op1, op2) => {
            compile_expr(*op1, buffer)?;
            let mut op2_ops = vec![];
            compile_expr(*op2, &mut op2_ops)?;
            buffer.push(Op::Dup);
            buffer.push(Op::JumpUnless(op2_ops.len() + 2));
            buffer.push(Op::Pop);
            buffer.extend(op2_ops);
        }
        ast::Expr::Or(op1, op2) => {
            compile_expr(*op1, buffer)?;
            let mut op2_ops = vec![];
            compile_expr(*op2, &mut op2_ops)?;
            buffer.push(Op::Dup);
            buffer.push(Op::JumpIf(op2_ops.len() + 2));
            buffer.push(Op::Pop);
            buffer.extend(op2_ops);
        }
        ast::Expr::Eq(op1, op2) => {
            compile_expr(*op1, buffer)?;
            compile_expr(*op2, buffer)?;
            buffer.push(Op::Compare);
        }
        ast::Expr::If { test, then, alt } => {
            compile_expr(*test, buffer)?;

            let mut then_ops = vec![];
            compile_expr(*then, &mut then_ops)?;
            let mut alt_ops = vec![];
            compile_expr(*alt, &mut alt_ops)?;

            buffer.push(Op::JumpUnless(then_ops.len() + 2));
            buffer.extend(then_ops);
            buffer.push(Op::Jump(alt_ops.len() + 1));
            buffer.extend(alt_ops);
        }
        ast::Expr::Func { body, arg, .. } => {
            let mut free_vars = body.free_vars();
            free_vars.remove(&arg);
            let mut fn_code = vec![Op::Store(arg)];
            compile_expr(*body, &mut fn_code)?;
            fn_code.push(Op::Ret);
            buffer.push(Op::PushFn(Branch(Rc::new(fn_code)), free_vars));
        }
        ast::Expr::Call(fun, arg) => {
            buffer.push(Op::Load(fun));
            compile_expr(*arg, buffer)?;
            buffer.push(Op::Call);
        }
        ast::Expr::Block(decls, expr) => {
            buffer.push(Op::PushEnv);
            for decl in decls {
                compile_declaration(decl, buffer)?;
            }
            compile_expr(*expr, buffer)?;
            buffer.push(Op::PopEnv);
        }
        ast::Expr::Unit => buffer.push(Op::PushUnit),
        ast::Expr::Tuple(exprs) => {
            let n = exprs.len();
            for expr in exprs.into_iter().rev() {
                compile_expr(expr, buffer)?;
            }
            buffer.push(Op::Tuple(n));
        }
        ast::Expr::TupleAccess(expr, index) => {
            compile_expr(*expr, buffer)?;
            buffer.push(Op::TupleAccess(index));
        }
    }

    Ok(())
}

fn compile_declaration(decl: ast::Declaration, buffer: &mut Vec<Op>) -> Result<(), String> {
    match decl {
        ast::Declaration::Expr(expr) => {
            compile_expr(expr, buffer)?;
            buffer.push(Op::Pop);
        }
        ast::Declaration::Let(var, expr) => {
            compile_expr(expr, buffer)?;
            buffer.push(Op::Store(var));
        }
        ast::Declaration::LetRec(var, _, expr) => {
            buffer.push(Op::PushSelf);
            buffer.push(Op::Store(var.clone()));
            compile_expr(expr, buffer)?;
            buffer.push(Op::Store(var));
        }
        ast::Declaration::Type(_, _) => {}
    }
    Ok(())
}
