use crate::ast;
use std::collections::{HashMap, HashSet};

type TyResult = Result<ast::Type, String>;

#[derive(Default)]
struct TyContext {
    bound: HashMap<String, Vec<ast::Type>>,
}

impl TyContext {
    fn insert(&mut self, var: String, ty: ast::Type) {
        self.bound.entry(var).or_insert_with(|| vec![]).push(ty)
    }

    fn get(&self, var: impl AsRef<str>) -> Option<&ast::Type> {
        self.bound.get(var.as_ref()).and_then(|types| types.last())
    }

    fn pop(&mut self, var: String) {
        use std::collections::hash_map::Entry;
        if let Entry::Occupied(occ) = self.bound.entry(var).and_modify(|types| {
            types.pop();
        }) {
            if occ.get().is_empty() {
                let _ = occ.remove();
            }
        }
    }
}

pub fn type_check(program: &ast::Program) -> TyResult {
    if program.0.is_empty() && program.1.is_none() {
        Err("Empty program")?
    }

    let mut typing_context: TyContext = Default::default();

    let _ = type_check_declarations(&program.0, &mut typing_context)?;

    if let Some(expr) = &program.1 {
        type_check_in_context(expr, &mut typing_context)
    } else {
        Ok(ast::Type::Unit)
    }
}

fn type_check_declarations(
    declarations: &[ast::Declaration],
    ctx: &mut TyContext,
) -> Result<(ast::Type, HashSet<String>), String> {
    let mut final_ty = ast::Type::Bool;
    let mut vars = HashSet::new();

    for decl in declarations {
        match decl {
            ast::Declaration::Expr(expr) => {
                final_ty = type_check_in_context(expr, ctx)?;
            }
            ast::Declaration::Let(var, expr) => {
                let ty = type_check_in_context(expr, ctx)?;
                final_ty = ty.clone();

                ctx.insert(var.clone(), ty);
                vars.insert(var.clone());
            }
            ast::Declaration::LetRec(var, ty, expr) => {
                if !matches!(ty, ast::Type::Func(..)) {
                    Err(format!("letrec can only declare function types"))?;
                }
                ctx.insert(var.clone(), ty.clone());
                let computed_ty_result = type_check_in_context(expr, ctx);

                match computed_ty_result {
                    Err(err) => {
                        ctx.pop(var.clone());
                        Err(err)?
                    }
                    Ok(computed_ty) => {
                        if &computed_ty != ty {
                            ctx.pop(var.clone());
                            Err(format!(
                                "Inconsistent recursive type: expected {:?}, got {:?}",
                                ty, computed_ty
                            ))?
                        }
                    }
                }
            }
        }
    }

    Ok((final_ty, vars))
}

fn type_check_in_context(expr: &ast::Expr, ctx: &mut TyContext) -> TyResult {
    match expr {
        ast::Expr::Unit => Ok(ast::Type::Unit),
        ast::Expr::Int(_) => Ok(ast::Type::Int),
        ast::Expr::Bool(_) => Ok(ast::Type::Bool),
        ast::Expr::String(_) => Ok(ast::Type::String),
        ast::Expr::Var(var) => ctx
            .get(var)
            .cloned()
            .ok_or(format!("Variable {} is not defined", var)),
        ast::Expr::Plus(op1, op2) => {
            let ty1 = type_check_in_context(op1, ctx)?;
            let ty2 = type_check_in_context(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be added: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => Ok(ast::Type::Int),
                ast::Type::String => Ok(ast::Type::String),
                _ => Err(format!("Values of type {:?} cannot be added", ty1)),
            }
        }
        ast::Expr::Eq(op1, op2) => {
            let ty1 = type_check_in_context(op1, ctx)?;
            let ty2 = type_check_in_context(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be compared for equality: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int | ast::Type::String | ast::Type::Bool => Ok(ast::Type::Bool),
                _ => Err(format!(
                    "Values of type {:?} cannot be compared for equality",
                    ty1
                )),
            }
        }
        ast::Expr::Minus(op1, op2) => {
            let ty1 = type_check_in_context(op1, ctx)?;
            let ty2 = type_check_in_context(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be substracted: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => Ok(ast::Type::Int),
                _ => Err(format!("Values of type {:?} cannot be substracted", ty1)),
            }
        }
        ast::Expr::Prod(op1, op2) => {
            let ty1 = type_check_in_context(op1, ctx)?;
            let ty2 = type_check_in_context(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be multiplied: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => Ok(ast::Type::Int),
                _ => Err(format!("Values of type {:?} cannot be multiplied", ty1)),
            }
        }
        ast::Expr::Div(op1, op2) => {
            let ty1 = type_check_in_context(op1, ctx)?;
            let ty2 = type_check_in_context(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be divided: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => Ok(ast::Type::Int),
                _ => Err(format!("Values of type {:?} cannot be divided", ty1)),
            }
        }
        ast::Expr::Neg(op) => {
            let ty = type_check_in_context(op, ctx)?;

            if let ast::Type::Bool = ty {
                Ok(ast::Type::Bool)
            } else {
                Err(format!(
                    "Negation operator can only be applied to booleans (got {:?})",
                    ty
                ))
            }
        }
        ast::Expr::And(op1, op2) => {
            let ty1 = type_check_in_context(op1, ctx)?;
            let ty2 = type_check_in_context(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be AND'ed: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Bool => Ok(ast::Type::Bool),
                _ => Err(format!("Values of type {:?} cannot be AND'ed", ty1)),
            }
        }
        ast::Expr::Or(op1, op2) => {
            let ty1 = type_check_in_context(op1, ctx)?;
            let ty2 = type_check_in_context(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be OR'ed: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Bool => Ok(ast::Type::Bool),
                _ => Err(format!("Values of type {:?} cannot be OR'ed", ty1)),
            }
        }
        ast::Expr::Call(fun, arg) => {
            let fun_ty = ctx
                .get(fun)
                .cloned()
                .ok_or(format!("Variable {} is not defined", fun))?;
            let arg_ty = type_check_in_context(arg, ctx)?;

            let (in_ty, out_ty) = if let ast::Type::Func(in_ty, out_ty) = fun_ty {
                (in_ty, out_ty)
            } else {
                Err(format!("Value ´{}´ is not a function: {:?}", fun, fun_ty))?
            };

            if *in_ty == arg_ty {
                Ok((*out_ty).clone())
            } else {
                Err(format!(
                    "Argument of type {:?} cannot be passed to function expecting {:?}",
                    arg_ty, in_ty
                ))
            }
        }
        ast::Expr::Func { arg, body, ty } => {
            ctx.insert(arg.clone(), ty.clone());

            let ty_result = type_check_in_context(body, ctx);

            ctx.pop(arg.clone());

            ty_result.map(|ret_ty| ast::Type::Func(Box::new(ty.clone()), Box::new(ret_ty)))
        }
        ast::Expr::If { test, then, alt } => {
            let test_ty = type_check_in_context(test, ctx)?;

            if !matches!(test_ty, ast::Type::Bool) {
                Err("if test must be boolean")?
            }

            let then_ty = type_check_in_context(then, ctx)?;
            let alt_ty = type_check_in_context(alt, ctx)?;

            if then_ty == alt_ty {
                Ok(then_ty)
            } else {
                Err(format!(
                    "if branches must have same type: {:?} vs. {:?}",
                    then_ty, alt_ty
                ))
            }
        }
        ast::Expr::Block(declarations, expr) => {
            let (_, vars) = type_check_declarations(&declarations[..], ctx)?;

            let result = type_check_in_context(expr, ctx);

            for var in vars {
                ctx.pop(var);
            }

            result
        }
        ast::Expr::Tuple(exprs) => {
            let types: Vec<_> = exprs
                .iter()
                .map(|ex| type_check_in_context(ex, ctx))
                .collect::<Result<_, _>>()?;
            Ok(ast::Type::Tuple(types))
        }
        ast::Expr::TupleAccess(expr, index) => {
            let ty = type_check_in_context(expr, ctx)?;

            if let ast::Type::Tuple(types) = ty {
                if *index >= types.len() {
                    Err(format!("Out of bounds tuple access"))
                } else {
                    Ok(types[*index].clone())
                }
            } else {
                Err(format!("Illegal tuple access for non-tuple {:?}", ty))
            }
        }
    }
}
