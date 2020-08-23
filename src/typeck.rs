use crate::ast;
use ast::{StringIndex, TypeIndex};
use std::collections::{hash_map::Entry, HashMap, HashSet};

type TyResult = Result<ast::Type, String>;

struct TyContext<'a> {
    bound: HashMap<StringIndex, Vec<ast::Type>>,
    interner: &'a ast::Interner,
    resolved: HashMap<TypeIndex, ast::Type>,
}

impl<'a> TyContext<'a> {
    fn insert(&mut self, var: StringIndex, ty: ast::Type) {
        self.bound.entry(var).or_insert_with(|| vec![]).push(ty)
    }

    fn get(&self, var: StringIndex) -> Option<&ast::Type> {
        self.bound.get(&var).and_then(|types| types.last())
    }

    fn pop(&mut self, var: StringIndex) {
        if let Entry::Occupied(occ) = self.bound.entry(var).and_modify(|types| {
            types.pop();
        }) {
            if occ.get().is_empty() {
                let _ = occ.remove();
            }
        }
    }
}

pub fn type_check_program(program: &ast::Program, interner: &ast::Interner) -> TyResult {
    if program.0.is_empty() && program.1.is_none() {
        Err("Empty program")?
    }

    let mut visitor = NamesVisitor::default();
    ast::Visitor::visit_program(&mut visitor, program);

    let resolved_types = type_check_type_declarations(visitor.declared, visitor.refs, interner)?;

    let mut typing_context: TyContext = TyContext {
        interner,
        bound: Default::default(),
        resolved: resolved_types,
    };

    let _ = type_check_declarations(&program.0, &mut typing_context)?;

    if let Some(expr) = &program.1 {
        type_check_in_context(expr, &mut typing_context)
    } else {
        Ok(ast::Type::Unit)
    }
}

fn type_check_type_declarations(
    declarations: Vec<(TypeIndex, ast::Type)>,
    refs: HashSet<TypeIndex>,
    interner: &ast::Interner,
) -> Result<HashMap<TypeIndex, ast::Type>, String> {
    let (mut to_deps, mut to_be_resolved) = {
        let mut to_deps = HashMap::new();
        let mut to_resolved = HashMap::new();

        for (name, ty) in declarations {
            if to_deps.contains_key(&name) {
                Err(format!(
                    "Type {} is declared multiple times",
                    name.display(interner)
                ))?
            }

            to_deps.insert(name, ty.vars());
            to_resolved.insert(name, ty);
        }

        (to_deps, to_resolved)
    };

    for ty in refs {
        if !to_deps.contains_key(&ty) {
            Err(format!("Type {} is never declared", ty.display(interner)))?
        }
    }

    let mut to_dependent = to_deps
        .iter()
        .flat_map(|(ty, deps)| {
            let ty = *ty;
            deps.iter().map(move |dep| (*dep, ty))
        })
        .fold(HashMap::new(), |mut acc, (dep, ty)| {
            acc.entry(dep).or_insert_with(|| HashSet::new()).insert(ty);
            acc
        });

    let mut resolved: HashMap<TypeIndex, ast::Type> = HashMap::new();

    loop {
        if to_deps.is_empty() {
            break;
        }

        let to_eliminate = match to_deps.iter().find(|(_, deps)| deps.is_empty()) {
            Some((ty, _)) => *ty,
            _ => Err("Type definitions are circular")?,
        };

        let _ = to_deps.remove(&to_eliminate);

        // brute force
        to_be_resolved.entry(to_eliminate).and_modify(|ty| {
            resolved.iter().for_each(|(var, resolved_ty)| {
                ty.substitute(var.clone(), resolved_ty.clone());
            });
        });

        to_be_resolved
            .remove(&to_eliminate)
            .into_iter()
            .for_each(|resolved_ty| {
                resolved.insert(to_eliminate, resolved_ty);
            });

        let removed = to_dependent.remove(&to_eliminate);

        for dependent in removed.into_iter().flat_map(|x| x) {
            to_deps.entry(dependent).and_modify(|deps| {
                deps.remove(&to_eliminate);
            });
        }
    }

    Ok(resolved)
}

fn type_check_declarations(
    declarations: &[ast::Declaration],
    ctx: &mut TyContext,
) -> Result<(ast::Type, HashSet<StringIndex>), String> {
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

                ctx.insert(*var, ty);
                vars.insert(*var);
            }
            ast::Declaration::LetRec(var, ty, expr) => {
                let resolved_ty = {
                    let mut ty = ty.clone();

                    ctx.resolved.iter().for_each(|(name, resolved_ty)| {
                        ty.substitute(*name, resolved_ty.clone());
                    });

                    ty
                };
                if !matches!(resolved_ty, ast::Type::Func(..)) {
                    Err(format!(
                        "letrec can only declare function types: {:?}",
                        resolved_ty
                    ))?;
                }
                ctx.insert(var.clone(), resolved_ty.clone());
                let computed_ty_result = type_check_in_context(expr, ctx);

                match computed_ty_result {
                    Err(err) => {
                        ctx.pop(var.clone());
                        Err(err)?
                    }
                    Ok(computed_ty) => {
                        if computed_ty != resolved_ty {
                            ctx.pop(var.clone());
                            Err(format!(
                                "Inconsistent recursive type: expected {:?}, got {:?}",
                                ty, computed_ty
                            ))?
                        }
                    }
                }
            }
            ast::Declaration::Type(..) => { /* done */ }
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
        ast::Expr::Var(var) => ctx.get(*var).cloned().ok_or(format!(
            "Variable {} is not defined",
            var.display(ctx.interner)
        )),
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
            let fun_ty = ctx.get(*fun).cloned().ok_or(format!(
                "Variable {} is not defined",
                fun.display(ctx.interner)
            ))?;
            let arg_ty = type_check_in_context(arg, ctx)?;

            let (in_ty, out_ty) = if let ast::Type::Func(in_ty, out_ty) = fun_ty {
                (in_ty, out_ty)
            } else {
                Err(format!(
                    "Value ´{}´ is not a function: {:?}",
                    fun.display(ctx.interner),
                    fun_ty
                ))?
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
            let resolved_ty = {
                let mut ty = ty.clone();

                ctx.resolved.iter().for_each(|(name, resolved_ty)| {
                    ty.substitute(*name, resolved_ty.clone());
                });

                ty
            };
            ctx.insert(*arg, resolved_ty.clone());

            let ty_result = type_check_in_context(body, ctx);

            ctx.pop(*arg);

            ty_result.map(|ret_ty| ast::Type::Func(Box::new(resolved_ty), Box::new(ret_ty)))
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

#[derive(Default)]
struct NamesVisitor {
    declared: Vec<(TypeIndex, ast::Type)>,
    refs: HashSet<TypeIndex>,
}

impl ast::Visitor for NamesVisitor {
    fn visit_declaration(&mut self, declaration: &ast::Declaration) {
        match declaration {
            ast::Declaration::LetRec(_, ty, _) => {
                self.refs.extend(ty.vars().into_iter());
            }
            ast::Declaration::Type(name, ty) => {
                self.declared.push((*name, ty.clone()));
            }
            _ => {}
        }

        ast::visit_declaration(self, declaration);
    }

    fn visit_expr(&mut self, expr: &ast::Expr) {
        match expr {
            ast::Expr::Func { ty, .. } => {
                self.refs.extend(ty.vars().into_iter());
            }
            ast::Expr::Bool(_)
            | ast::Expr::String(_)
            | ast::Expr::Var(_)
            | ast::Expr::Int(_)
            | ast::Expr::Call(_, _)
            | ast::Expr::Neg(_)
            | ast::Expr::Plus(_, _)
            | ast::Expr::Minus(_, _)
            | ast::Expr::Prod(_, _)
            | ast::Expr::Div(_, _)
            | ast::Expr::And(_, _)
            | ast::Expr::Or(_, _)
            | ast::Expr::Eq(_, _)
            | ast::Expr::If { .. }
            | ast::Expr::Block(_, _)
            | ast::Expr::Tuple(_)
            | ast::Expr::TupleAccess(_, _)
            | ast::Expr::Unit => {}
        }

        ast::visit_expr(self, expr);
    }
}
