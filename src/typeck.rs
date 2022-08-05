use crate::ast;
use ast::{StringIndex, TypeIndex};
use std::collections::{hash_map::Entry, HashMap, HashSet};

type TyResult = Result<ast::Type, String>;

struct TyContext<'a> {
    bound: HashMap<StringIndex, Vec<ast::Type>>,
    interner: &'a ast::Interner,
    aliases: HashMap<TypeIndex, ast::Type>,
    resolved: HashMap<ast::Type, Option<ast::Type>>,
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

    fn get_resolved(&mut self, ty: ast::Type) -> ast::Type {
        if let Some(resolved) = self.resolved.get(&ty) {
            return resolved.clone().unwrap_or(ty);
        }

        let mut final_ty = ty.clone();
        self.aliases
            .iter()
            .for_each(|(var, resolved_ty)| final_ty.substitute(*var, resolved_ty.clone()));
        let value = if final_ty == ty {
            None
        } else {
            Some(final_ty.clone())
        };

        self.resolved.insert(ty, value);
        final_ty
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
        aliases: resolved_types,
        resolved: Default::default(),
    };

    let _ = type_check_declarations(&program.0, &mut typing_context)?;

    if let Some(expr) = &program.1 {
        typecheck_expr(expr, &mut typing_context)
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
                final_ty = typecheck_expr(expr, ctx)?;
            }
            ast::Declaration::Let(var, expr) => {
                let ty = typecheck_expr(expr, ctx)?;
                final_ty = ty.clone();

                ctx.insert(*var, ty);
                vars.insert(*var);
            }
            ast::Declaration::LetRec(var, ty, expr) => {
                let ty = ty.as_ref().ok_or("letrec must declare a type")?;

                let resolved_ty = ctx.get_resolved(ty.clone());
                if !matches!(resolved_ty, ast::Type::Func(..)) {
                    Err(format!(
                        "letrec can only declare function types: {:?}",
                        resolved_ty
                    ))?;
                }
                ctx.insert(var.clone(), resolved_ty.clone());
                let computed_ty_result = typecheck_expr(expr, ctx);

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

fn typecheck_expr(expr: &ast::Expr, ctx: &mut TyContext) -> TyResult {
    let ty = match expr {
        ast::Expr::Unit => ast::Type::Unit,
        ast::Expr::Int(_) => ast::Type::Int,
        ast::Expr::Bool(_) => ast::Type::Bool,
        ast::Expr::String(_) => ast::Type::String,
        ast::Expr::Var(var) => ctx.get(*var).cloned().ok_or(format!(
            "Variable {} is not defined",
            var.display(ctx.interner)
        ))?,
        ast::Expr::Plus(op1, op2) => {
            let ty1 = typecheck_expr(op1, ctx)?;
            let ty2 = typecheck_expr(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be added: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => ast::Type::Int,
                ast::Type::String => ast::Type::String,
                _ => Err(format!("Values of type {:?} cannot be added", ty1))?,
            }
        }
        ast::Expr::Eq(op1, op2) => {
            let ty1 = typecheck_expr(op1, ctx)?;
            let ty2 = typecheck_expr(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be compared for equality: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int | ast::Type::String | ast::Type::Bool => ast::Type::Bool,
                _ => Err(format!(
                    "Values of type {:?} cannot be compared for equality",
                    ty1
                ))?,
            }
        }
        ast::Expr::Lt(op1, op2)
        | ast::Expr::Lte(op1, op2)
        | ast::Expr::Gt(op1, op2)
        | ast::Expr::Gte(op1, op2) => {
            let ty1 = typecheck_expr(op1, ctx)?;
            let ty2 = typecheck_expr(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be compared by order: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => ast::Type::Bool,
                _ => Err(format!(
                    "Values of type {:?} cannot be compared by order",
                    ty1
                ))?,
            }
        }
        ast::Expr::Minus(op1, op2) => {
            let ty1 = typecheck_expr(op1, ctx)?;
            let ty2 = typecheck_expr(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be substracted: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => ast::Type::Int,
                _ => Err(format!("Values of type {:?} cannot be substracted", ty1))?,
            }
        }
        ast::Expr::Prod(op1, op2) => {
            let ty1 = typecheck_expr(op1, ctx)?;
            let ty2 = typecheck_expr(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be multiplied: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => ast::Type::Int,
                _ => Err(format!("Values of type {:?} cannot be multiplied", ty1))?,
            }
        }
        ast::Expr::Div(op1, op2) => {
            let ty1 = typecheck_expr(op1, ctx)?;
            let ty2 = typecheck_expr(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be divided: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Int => ast::Type::Int,
                _ => Err(format!("Values of type {:?} cannot be divided", ty1))?,
            }
        }
        ast::Expr::Neg(op) => {
            let ty = typecheck_expr(op, ctx)?;

            if let ast::Type::Bool = ty {
                ast::Type::Bool
            } else {
                Err(format!(
                    "Negation operator can only be applied to booleans (got {:?})",
                    ty
                ))?
            }
        }
        ast::Expr::And(op1, op2) => {
            let ty1 = typecheck_expr(op1, ctx)?;
            let ty2 = typecheck_expr(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be AND'ed: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Bool => ast::Type::Bool,
                _ => Err(format!("Values of type {:?} cannot be AND'ed", ty1))?,
            }
        }
        ast::Expr::Or(op1, op2) => {
            let ty1 = typecheck_expr(op1, ctx)?;
            let ty2 = typecheck_expr(op2, ctx)?;
            if ty1 != ty2 {
                Err(format!(
                    "Different types cannot be OR'ed: [{:?}] + [{:?}]",
                    ty1, ty2
                ))?
            }

            match ty1 {
                ast::Type::Bool => ast::Type::Bool,
                _ => Err(format!("Values of type {:?} cannot be OR'ed", ty1))?,
            }
        }
        ast::Expr::Call(fun, arg) => {
            let fun_ty = ctx.get(*fun).cloned().ok_or(format!(
                "Variable {} is not defined",
                fun.display(ctx.interner)
            ))?;
            let arg_ty = typecheck_expr(arg, ctx)?;

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
                (*out_ty).clone()
            } else {
                Err(format!(
                    "Argument of type {:?} cannot be passed to function expecting {:?}",
                    arg_ty, in_ty
                ))?
            }
        }
        ast::Expr::Func { arg, body, ty } => {
            let resolved_ty = ctx.get_resolved(ty.clone());
            ctx.insert(*arg, resolved_ty.clone());

            let ty_result = typecheck_expr(body, ctx);

            ctx.pop(*arg);

            ty_result.map(|ret_ty| ast::Type::Func(Box::new(resolved_ty), Box::new(ret_ty)))?
        }
        ast::Expr::If { test, then, alt } => {
            let test_ty = typecheck_expr(test, ctx)?;

            if !matches!(test_ty, ast::Type::Bool) {
                Err("if test must be boolean")?
            }

            let then_ty = typecheck_expr(then, ctx)?;
            let alt_ty = typecheck_expr(alt, ctx)?;

            if then_ty == alt_ty {
                then_ty
            } else {
                Err(format!(
                    "if branches must have same type: {:?} vs. {:?}",
                    then_ty, alt_ty
                ))?
            }
        }
        ast::Expr::Block(declarations, expr) => {
            let (_, vars) = type_check_declarations(&declarations[..], ctx)?;

            let result = typecheck_expr(expr, ctx);

            for var in vars {
                ctx.pop(var);
            }

            result?
        }
        ast::Expr::Tuple(exprs) => {
            let types: Vec<_> = exprs
                .iter()
                .map(|ex| typecheck_expr(ex, ctx))
                .collect::<Result<_, _>>()?;
            ast::Type::Tuple(types)
        }
        ast::Expr::TupleAccess(expr, index) => {
            let ty = typecheck_expr(expr, ctx)?;

            if let ast::Type::Tuple(types) = ty {
                if *index >= types.len() {
                    Err(format!("Out of bounds tuple access"))?
                } else {
                    types[*index].clone()
                }
            } else {
                Err(format!("Illegal tuple access for non-tuple {:?}", ty))?
            }
        }
        ast::Expr::ArrayInit { elements, update } => {
            debug_assert!(elements.len() > 0);

            let element_types: Vec<_> = elements
                .iter()
                .map(|(el, rest)| typecheck_expr(el, ctx).map(|ty| (ty, *rest)))
                .collect::<Result<_, _>>()?;

            let mut array_ty = None;
            for (ty, rest) in element_types {
                let candidate = match (ty, rest) {
                    (ty, false) => ty,
                    (ast::Type::Array(ty), true) => *ty,
                    (_, true) => Err("Rest operator ... can only be applied to arrays")?,
                };
                array_ty = match (array_ty, candidate) {
                    (None, ty) => Some(ty),
                    (Some(array_ty), ty) => {
                        if array_ty != ty {
                            Err(format!("Expected array of {:?}, found {:?}", ty, array_ty))?
                        }

                        Some(array_ty)
                    }
                }
            }

            let array_ty = array_ty.unwrap();

            if let Some((index, value)) = update.as_deref() {
                if !matches!(typecheck_expr(index, ctx)?, ast::Type::Int) {
                    Err("Update index must be int")?
                }

                if typecheck_expr(value, ctx)? != array_ty {
                    Err("Update value must match array type")?
                }
            }

            ast::Type::Array(array_ty.into())
        }
        ast::Expr::ImplicitArrayInit { init, length } => {
            let array_ty = typecheck_expr(init, ctx)?;

            // TODO: review alias substitution

            if !array_ty.has_default() {
                Err(format!(
                    "Cannot build default arrays of non-default types {:?}",
                    array_ty
                ))?
            }

            if typecheck_expr(length, ctx)? != ast::Type::Int {
                Err("Array length must be an integer")?
            }

            ast::Type::Array(array_ty.into())
        }
        ast::Expr::ArrayAccess {
            array,
            index,
            default,
        } => {
            let array_ty = typecheck_expr(array, ctx)?;
            let index_ty = typecheck_expr(index, ctx)?;
            let default_ty = typecheck_expr(default, ctx)?;

            let element_ty = if let ast::Type::Array(ty) = array_ty {
                *ty
            } else {
                Err("Cannot update non-array")?
            };

            if element_ty != default_ty {
                Err("Default element must be of same type as array")?
            }

            if index_ty != ast::Type::Int {
                Err("Index type must be int")?
            }

            default_ty
        }
    };

    Ok(ctx.get_resolved(ty))
}

#[derive(Default)]
struct NamesVisitor {
    declared: Vec<(TypeIndex, ast::Type)>,
    refs: HashSet<TypeIndex>,
}

impl ast::Visitor for NamesVisitor {
    fn visit_declaration(&mut self, declaration: &ast::Declaration) {
        match declaration {
            ast::Declaration::LetRec(_, Some(ty), _) => {
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
            | ast::Expr::Lt(_, _)
            | ast::Expr::Lte(_, _)
            | ast::Expr::Gt(_, _)
            | ast::Expr::Gte(_, _)
            | ast::Expr::If { .. }
            | ast::Expr::Block(_, _)
            | ast::Expr::Tuple(_)
            | ast::Expr::TupleAccess(_, _)
            | ast::Expr::ArrayAccess { .. }
            | ast::Expr::ArrayInit { .. }
            | ast::Expr::ImplicitArrayInit { .. }
            | ast::Expr::Unit => {}
        }

        ast::visit_expr(self, expr);
    }
}
