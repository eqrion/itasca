//! Compile initialization expressions and segment writes into ordinary bytecode.
use super::*;
use crate::{ConstExpr, DataMode, ElementMode};

fn emit<A: Alloc>(
    budget: &mut Budget<A>,
    code: &mut Vec<Instr>,
    instruction: Instr,
) -> VisitResult {
    budget.charge(CompileResource::Instructions)?;
    budget.push(code, instruction)
}

fn constant<A: Alloc>(
    budget: &mut Budget<A>,
    function: &mut CompiledFunction,
    expr: ConstExpr,
    ty: ValueType,
    dst: u32,
) -> VisitResult {
    let instruction = match expr {
        ConstExpr::I32(v) => Instr::Const32 {
            dst,
            value: v as u32,
        },
        ConstExpr::I64(v) => Instr::Const64 {
            dst,
            value: v as u64,
        },
        ConstExpr::F32(value) => Instr::Const32 { dst, value },
        ConstExpr::F64(value) => Instr::Const64 { dst, value },
        ConstExpr::V128(lo, hi) => {
            let pool = bounded_index(function.v128_pool.len())?;
            budget.push(&mut function.v128_pool, lo as u128 | ((hi as u128) << 64))?;
            Instr::ConstV128 { dst, pool }
        }
        ConstExpr::RefNull(_) => Instr::RefNull { dst },
        ConstExpr::RefFunc(func) => Instr::RefFunc { dst, func },
        ConstExpr::GlobalGet(global) => match ty {
            ValueType::V128 => Instr::GlobalGet2 { dst, global },
            _ => Instr::GlobalGet { dst, global },
        },
    };
    emit(budget, &mut function.code, instruction)
}

fn expression<A: Alloc>(
    module: &mut ExecutableModule,
    budget: &mut Budget<A>,
    expr: ConstExpr,
    ty: ValueType,
) -> Result<usize, VisitError> {
    let mut function = CompiledFunction::synthetic(Vec::new(), width(ty));
    constant(budget, &mut function, expr, ty, 0)?;
    emit(
        budget,
        &mut function.code,
        Instr::Return {
            src: 0,
            n: width(ty),
        },
    )?;
    let index = module.functions.len();
    if !function.well_formed() {
        return Err(VisitError::OutOfMemory);
    }
    budget.push(&mut module.functions, function)?;
    Ok(index)
}

fn lower_global<A: Alloc>(
    module: &mut ExecutableModule,
    budget: &mut Budget<A>,
    index: usize,
) -> VisitResult {
    let global = module.env().globals()[index];
    let code = expression(module, budget, global.init, global.gtype.valtype)?;
    budget.push(&mut module.global_initializers, code)
}
fn lower_element_value<A: Alloc>(
    module: &mut ExecutableModule,
    budget: &mut Budget<A>,
    indices: &mut Vec<usize>,
    i: usize,
    j: usize,
) -> VisitResult {
    let expr = module.env().elements()[i].init[j];
    let ty = module.env().elements()[i].elem.value_type();
    let index = expression(module, budget, expr, ty)?;
    budget.push(indices, index)
}
fn element_offset(env: &Env, i: usize) -> Option<ConstExpr> {
    let mode = env.elements()[i].mode;
    match mode {
        ElementMode::Active { offset, .. } => Some(offset),
        _ => None,
    }
}

fn lower_element<A: Alloc>(
    module: &mut ExecutableModule,
    budget: &mut Budget<A>,
    i: usize,
) -> VisitResult {
    let mut indices = Vec::new();
    let mut j = 0;
    let mut result = Ok(());
    while j < module.env().elements()[i].init.len() && result.is_ok() {
        result = lower_element_value(module, budget, &mut indices, i, j);
        j += 1;
    }
    result?;
    budget.push(&mut module.element_initializers, indices)?;
    let offset = match element_offset(module.env(), i) {
        Some(expr) => Some(expression(module, budget, expr, ValueType::I32)?),
        None => None,
    };
    budget.push(&mut module.element_offsets, offset)
}
fn lower_data_offset<A: Alloc>(
    module: &mut ExecutableModule,
    budget: &mut Budget<A>,
    i: usize,
) -> VisitResult {
    let mode = module.tail().data[i].mode;
    let offset = match mode {
        DataMode::Active { offset, .. } => {
            Some(expression(module, budget, offset, ValueType::I32)?)
        }
        _ => None,
    };
    budget.push(&mut module.data_offsets, offset)
}
fn emit_element<A: Alloc>(
    module: &ExecutableModule,
    budget: &mut Budget<A>,
    function: &mut CompiledFunction,
    i: usize,
) -> VisitResult {
    let segment = &module.env().elements()[i];
    let mode = segment.mode;
    match mode {
        ElementMode::Active { table_idx, offset } => {
            function.slot_count = 3;
            constant(budget, function, offset, ValueType::I32, 0)?;
            emit(
                budget,
                &mut function.code,
                Instr::Const32 { dst: 1, value: 0 },
            )?;
            emit(
                budget,
                &mut function.code,
                Instr::Const32 {
                    dst: 2,
                    value: bounded_index(segment.init.len())?,
                },
            )?;
            let entry = bounded_index(function.indirect.len())?;
            budget.push(&mut function.indirect, (bounded_index(i)?, table_idx))?;
            emit(budget, &mut function.code, Instr::TableInit { d: 0, entry })?;
            emit(
                budget,
                &mut function.code,
                Instr::ElemDrop {
                    elem: bounded_index(i)?,
                },
            )
        }
        ElementMode::Declarative => emit(
            budget,
            &mut function.code,
            Instr::ElemDrop {
                elem: bounded_index(i)?,
            },
        ),
        ElementMode::Passive => Ok(()),
    }
}
fn emit_data<A: Alloc>(
    module: &ExecutableModule,
    budget: &mut Budget<A>,
    function: &mut CompiledFunction,
    i: usize,
) -> VisitResult {
    let segment = &module.tail().data[i];
    let mode = segment.mode;
    if let DataMode::Active { offset, .. } = mode {
        function.slot_count = 3;
        constant(budget, function, offset, ValueType::I32, 0)?;
        emit(
            budget,
            &mut function.code,
            Instr::Const32 { dst: 1, value: 0 },
        )?;
        emit(
            budget,
            &mut function.code,
            Instr::Const32 {
                dst: 2,
                value: bounded_index(segment.init.len())?,
            },
        )?;
        emit(
            budget,
            &mut function.code,
            Instr::MemoryInit {
                d: 0,
                data: bounded_index(i)?,
            },
        )?;
        emit(
            budget,
            &mut function.code,
            Instr::DataDrop {
                data: bounded_index(i)?,
            },
        )?;
    }
    Ok(())
}
pub(super) fn lower<A: Alloc>(
    module: &mut ExecutableModule,
    budget: &mut Budget<A>,
) -> VisitResult {
    let mut i = 0;
    let mut result = Ok(());
    while i < module.env().globals().len() && result.is_ok() {
        result = lower_global(module, budget, i);
        i += 1;
    }
    result?;
    i = 0;
    while i < module.env().elements().len() && result.is_ok() {
        result = lower_element(module, budget, i);
        i += 1;
    }
    result?;
    i = 0;
    while i < module.tail().data.len() && result.is_ok() {
        result = lower_data_offset(module, budget, i);
        i += 1;
    }
    result?;
    let mut function = CompiledFunction::synthetic(Vec::new(), 0);
    i = 0;
    while i < module.env().elements().len() && result.is_ok() {
        result = emit_element(module, budget, &mut function, i);
        i += 1;
    }
    result?;
    i = 0;
    while i < module.tail().data.len() && result.is_ok() {
        result = emit_data(module, budget, &mut function, i);
        i += 1;
    }
    result?;
    emit(budget, &mut function.code, Instr::Return { src: 0, n: 0 })?;
    if !function.well_formed() {
        return Err(VisitError::OutOfMemory);
    }
    module.initialization = module.functions.len();
    budget.push(&mut module.functions, function)
}
