-- Handwritten adapters to canonical validator functions and primitive models.
module
public import Aeneas
public import Itasca.Generated.Funs
@[expose] public section
open Aeneas Aeneas.Std

namespace Exec
-- Reuse the checked validator implementations with their original types.
@[rust_fun "itasca::module::{itasca::module::Env}::elements"]
def module.Env.elements := Itasca.module.Env.impl.elements

@[rust_fun "itasca::module::{itasca::module::Env}::exports"]
def module.Env.exports := Itasca.module.Env.impl.exports

@[rust_fun "itasca::module::{itasca::module::Env}::func_type_indices"]
def module.Env.func_type_indices := Itasca.module.Env.impl.func_type_indices

@[rust_fun "itasca::module::{itasca::module::Env}::func_types"]
def module.Env.func_types := Itasca.module.Env.impl.func_types

@[rust_fun "itasca::module::{itasca::module::Env}::global_types"]
def module.Env.global_types := Itasca.module.Env.impl.global_types

@[rust_fun "itasca::module::{itasca::module::Env}::globals"]
def module.Env.globals := Itasca.module.Env.impl.globals

@[rust_fun "itasca::module::{itasca::module::Env}::imports"]
def module.Env.imports := Itasca.module.Env.impl.imports

@[rust_fun "itasca::module::{itasca::module::Env}::mem_types"]
def module.Env.mem_types := Itasca.module.Env.impl.mem_types

@[rust_fun "itasca::module::{itasca::module::Env}::start"]
def module.Env.start := Itasca.module.Env.impl.start

@[rust_fun "itasca::module::{itasca::module::Env}::table_types"]
def module.Env.table_types := Itasca.module.Env.impl.table_types

@[rust_fun "itasca::module::{itasca::module::Env}::types"]
def module.Env.types := Itasca.module.Env.impl.types

@[rust_fun "itasca::module::{itasca::module::Module}::env"]
def module.Module.env := Itasca.module.Module.impl.env

@[rust_fun "itasca::module::{itasca::module::Module}::tail"]
def module.Module.tail := Itasca.module.Module.impl.tail

@[rust_fun "itasca::types::{impl core::cmp::PartialEq<itasca::types::Mut> for itasca::types::Mut}::eq"]
def types.Mut.Insts.CoreCmpPartialEqMut.eq :=
  Itasca.types.Mut.Insts.CoreCmpPartialEqMut.eq

@[rust_fun "itasca::types::{impl core::cmp::PartialEq<itasca::types::ValueType> for itasca::types::ValueType}::eq"]
def types.ValueType.Insts.CoreCmpPartialEqValueType.eq :=
  Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq

@[rust_fun "itasca::types::{itasca::types::ElemType}::value_type"]
def types.ElemType.value_type := Itasca.types.ElemType.value_type

-- The opaque pass retains the default-method dictionary argument, while the
-- canonical checked no-op definition has no use for it.
@[rust_fun "itasca::module::ModuleVisitor::on_custom_section"]
def module.ModuleVisitor.on_custom_section.default {Self : Type}
    (_inst : Itasca.module.ModuleVisitor Self) :=
  @Itasca.module.ModuleVisitor.on_custom_section.default Self

-- Validator callbacks and the complete-module streaming driver.
@[rust_fun "itasca::code::OpVisitor::on_i32_eqz"]
def code.OpVisitor.on_i32_eqz.default := @Itasca.code.OpVisitor.on_i32_eqz.default

@[rust_fun "itasca::code::OpVisitor::on_i32_eq"]
def code.OpVisitor.on_i32_eq.default := @Itasca.code.OpVisitor.on_i32_eq.default

@[rust_fun "itasca::code::OpVisitor::on_i32_ne"]
def code.OpVisitor.on_i32_ne.default := @Itasca.code.OpVisitor.on_i32_ne.default

@[rust_fun "itasca::code::OpVisitor::on_i32_lt_s"]
def code.OpVisitor.on_i32_lt_s.default := @Itasca.code.OpVisitor.on_i32_lt_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_lt_u"]
def code.OpVisitor.on_i32_lt_u.default := @Itasca.code.OpVisitor.on_i32_lt_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_gt_s"]
def code.OpVisitor.on_i32_gt_s.default := @Itasca.code.OpVisitor.on_i32_gt_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_gt_u"]
def code.OpVisitor.on_i32_gt_u.default := @Itasca.code.OpVisitor.on_i32_gt_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_le_s"]
def code.OpVisitor.on_i32_le_s.default := @Itasca.code.OpVisitor.on_i32_le_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_le_u"]
def code.OpVisitor.on_i32_le_u.default := @Itasca.code.OpVisitor.on_i32_le_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_ge_s"]
def code.OpVisitor.on_i32_ge_s.default := @Itasca.code.OpVisitor.on_i32_ge_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_ge_u"]
def code.OpVisitor.on_i32_ge_u.default := @Itasca.code.OpVisitor.on_i32_ge_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_eqz"]
def code.OpVisitor.on_i64_eqz.default := @Itasca.code.OpVisitor.on_i64_eqz.default

@[rust_fun "itasca::code::OpVisitor::on_i64_eq"]
def code.OpVisitor.on_i64_eq.default := @Itasca.code.OpVisitor.on_i64_eq.default

@[rust_fun "itasca::code::OpVisitor::on_i64_ne"]
def code.OpVisitor.on_i64_ne.default := @Itasca.code.OpVisitor.on_i64_ne.default

@[rust_fun "itasca::code::OpVisitor::on_i64_lt_s"]
def code.OpVisitor.on_i64_lt_s.default := @Itasca.code.OpVisitor.on_i64_lt_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_lt_u"]
def code.OpVisitor.on_i64_lt_u.default := @Itasca.code.OpVisitor.on_i64_lt_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_gt_s"]
def code.OpVisitor.on_i64_gt_s.default := @Itasca.code.OpVisitor.on_i64_gt_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_gt_u"]
def code.OpVisitor.on_i64_gt_u.default := @Itasca.code.OpVisitor.on_i64_gt_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_le_s"]
def code.OpVisitor.on_i64_le_s.default := @Itasca.code.OpVisitor.on_i64_le_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_le_u"]
def code.OpVisitor.on_i64_le_u.default := @Itasca.code.OpVisitor.on_i64_le_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_ge_s"]
def code.OpVisitor.on_i64_ge_s.default := @Itasca.code.OpVisitor.on_i64_ge_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_ge_u"]
def code.OpVisitor.on_i64_ge_u.default := @Itasca.code.OpVisitor.on_i64_ge_u.default

@[rust_fun "itasca::code::OpVisitor::on_f32_eq"]
def code.OpVisitor.on_f32_eq.default := @Itasca.code.OpVisitor.on_f32_eq.default

@[rust_fun "itasca::code::OpVisitor::on_f32_ne"]
def code.OpVisitor.on_f32_ne.default := @Itasca.code.OpVisitor.on_f32_ne.default

@[rust_fun "itasca::code::OpVisitor::on_f32_lt"]
def code.OpVisitor.on_f32_lt.default := @Itasca.code.OpVisitor.on_f32_lt.default

@[rust_fun "itasca::code::OpVisitor::on_f32_gt"]
def code.OpVisitor.on_f32_gt.default := @Itasca.code.OpVisitor.on_f32_gt.default

@[rust_fun "itasca::code::OpVisitor::on_f32_le"]
def code.OpVisitor.on_f32_le.default := @Itasca.code.OpVisitor.on_f32_le.default

@[rust_fun "itasca::code::OpVisitor::on_f32_ge"]
def code.OpVisitor.on_f32_ge.default := @Itasca.code.OpVisitor.on_f32_ge.default

@[rust_fun "itasca::code::OpVisitor::on_f64_eq"]
def code.OpVisitor.on_f64_eq.default := @Itasca.code.OpVisitor.on_f64_eq.default

@[rust_fun "itasca::code::OpVisitor::on_f64_ne"]
def code.OpVisitor.on_f64_ne.default := @Itasca.code.OpVisitor.on_f64_ne.default

@[rust_fun "itasca::code::OpVisitor::on_f64_lt"]
def code.OpVisitor.on_f64_lt.default := @Itasca.code.OpVisitor.on_f64_lt.default

@[rust_fun "itasca::code::OpVisitor::on_f64_gt"]
def code.OpVisitor.on_f64_gt.default := @Itasca.code.OpVisitor.on_f64_gt.default

@[rust_fun "itasca::code::OpVisitor::on_f64_le"]
def code.OpVisitor.on_f64_le.default := @Itasca.code.OpVisitor.on_f64_le.default

@[rust_fun "itasca::code::OpVisitor::on_f64_ge"]
def code.OpVisitor.on_f64_ge.default := @Itasca.code.OpVisitor.on_f64_ge.default

@[rust_fun "itasca::code::OpVisitor::on_i32_sub"]
def code.OpVisitor.on_i32_sub.default := @Itasca.code.OpVisitor.on_i32_sub.default

@[rust_fun "itasca::code::OpVisitor::on_i32_mul"]
def code.OpVisitor.on_i32_mul.default := @Itasca.code.OpVisitor.on_i32_mul.default

@[rust_fun "itasca::code::OpVisitor::on_i32_div_s"]
def code.OpVisitor.on_i32_div_s.default := @Itasca.code.OpVisitor.on_i32_div_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_div_u"]
def code.OpVisitor.on_i32_div_u.default := @Itasca.code.OpVisitor.on_i32_div_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_rem_s"]
def code.OpVisitor.on_i32_rem_s.default := @Itasca.code.OpVisitor.on_i32_rem_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_rem_u"]
def code.OpVisitor.on_i32_rem_u.default := @Itasca.code.OpVisitor.on_i32_rem_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_and"]
def code.OpVisitor.on_i32_and.default := @Itasca.code.OpVisitor.on_i32_and.default

@[rust_fun "itasca::code::OpVisitor::on_i32_or"]
def code.OpVisitor.on_i32_or.default := @Itasca.code.OpVisitor.on_i32_or.default

@[rust_fun "itasca::code::OpVisitor::on_i32_xor"]
def code.OpVisitor.on_i32_xor.default := @Itasca.code.OpVisitor.on_i32_xor.default

@[rust_fun "itasca::code::OpVisitor::on_i32_shl"]
def code.OpVisitor.on_i32_shl.default := @Itasca.code.OpVisitor.on_i32_shl.default

@[rust_fun "itasca::code::OpVisitor::on_i32_shr_s"]
def code.OpVisitor.on_i32_shr_s.default := @Itasca.code.OpVisitor.on_i32_shr_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_shr_u"]
def code.OpVisitor.on_i32_shr_u.default := @Itasca.code.OpVisitor.on_i32_shr_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_rotl"]
def code.OpVisitor.on_i32_rotl.default := @Itasca.code.OpVisitor.on_i32_rotl.default

@[rust_fun "itasca::code::OpVisitor::on_i32_rotr"]
def code.OpVisitor.on_i32_rotr.default := @Itasca.code.OpVisitor.on_i32_rotr.default

@[rust_fun "itasca::code::OpVisitor::on_i64_add"]
def code.OpVisitor.on_i64_add.default := @Itasca.code.OpVisitor.on_i64_add.default

@[rust_fun "itasca::code::OpVisitor::on_i64_sub"]
def code.OpVisitor.on_i64_sub.default := @Itasca.code.OpVisitor.on_i64_sub.default

@[rust_fun "itasca::code::OpVisitor::on_i64_mul"]
def code.OpVisitor.on_i64_mul.default := @Itasca.code.OpVisitor.on_i64_mul.default

@[rust_fun "itasca::code::OpVisitor::on_i64_div_s"]
def code.OpVisitor.on_i64_div_s.default := @Itasca.code.OpVisitor.on_i64_div_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_div_u"]
def code.OpVisitor.on_i64_div_u.default := @Itasca.code.OpVisitor.on_i64_div_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_rem_s"]
def code.OpVisitor.on_i64_rem_s.default := @Itasca.code.OpVisitor.on_i64_rem_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_rem_u"]
def code.OpVisitor.on_i64_rem_u.default := @Itasca.code.OpVisitor.on_i64_rem_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_and"]
def code.OpVisitor.on_i64_and.default := @Itasca.code.OpVisitor.on_i64_and.default

@[rust_fun "itasca::code::OpVisitor::on_i64_or"]
def code.OpVisitor.on_i64_or.default := @Itasca.code.OpVisitor.on_i64_or.default

@[rust_fun "itasca::code::OpVisitor::on_i64_xor"]
def code.OpVisitor.on_i64_xor.default := @Itasca.code.OpVisitor.on_i64_xor.default

@[rust_fun "itasca::code::OpVisitor::on_i64_shl"]
def code.OpVisitor.on_i64_shl.default := @Itasca.code.OpVisitor.on_i64_shl.default

@[rust_fun "itasca::code::OpVisitor::on_i64_shr_s"]
def code.OpVisitor.on_i64_shr_s.default := @Itasca.code.OpVisitor.on_i64_shr_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_shr_u"]
def code.OpVisitor.on_i64_shr_u.default := @Itasca.code.OpVisitor.on_i64_shr_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_rotl"]
def code.OpVisitor.on_i64_rotl.default := @Itasca.code.OpVisitor.on_i64_rotl.default

@[rust_fun "itasca::code::OpVisitor::on_i64_rotr"]
def code.OpVisitor.on_i64_rotr.default := @Itasca.code.OpVisitor.on_i64_rotr.default

@[rust_fun "itasca::code::OpVisitor::on_f32_add"]
def code.OpVisitor.on_f32_add.default := @Itasca.code.OpVisitor.on_f32_add.default

@[rust_fun "itasca::code::OpVisitor::on_f32_sub"]
def code.OpVisitor.on_f32_sub.default := @Itasca.code.OpVisitor.on_f32_sub.default

@[rust_fun "itasca::code::OpVisitor::on_f32_mul"]
def code.OpVisitor.on_f32_mul.default := @Itasca.code.OpVisitor.on_f32_mul.default

@[rust_fun "itasca::code::OpVisitor::on_f32_div"]
def code.OpVisitor.on_f32_div.default := @Itasca.code.OpVisitor.on_f32_div.default

@[rust_fun "itasca::code::OpVisitor::on_f32_min"]
def code.OpVisitor.on_f32_min.default := @Itasca.code.OpVisitor.on_f32_min.default

@[rust_fun "itasca::code::OpVisitor::on_f32_max"]
def code.OpVisitor.on_f32_max.default := @Itasca.code.OpVisitor.on_f32_max.default

@[rust_fun "itasca::code::OpVisitor::on_f32_copysign"]
def code.OpVisitor.on_f32_copysign.default := @Itasca.code.OpVisitor.on_f32_copysign.default

@[rust_fun "itasca::code::OpVisitor::on_f64_add"]
def code.OpVisitor.on_f64_add.default := @Itasca.code.OpVisitor.on_f64_add.default

@[rust_fun "itasca::code::OpVisitor::on_f64_sub"]
def code.OpVisitor.on_f64_sub.default := @Itasca.code.OpVisitor.on_f64_sub.default

@[rust_fun "itasca::code::OpVisitor::on_f64_mul"]
def code.OpVisitor.on_f64_mul.default := @Itasca.code.OpVisitor.on_f64_mul.default

@[rust_fun "itasca::code::OpVisitor::on_f64_div"]
def code.OpVisitor.on_f64_div.default := @Itasca.code.OpVisitor.on_f64_div.default

@[rust_fun "itasca::code::OpVisitor::on_f64_min"]
def code.OpVisitor.on_f64_min.default := @Itasca.code.OpVisitor.on_f64_min.default

@[rust_fun "itasca::code::OpVisitor::on_f64_max"]
def code.OpVisitor.on_f64_max.default := @Itasca.code.OpVisitor.on_f64_max.default

@[rust_fun "itasca::code::OpVisitor::on_f64_copysign"]
def code.OpVisitor.on_f64_copysign.default := @Itasca.code.OpVisitor.on_f64_copysign.default

@[rust_fun "itasca::code::OpVisitor::on_i32_clz"]
def code.OpVisitor.on_i32_clz.default := @Itasca.code.OpVisitor.on_i32_clz.default

@[rust_fun "itasca::code::OpVisitor::on_i32_ctz"]
def code.OpVisitor.on_i32_ctz.default := @Itasca.code.OpVisitor.on_i32_ctz.default

@[rust_fun "itasca::code::OpVisitor::on_i32_popcnt"]
def code.OpVisitor.on_i32_popcnt.default := @Itasca.code.OpVisitor.on_i32_popcnt.default

@[rust_fun "itasca::code::OpVisitor::on_i32_add"]
def code.OpVisitor.on_i32_add.default := @Itasca.code.OpVisitor.on_i32_add.default

@[rust_fun "itasca::code::OpVisitor::on_i64_clz"]
def code.OpVisitor.on_i64_clz.default := @Itasca.code.OpVisitor.on_i64_clz.default

@[rust_fun "itasca::code::OpVisitor::on_i64_ctz"]
def code.OpVisitor.on_i64_ctz.default := @Itasca.code.OpVisitor.on_i64_ctz.default

@[rust_fun "itasca::code::OpVisitor::on_i64_popcnt"]
def code.OpVisitor.on_i64_popcnt.default := @Itasca.code.OpVisitor.on_i64_popcnt.default

@[rust_fun "itasca::code::OpVisitor::on_f32_abs"]
def code.OpVisitor.on_f32_abs.default := @Itasca.code.OpVisitor.on_f32_abs.default

@[rust_fun "itasca::code::OpVisitor::on_f32_neg"]
def code.OpVisitor.on_f32_neg.default := @Itasca.code.OpVisitor.on_f32_neg.default

@[rust_fun "itasca::code::OpVisitor::on_f32_ceil"]
def code.OpVisitor.on_f32_ceil.default := @Itasca.code.OpVisitor.on_f32_ceil.default

@[rust_fun "itasca::code::OpVisitor::on_f32_floor"]
def code.OpVisitor.on_f32_floor.default := @Itasca.code.OpVisitor.on_f32_floor.default

@[rust_fun "itasca::code::OpVisitor::on_f32_trunc"]
def code.OpVisitor.on_f32_trunc.default := @Itasca.code.OpVisitor.on_f32_trunc.default

@[rust_fun "itasca::code::OpVisitor::on_f32_nearest"]
def code.OpVisitor.on_f32_nearest.default := @Itasca.code.OpVisitor.on_f32_nearest.default

@[rust_fun "itasca::code::OpVisitor::on_f32_sqrt"]
def code.OpVisitor.on_f32_sqrt.default := @Itasca.code.OpVisitor.on_f32_sqrt.default

@[rust_fun "itasca::code::OpVisitor::on_f64_abs"]
def code.OpVisitor.on_f64_abs.default := @Itasca.code.OpVisitor.on_f64_abs.default

@[rust_fun "itasca::code::OpVisitor::on_f64_neg"]
def code.OpVisitor.on_f64_neg.default := @Itasca.code.OpVisitor.on_f64_neg.default

@[rust_fun "itasca::code::OpVisitor::on_f64_ceil"]
def code.OpVisitor.on_f64_ceil.default := @Itasca.code.OpVisitor.on_f64_ceil.default

@[rust_fun "itasca::code::OpVisitor::on_f64_floor"]
def code.OpVisitor.on_f64_floor.default := @Itasca.code.OpVisitor.on_f64_floor.default

@[rust_fun "itasca::code::OpVisitor::on_f64_trunc"]
def code.OpVisitor.on_f64_trunc.default := @Itasca.code.OpVisitor.on_f64_trunc.default

@[rust_fun "itasca::code::OpVisitor::on_f64_nearest"]
def code.OpVisitor.on_f64_nearest.default := @Itasca.code.OpVisitor.on_f64_nearest.default

@[rust_fun "itasca::code::OpVisitor::on_f64_sqrt"]
def code.OpVisitor.on_f64_sqrt.default := @Itasca.code.OpVisitor.on_f64_sqrt.default

@[rust_fun "itasca::code::OpVisitor::on_i32_wrap_i64"]
def code.OpVisitor.on_i32_wrap_i64.default := @Itasca.code.OpVisitor.on_i32_wrap_i64.default

@[rust_fun "itasca::code::OpVisitor::on_i32_trunc_f32_s"]
def code.OpVisitor.on_i32_trunc_f32_s.default := @Itasca.code.OpVisitor.on_i32_trunc_f32_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_trunc_f32_u"]
def code.OpVisitor.on_i32_trunc_f32_u.default := @Itasca.code.OpVisitor.on_i32_trunc_f32_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_trunc_f64_s"]
def code.OpVisitor.on_i32_trunc_f64_s.default := @Itasca.code.OpVisitor.on_i32_trunc_f64_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_trunc_f64_u"]
def code.OpVisitor.on_i32_trunc_f64_u.default := @Itasca.code.OpVisitor.on_i32_trunc_f64_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_extend_i32_s"]
def code.OpVisitor.on_i64_extend_i32_s.default := @Itasca.code.OpVisitor.on_i64_extend_i32_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_extend_i32_u"]
def code.OpVisitor.on_i64_extend_i32_u.default := @Itasca.code.OpVisitor.on_i64_extend_i32_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_trunc_f32_s"]
def code.OpVisitor.on_i64_trunc_f32_s.default := @Itasca.code.OpVisitor.on_i64_trunc_f32_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_trunc_f32_u"]
def code.OpVisitor.on_i64_trunc_f32_u.default := @Itasca.code.OpVisitor.on_i64_trunc_f32_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_trunc_f64_s"]
def code.OpVisitor.on_i64_trunc_f64_s.default := @Itasca.code.OpVisitor.on_i64_trunc_f64_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_trunc_f64_u"]
def code.OpVisitor.on_i64_trunc_f64_u.default := @Itasca.code.OpVisitor.on_i64_trunc_f64_u.default

@[rust_fun "itasca::code::OpVisitor::on_f32_convert_i32_s"]
def code.OpVisitor.on_f32_convert_i32_s.default := @Itasca.code.OpVisitor.on_f32_convert_i32_s.default

@[rust_fun "itasca::code::OpVisitor::on_f32_convert_i32_u"]
def code.OpVisitor.on_f32_convert_i32_u.default := @Itasca.code.OpVisitor.on_f32_convert_i32_u.default

@[rust_fun "itasca::code::OpVisitor::on_f32_convert_i64_s"]
def code.OpVisitor.on_f32_convert_i64_s.default := @Itasca.code.OpVisitor.on_f32_convert_i64_s.default

@[rust_fun "itasca::code::OpVisitor::on_f32_convert_i64_u"]
def code.OpVisitor.on_f32_convert_i64_u.default := @Itasca.code.OpVisitor.on_f32_convert_i64_u.default

@[rust_fun "itasca::code::OpVisitor::on_f32_demote_f64"]
def code.OpVisitor.on_f32_demote_f64.default := @Itasca.code.OpVisitor.on_f32_demote_f64.default

@[rust_fun "itasca::code::OpVisitor::on_f64_convert_i32_s"]
def code.OpVisitor.on_f64_convert_i32_s.default := @Itasca.code.OpVisitor.on_f64_convert_i32_s.default

@[rust_fun "itasca::code::OpVisitor::on_f64_convert_i32_u"]
def code.OpVisitor.on_f64_convert_i32_u.default := @Itasca.code.OpVisitor.on_f64_convert_i32_u.default

@[rust_fun "itasca::code::OpVisitor::on_f64_convert_i64_s"]
def code.OpVisitor.on_f64_convert_i64_s.default := @Itasca.code.OpVisitor.on_f64_convert_i64_s.default

@[rust_fun "itasca::code::OpVisitor::on_f64_convert_i64_u"]
def code.OpVisitor.on_f64_convert_i64_u.default := @Itasca.code.OpVisitor.on_f64_convert_i64_u.default

@[rust_fun "itasca::code::OpVisitor::on_f64_promote_f32"]
def code.OpVisitor.on_f64_promote_f32.default := @Itasca.code.OpVisitor.on_f64_promote_f32.default

@[rust_fun "itasca::code::OpVisitor::on_i32_reinterpret_f32"]
def code.OpVisitor.on_i32_reinterpret_f32.default := @Itasca.code.OpVisitor.on_i32_reinterpret_f32.default

@[rust_fun "itasca::code::OpVisitor::on_i64_reinterpret_f64"]
def code.OpVisitor.on_i64_reinterpret_f64.default := @Itasca.code.OpVisitor.on_i64_reinterpret_f64.default

@[rust_fun "itasca::code::OpVisitor::on_f32_reinterpret_i32"]
def code.OpVisitor.on_f32_reinterpret_i32.default := @Itasca.code.OpVisitor.on_f32_reinterpret_i32.default

@[rust_fun "itasca::code::OpVisitor::on_f64_reinterpret_i64"]
def code.OpVisitor.on_f64_reinterpret_i64.default := @Itasca.code.OpVisitor.on_f64_reinterpret_i64.default

@[rust_fun "itasca::code::OpVisitor::on_i32_load"]
def code.OpVisitor.on_i32_load.default := @Itasca.code.OpVisitor.on_i32_load.default

@[rust_fun "itasca::code::OpVisitor::on_i64_load"]
def code.OpVisitor.on_i64_load.default := @Itasca.code.OpVisitor.on_i64_load.default

@[rust_fun "itasca::code::OpVisitor::on_f32_load"]
def code.OpVisitor.on_f32_load.default := @Itasca.code.OpVisitor.on_f32_load.default

@[rust_fun "itasca::code::OpVisitor::on_f64_load"]
def code.OpVisitor.on_f64_load.default := @Itasca.code.OpVisitor.on_f64_load.default

@[rust_fun "itasca::code::OpVisitor::on_i32_load8_s"]
def code.OpVisitor.on_i32_load8_s.default := @Itasca.code.OpVisitor.on_i32_load8_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_load8_u"]
def code.OpVisitor.on_i32_load8_u.default := @Itasca.code.OpVisitor.on_i32_load8_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_load16_s"]
def code.OpVisitor.on_i32_load16_s.default := @Itasca.code.OpVisitor.on_i32_load16_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_load16_u"]
def code.OpVisitor.on_i32_load16_u.default := @Itasca.code.OpVisitor.on_i32_load16_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_load8_s"]
def code.OpVisitor.on_i64_load8_s.default := @Itasca.code.OpVisitor.on_i64_load8_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_load8_u"]
def code.OpVisitor.on_i64_load8_u.default := @Itasca.code.OpVisitor.on_i64_load8_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_load16_s"]
def code.OpVisitor.on_i64_load16_s.default := @Itasca.code.OpVisitor.on_i64_load16_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_load16_u"]
def code.OpVisitor.on_i64_load16_u.default := @Itasca.code.OpVisitor.on_i64_load16_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_load32_s"]
def code.OpVisitor.on_i64_load32_s.default := @Itasca.code.OpVisitor.on_i64_load32_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_load32_u"]
def code.OpVisitor.on_i64_load32_u.default := @Itasca.code.OpVisitor.on_i64_load32_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_store"]
def code.OpVisitor.on_i32_store.default := @Itasca.code.OpVisitor.on_i32_store.default

@[rust_fun "itasca::code::OpVisitor::on_i64_store"]
def code.OpVisitor.on_i64_store.default := @Itasca.code.OpVisitor.on_i64_store.default

@[rust_fun "itasca::code::OpVisitor::on_f32_store"]
def code.OpVisitor.on_f32_store.default := @Itasca.code.OpVisitor.on_f32_store.default

@[rust_fun "itasca::code::OpVisitor::on_f64_store"]
def code.OpVisitor.on_f64_store.default := @Itasca.code.OpVisitor.on_f64_store.default

@[rust_fun "itasca::code::OpVisitor::on_i32_store8"]
def code.OpVisitor.on_i32_store8.default := @Itasca.code.OpVisitor.on_i32_store8.default

@[rust_fun "itasca::code::OpVisitor::on_i32_store16"]
def code.OpVisitor.on_i32_store16.default := @Itasca.code.OpVisitor.on_i32_store16.default

@[rust_fun "itasca::code::OpVisitor::on_i64_store8"]
def code.OpVisitor.on_i64_store8.default := @Itasca.code.OpVisitor.on_i64_store8.default

@[rust_fun "itasca::code::OpVisitor::on_i64_store16"]
def code.OpVisitor.on_i64_store16.default := @Itasca.code.OpVisitor.on_i64_store16.default

@[rust_fun "itasca::code::OpVisitor::on_i64_store32"]
def code.OpVisitor.on_i64_store32.default := @Itasca.code.OpVisitor.on_i64_store32.default

@[rust_fun "itasca::code::OpVisitor::on_ref_null"]
def code.OpVisitor.on_ref_null.default := @Itasca.code.OpVisitor.on_ref_null.default

@[rust_fun "itasca::code::OpVisitor::on_ref_is_null"]
def code.OpVisitor.on_ref_is_null.default := @Itasca.code.OpVisitor.on_ref_is_null.default

@[rust_fun "itasca::code::OpVisitor::on_ref_func"]
def code.OpVisitor.on_ref_func.default := @Itasca.code.OpVisitor.on_ref_func.default

@[rust_fun "itasca::code::OpVisitor::on_select_typed"]
def code.OpVisitor.on_select_typed.default := @Itasca.code.OpVisitor.on_select_typed.default

@[rust_fun "itasca::code::OpVisitor::on_table_get"]
def code.OpVisitor.on_table_get.default := @Itasca.code.OpVisitor.on_table_get.default

@[rust_fun "itasca::code::OpVisitor::on_table_set"]
def code.OpVisitor.on_table_set.default := @Itasca.code.OpVisitor.on_table_set.default

@[rust_fun "itasca::code::OpVisitor::on_memory_init"]
def code.OpVisitor.on_memory_init.default := @Itasca.code.OpVisitor.on_memory_init.default

@[rust_fun "itasca::code::OpVisitor::on_data_drop"]
def code.OpVisitor.on_data_drop.default := @Itasca.code.OpVisitor.on_data_drop.default

@[rust_fun "itasca::code::OpVisitor::on_memory_copy"]
def code.OpVisitor.on_memory_copy.default := @Itasca.code.OpVisitor.on_memory_copy.default

@[rust_fun "itasca::code::OpVisitor::on_memory_fill"]
def code.OpVisitor.on_memory_fill.default := @Itasca.code.OpVisitor.on_memory_fill.default

@[rust_fun "itasca::code::OpVisitor::on_table_init"]
def code.OpVisitor.on_table_init.default := @Itasca.code.OpVisitor.on_table_init.default

@[rust_fun "itasca::code::OpVisitor::on_elem_drop"]
def code.OpVisitor.on_elem_drop.default := @Itasca.code.OpVisitor.on_elem_drop.default

@[rust_fun "itasca::code::OpVisitor::on_table_copy"]
def code.OpVisitor.on_table_copy.default := @Itasca.code.OpVisitor.on_table_copy.default

@[rust_fun "itasca::code::OpVisitor::on_table_grow"]
def code.OpVisitor.on_table_grow.default := @Itasca.code.OpVisitor.on_table_grow.default

@[rust_fun "itasca::code::OpVisitor::on_table_size"]
def code.OpVisitor.on_table_size.default := @Itasca.code.OpVisitor.on_table_size.default

@[rust_fun "itasca::code::OpVisitor::on_table_fill"]
def code.OpVisitor.on_table_fill.default := @Itasca.code.OpVisitor.on_table_fill.default

@[rust_fun "itasca::code::OpVisitor::on_simd"]
def code.OpVisitor.on_simd.default := @Itasca.code.OpVisitor.on_simd.default

@[rust_fun "itasca::code::OpVisitor::on_simd_lane"]
def code.OpVisitor.on_simd_lane.default := @Itasca.code.OpVisitor.on_simd_lane.default

@[rust_fun "itasca::code::OpVisitor::on_simd_memory"]
def code.OpVisitor.on_simd_memory.default := @Itasca.code.OpVisitor.on_simd_memory.default

@[rust_fun "itasca::code::OpVisitor::on_simd_memory_lane"]
def code.OpVisitor.on_simd_memory_lane.default := @Itasca.code.OpVisitor.on_simd_memory_lane.default

@[rust_fun "itasca::code::OpVisitor::on_simd_const"]
def code.OpVisitor.on_simd_const.default := @Itasca.code.OpVisitor.on_simd_const.default

@[rust_fun "itasca::code::OpVisitor::on_simd_shuffle"]
def code.OpVisitor.on_simd_shuffle.default := @Itasca.code.OpVisitor.on_simd_shuffle.default

@[rust_fun "itasca::code::OpVisitor::on_i32_extend8_s"]
def code.OpVisitor.on_i32_extend8_s.default := @Itasca.code.OpVisitor.on_i32_extend8_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_extend16_s"]
def code.OpVisitor.on_i32_extend16_s.default := @Itasca.code.OpVisitor.on_i32_extend16_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_extend8_s"]
def code.OpVisitor.on_i64_extend8_s.default := @Itasca.code.OpVisitor.on_i64_extend8_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_extend16_s"]
def code.OpVisitor.on_i64_extend16_s.default := @Itasca.code.OpVisitor.on_i64_extend16_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_extend32_s"]
def code.OpVisitor.on_i64_extend32_s.default := @Itasca.code.OpVisitor.on_i64_extend32_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_trunc_sat_f32_s"]
def code.OpVisitor.on_i32_trunc_sat_f32_s.default := @Itasca.code.OpVisitor.on_i32_trunc_sat_f32_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_trunc_sat_f32_u"]
def code.OpVisitor.on_i32_trunc_sat_f32_u.default := @Itasca.code.OpVisitor.on_i32_trunc_sat_f32_u.default

@[rust_fun "itasca::code::OpVisitor::on_i32_trunc_sat_f64_s"]
def code.OpVisitor.on_i32_trunc_sat_f64_s.default := @Itasca.code.OpVisitor.on_i32_trunc_sat_f64_s.default

@[rust_fun "itasca::code::OpVisitor::on_i32_trunc_sat_f64_u"]
def code.OpVisitor.on_i32_trunc_sat_f64_u.default := @Itasca.code.OpVisitor.on_i32_trunc_sat_f64_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_trunc_sat_f32_s"]
def code.OpVisitor.on_i64_trunc_sat_f32_s.default := @Itasca.code.OpVisitor.on_i64_trunc_sat_f32_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_trunc_sat_f32_u"]
def code.OpVisitor.on_i64_trunc_sat_f32_u.default := @Itasca.code.OpVisitor.on_i64_trunc_sat_f32_u.default

@[rust_fun "itasca::code::OpVisitor::on_i64_trunc_sat_f64_s"]
def code.OpVisitor.on_i64_trunc_sat_f64_s.default := @Itasca.code.OpVisitor.on_i64_trunc_sat_f64_s.default

@[rust_fun "itasca::code::OpVisitor::on_i64_trunc_sat_f64_u"]
def code.OpVisitor.on_i64_trunc_sat_f64_u.default := @Itasca.code.OpVisitor.on_i64_trunc_sat_f64_u.default

@[rust_fun "itasca::code::OpVisitor::on_function_start"]
def code.OpVisitor.on_function_start.default := @Itasca.code.OpVisitor.on_function_start.default

@[rust_fun "itasca::code::OpVisitor::on_unreachable"]
def code.OpVisitor.on_unreachable.default := @Itasca.code.OpVisitor.on_unreachable.default

@[rust_fun "itasca::code::OpVisitor::on_nop"]
def code.OpVisitor.on_nop.default := @Itasca.code.OpVisitor.on_nop.default

@[rust_fun "itasca::code::OpVisitor::on_block"]
def code.OpVisitor.on_block.default := @Itasca.code.OpVisitor.on_block.default

@[rust_fun "itasca::code::OpVisitor::on_loop"]
def code.OpVisitor.on_loop.default := @Itasca.code.OpVisitor.on_loop.default

@[rust_fun "itasca::code::OpVisitor::on_if"]
def code.OpVisitor.on_if.default := @Itasca.code.OpVisitor.on_if.default

@[rust_fun "itasca::code::OpVisitor::on_else"]
def code.OpVisitor.on_else.default := @Itasca.code.OpVisitor.on_else.default

@[rust_fun "itasca::code::OpVisitor::on_end"]
def code.OpVisitor.on_end.default := @Itasca.code.OpVisitor.on_end.default

@[rust_fun "itasca::code::OpVisitor::on_br"]
def code.OpVisitor.on_br.default := @Itasca.code.OpVisitor.on_br.default

@[rust_fun "itasca::code::OpVisitor::on_br_if"]
def code.OpVisitor.on_br_if.default := @Itasca.code.OpVisitor.on_br_if.default

@[rust_fun "itasca::code::OpVisitor::on_br_table_label"]
def code.OpVisitor.on_br_table_label.default := @Itasca.code.OpVisitor.on_br_table_label.default

@[rust_fun "itasca::code::OpVisitor::on_br_table"]
def code.OpVisitor.on_br_table.default := @Itasca.code.OpVisitor.on_br_table.default

@[rust_fun "itasca::code::OpVisitor::on_return"]
def code.OpVisitor.on_return.default := @Itasca.code.OpVisitor.on_return.default

@[rust_fun "itasca::code::OpVisitor::on_call"]
def code.OpVisitor.on_call.default := @Itasca.code.OpVisitor.on_call.default

@[rust_fun "itasca::code::OpVisitor::on_call_indirect"]
def code.OpVisitor.on_call_indirect.default := @Itasca.code.OpVisitor.on_call_indirect.default

@[rust_fun "itasca::code::OpVisitor::on_drop"]
def code.OpVisitor.on_drop.default := @Itasca.code.OpVisitor.on_drop.default

@[rust_fun "itasca::code::OpVisitor::on_select"]
def code.OpVisitor.on_select.default := @Itasca.code.OpVisitor.on_select.default

@[rust_fun "itasca::code::OpVisitor::on_local_get"]
def code.OpVisitor.on_local_get.default := @Itasca.code.OpVisitor.on_local_get.default

@[rust_fun "itasca::code::OpVisitor::on_local_set"]
def code.OpVisitor.on_local_set.default := @Itasca.code.OpVisitor.on_local_set.default

@[rust_fun "itasca::code::OpVisitor::on_local_tee"]
def code.OpVisitor.on_local_tee.default := @Itasca.code.OpVisitor.on_local_tee.default

@[rust_fun "itasca::code::OpVisitor::on_global_get"]
def code.OpVisitor.on_global_get.default := @Itasca.code.OpVisitor.on_global_get.default

@[rust_fun "itasca::code::OpVisitor::on_global_set"]
def code.OpVisitor.on_global_set.default := @Itasca.code.OpVisitor.on_global_set.default

@[rust_fun "itasca::code::OpVisitor::on_memory_size"]
def code.OpVisitor.on_memory_size.default := @Itasca.code.OpVisitor.on_memory_size.default

@[rust_fun "itasca::code::OpVisitor::on_memory_grow"]
def code.OpVisitor.on_memory_grow.default := @Itasca.code.OpVisitor.on_memory_grow.default

@[rust_fun "itasca::code::OpVisitor::on_i32_const"]
def code.OpVisitor.on_i32_const.default := @Itasca.code.OpVisitor.on_i32_const.default

@[rust_fun "itasca::code::OpVisitor::on_i64_const"]
def code.OpVisitor.on_i64_const.default := @Itasca.code.OpVisitor.on_i64_const.default

@[rust_fun "itasca::code::OpVisitor::on_f32_const"]
def code.OpVisitor.on_f32_const.default := @Itasca.code.OpVisitor.on_f32_const.default

@[rust_fun "itasca::code::OpVisitor::on_f64_const"]
def code.OpVisitor.on_f64_const.default := @Itasca.code.OpVisitor.on_f64_const.default

@[rust_fun "itasca::module::{itasca::module::Env}::new"]
def module.Env.new := @Itasca.module.Env.new

@[rust_fun "itasca::stream::validate_streaming"]
def stream.validate_streaming := @Itasca.stream.validate_streaming

@[rust_fun "itasca::stream::{itasca::stream::CodeBatch<'_0>}::len"]
def stream.CodeBatch.len := @Itasca.stream.CodeBatch.len

@[rust_fun "itasca::stream::{itasca::stream::CodeBatch<'_0>}::validate_func"]
def stream.CodeBatch.validate_func := @Itasca.stream.CodeBatch.validate_func

@[rust_fun "itasca::stream::{itasca::stream::CodeBatch<'_0>}::next_entry"]
def stream.CodeBatch.next_entry := @Itasca.stream.CodeBatch.next_entry

@[rust_fun "itasca::stream::{itasca::stream::CodeBatch<'_0>}::code_offset"]
def stream.CodeBatch.code_offset := @Itasca.stream.CodeBatch.impl.code_offset
end Exec

namespace Exec.Primitive
/-- Count the set bits in the low `width` bits of a natural number. -/
def countBits : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, value => value % 2 + countBits width (value / 2)

/-- Count the zero low bits, returning `width` for an all-zero word. -/
def trailingZeros : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, value => if value % 2 = 0 then 1 + trailingZeros width (value / 2) else 0

theorem countBits_le (width value : Nat) : countBits width value ≤ width := by
  induction width generalizing value with
  | zero => simp [countBits]
  | succ width ih =>
    simp only [countBits]
    have := ih (value / 2)
    have := Nat.mod_lt value (by decide : 0 < 2)
    omega

theorem trailingZeros_le (width value : Nat) : trailingZeros width value ≤ width := by
  induction width generalizing value with
  | zero => simp [trailingZeros]
  | succ width ih =>
    simp only [trailingZeros]
    split
    · have := ih (value / 2); omega
    · omega
end Exec.Primitive

@[rust_fun "core::num::{u32}::count_ones"]
def core.num.U32.count_ones (x : U32) : Result U32 :=
  .ok ⟨BitVec.ofNat 32 (Exec.Primitive.countBits 32 x.val)⟩
@[rust_fun "core::num::{u64}::count_ones"]
def core.num.U64.count_ones (x : U64) : Result U32 :=
  .ok ⟨BitVec.ofNat 32 (Exec.Primitive.countBits 64 x.val)⟩
@[rust_fun "core::num::{u32}::trailing_zeros"]
def core.num.U32.trailing_zeros (x : U32) : Result U32 :=
  .ok ⟨BitVec.ofNat 32 (Exec.Primitive.trailingZeros 32 x.val)⟩
@[rust_fun "core::num::{u64}::trailing_zeros"]
def core.num.U64.trailing_zeros (x : U64) : Result U32 :=
  .ok ⟨BitVec.ofNat 32 (Exec.Primitive.trailingZeros 64 x.val)⟩

example : core.num.U64.count_ones 18446744073709551615#u64 = .ok 64#u32 := by rfl
example : core.num.U32.trailing_zeros 0#u32 = .ok 32#u32 := by rfl
example : core.num.U64.trailing_zeros 9223372036854775808#u64 = .ok 63#u32 := by rfl
