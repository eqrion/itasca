import Itasca.Profile.State

open Aeneas Aeneas.Std

namespace Itasca

/-! Compatibility names for the existing multi-value invariant. Both names
reduce to the shared profile-parametric runtime loop. -/

abbrev code.validate_multi_value_body_with_loop.body {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (type_defs : alloc.vec.Vec types.FuncType)
    (imports : alloc.vec.Vec module.Import) (globals : alloc.vec.Vec module.Global)
    (exports : alloc.vec.Vec module.Export) (elements : alloc.vec.Vec module.Element)
    (start : Option U32) (func_type_indices : alloc.vec.Vec U32)
    (func_types : alloc.vec.Vec types.FuncType) (table_types : alloc.vec.Vec types.TableType)
    (mem_types : alloc.vec.Vec types.MemType) (global_types : alloc.vec.Vec types.GlobalType)
    (num_imported_funcs num_imported_globals : Usize) (ctx : code.Context) (index : U32)
    (v : V) (st : code.BodyState) :=
  code.body_loop_loop.body visitor data
    ⟨type_defs, imports, globals, exports, elements, start, func_type_indices, func_types,
      table_types, mem_types, global_types, num_imported_funcs, num_imported_globals⟩
    ctx index .MultiValue v st

abbrev code.validate_multi_value_body_with_loop {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (type_defs : alloc.vec.Vec types.FuncType)
    (imports : alloc.vec.Vec module.Import) (globals : alloc.vec.Vec module.Global)
    (exports : alloc.vec.Vec module.Export) (elements : alloc.vec.Vec module.Element)
    (start : Option U32) (func_type_indices : alloc.vec.Vec U32)
    (func_types : alloc.vec.Vec types.FuncType) (table_types : alloc.vec.Vec types.TableType)
    (mem_types : alloc.vec.Vec types.MemType) (global_types : alloc.vec.Vec types.GlobalType)
    (num_imported_funcs num_imported_globals : Usize) (ctx : code.Context) (index : U32)
    (v : V) (st : code.BodyState) :=
  code.body_loop_loop visitor data
    ⟨type_defs, imports, globals, exports, elements, start, func_type_indices, func_types,
      table_types, mem_types, global_types, num_imported_funcs, num_imported_globals⟩
    ctx index .MultiValue v st

end Itasca
