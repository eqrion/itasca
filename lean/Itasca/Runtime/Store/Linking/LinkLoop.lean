import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Linking.LinkedOwners

/-!
Sections, each formerly its own module: LinkErrors, ExternalMaps, LinkLoop.
-/

/-! ## LinkErrors -/

section

/-!
Linking error classification and exclusion of resource errors. These results are consumed by instance preparation without executing module code.
-/

/-! ## Link Errors -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
macro "link_error_step " h:ident : tactic => `(tactic|
  first
  | solve | (simp only [Result.ok.injEq] at $h:ident; cases $h:ident; simp_all [ErrorAllowed, PrecommitError])
  | solve | simp_all only [Result.ok.injEq, Prod.mk.injEq, ErrorAllowed, PrecommitError,
      runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok]
  | (fail_if_no_progress simp only [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok, uncurry_apply_pair] at $h:ident)
  | split at $h:ident
  | (obtain ⟨value, called, rest⟩ := normal_bind_exists _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩
        repeat' (guard_hyp secondValue : Prod _ _; rcases secondValue with ⟨firstValue, secondValue⟩))
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | split at $h:ident)

/-- Linking itself can reject only compatibility or handle ownership. Partial
indexing is excluded by normal return here, and by issued-handle invariants in
the surrounding total staging theorem. -/
theorem link_import_errors {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (external : runtime.Extern)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.link_import memory store inst index external = .ok out) :
    ErrorAllowed PrecommitError out.1 ∧ out.2.1 = store ∧ out.2.2.module = inst.module := by
  unfold runtime.store.instantiate.Store.link_import at run
  repeat' link_error_step run

end Itasca.Runtime.Store

end

/-! ## Link Error Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
theorem link_staging_errors {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (imports : Slice runtime.Extern)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed PrecommitError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop2 memory store imports status index inst = .ok out) :
    ErrorAllowed PrecommitError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop2 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop2.body,
      runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, bind_ok] at run
    split at run
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨external, read, rest⟩ := normal_bind_exists _ _ _ run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have nextAllowed := (link_import_errors memory store inst index external _ called).1
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop2 memory nextStore imports nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop2, runtime.store.instantiate.Store.prepare_instance_loop2.body,
            runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

end Itasca.Runtime.Store

end

/-! ## Link Nonresource -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
/-- Link compatibility and ownership checks allocate no execution resources. -/
def LinkFailure (error : runtime.ExecError) : Prop :=
  match error with
  | .Link _ | .WrongStore => True
  | _ => False
macro "link_nonresource_step " h:ident : tactic => `(tactic|
  first
  | solve | (simp only [Result.ok.injEq] at $h:ident; cases $h:ident; simp_all [ErrorAllowed, LinkFailure])
  | solve | simp_all only [Result.ok.injEq, Prod.mk.injEq, ErrorAllowed, LinkFailure,
      runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok]
  | (fail_if_no_progress simp only [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok, uncurry_apply_pair] at $h:ident)
  | split at $h:ident
  | (obtain ⟨value, called, rest⟩ := normal_bind_exists _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩
        repeat' (guard_hyp secondValue : Prod _ _; rcases secondValue with ⟨firstValue, secondValue⟩))
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | split at $h:ident)

/-- Linking itself can reject only compatibility or handle ownership. Partial
indexing is excluded by normal return here, and by issued-handle invariants in
the surrounding total staging theorem. -/
theorem link_import_nonresource {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (index : Usize) (external : runtime.Extern)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.link_import memory store inst index external = .ok out) :
    ErrorAllowed (LinkFailure) out.1 ∧ out.2.1 = store ∧ out.2.2.module = inst.module := by
  unfold runtime.store.instantiate.Store.link_import at run
  repeat' link_nonresource_step run

theorem link_staging_nonresource {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (imports : Slice runtime.Extern)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed LinkFailure status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop2 memory store imports status index inst = .ok out) :
    ErrorAllowed LinkFailure out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop2 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop2.body,
      runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, bind_ok] at run
    split at run
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨external, read, rest⟩ := normal_bind_exists _ _ _ run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have nextAllowed := (link_import_nonresource memory store inst index external _ called).1
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop2 memory nextStore imports nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop2, runtime.store.instantiate.Store.prepare_instance_loop2.body,
            runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

end Itasca.Runtime.Store

end

end

/-! ## ExternalMaps -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def decodeExternal : runtime.Extern → externaddr
  | .Func address => .FUNC address.index.val
  | .Table address => .TABLE address.index.val
  | .Memory address => .MEM address.index.val
  | .Global address => .GLOBAL address.index.val

def externalFunctions (externals : List runtime.Extern) : List runtime.FuncAddr :=
  externals.filterMap (fun external => match external with | .Func a => some a | _ => none)
def externalTables (externals : List runtime.Extern) : List runtime.TableAddr :=
  externals.filterMap (fun external => match external with | .Table a => some a | _ => none)
def externalMemories (externals : List runtime.Extern) : List runtime.MemoryAddr :=
  externals.filterMap (fun external => match external with | .Memory a => some a | _ => none)
def externalGlobals (externals : List runtime.Extern) : List runtime.GlobalAddr :=
  externals.filterMap (fun external => match external with | .Global a => some a | _ => none)

/-- Exact address subsequences of the caller's external list, including ownership
bits. This complements the signature-indexed import map. -/
structure ExternalMaps (externals : List runtime.Extern) (inst : runtime.store.ModuleInst) : Prop where
  funcs : inst.funcs.val = externalFunctions externals
  tables : inst.tables.val = externalTables externals
  memories : inst.memories.val = externalMemories externals
  globals : inst.globals.val = externalGlobals externals

theorem LinkedStep.external_maps {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {before after : runtime.store.ModuleInst} {desc external externals}
    (effect : LinkedStep view store before desc external after)
    (maps : ExternalMaps externals before) : ExternalMaps (externals ++ [external]) after := by
  cases effect <;> constructor <;>
    simp_all [externalFunctions, externalTables, externalMemories, externalGlobals,
      maps.funcs, maps.tables, maps.memories, maps.globals]

theorem external_functions (externals : List runtime.Extern) :
    fun_funcs (externals.map decodeExternal)
      ((externalFunctions externals).map (fun a => a.index.val)) := by
  induction externals with
  | nil => exact .fun_funcs_case_0
  | cons external rest ih =>
    cases external <;> simp only [List.map_cons, externalFunctions, List.filterMap_cons,
      List.map_cons,
      decodeExternal] at *
    · exact .fun_funcs_case_1 _ _ _ ih
    all_goals exact .fun_funcs_case_2 _ _ _ ih

theorem external_globals (externals : List runtime.Extern) :
    fun_globals (externals.map decodeExternal)
      ((externalGlobals externals).map (fun a => a.index.val)) := by
  induction externals with
  | nil => exact .fun_globals_case_0
  | cons external rest ih =>
    cases external <;> simp only [List.map_cons, externalGlobals, List.filterMap_cons,
      List.map_cons,
      decodeExternal] at *
    all_goals first
      | exact .fun_globals_case_1 _ _ _ ih
      | exact .fun_globals_case_2 _ _ _ ih

theorem external_tables (externals : List runtime.Extern) :
    fun_tables (externals.map decodeExternal)
      ((externalTables externals).map (fun a => a.index.val)) := by
  induction externals with
  | nil => exact .fun_tables_case_0
  | cons external rest ih =>
    cases external <;> simp only [List.map_cons, externalTables, List.filterMap_cons,
      List.map_cons,
      decodeExternal] at *
    all_goals first
      | exact .fun_tables_case_1 _ _ _ ih
      | exact .fun_tables_case_2 _ _ _ ih

theorem external_memories (externals : List runtime.Extern) :
    fun_mems (externals.map decodeExternal)
      ((externalMemories externals).map (fun a => a.index.val)) := by
  induction externals with
  | nil => exact .fun_mems_case_0
  | cons external rest ih =>
    cases external <;> simp only [List.map_cons, externalMemories, List.filterMap_cons,
      List.map_cons,
      decodeExternal] at *
    all_goals first
      | exact .fun_mems_case_1 _ _ _ ih
      | exact .fun_mems_case_2 _ _ _ ih
end Itasca.Runtime.Store

end

/-! ## LinkLoop -/

section

/-!
Import linking loop and its external-map certificate. These results are consumed by instance preparation without executing module code.
-/

/-! ## Link External Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The actual complete import loop preserves the store, terminates normally,
and constructs the typed per-index-space maps on successful linking. -/
theorem link_external_maps_loop {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (shape : Shape view store)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (lengths : imports.length = module.module.env.imports.length)
    (handles : ∀ external ∈ imports.val, ExternalIssued store external)
    {tables memories} (cache : Cache module.module.env tables memories)
    (inst : runtime.store.ModuleInst) (start : Usize) (startBound : start.val ≤ imports.length)
    (maps : LinkedMaps view store module (module.module.env.imports.val.take start.val) inst)
    (externals : ExternalMaps (imports.val.take start.val) inst) :
    runtime.store.instantiate.Store.prepare_instance_loop2 memory store imports (.Ok ()) start inst
      ⦃ out => out.1 = store ∧ out.2.2.module = module ∧
        (out.2.1 = .Ok () → LinkedMaps view store module module.module.env.imports.val out.2.2 ∧
          ExternalMaps imports.val out.2.2) ⦄ := by
  have hostSize : imports.length = imports.val.length := rfl
  have sourceSize : module.module.env.imports.length = module.module.env.imports.val.length := rfl
  unfold runtime.store.instantiate.Store.prepare_instance_loop2
  apply loop.spec_decr_nat (fun state => imports.length - state.2.2.1.val)
    (fun state => state.1 = store ∧ state.2.2.2.module = module ∧ state.2.2.1.val ≤ imports.length ∧
      (state.2.1 = .Ok () → LinkedMaps view store module
        (module.module.env.imports.val.take state.2.2.1.val) state.2.2.2 ∧
        ExternalMaps (imports.val.take state.2.2.1.val) state.2.2.2))
  · rintro ⟨current, status, index, currentInst⟩ ⟨sameStore, source, indexBound, mapping⟩
    dsimp only at sameStore source indexBound mapping ⊢
    subst current
    unfold runtime.store.instantiate.Store.prepare_instance_loop2.body
    dsimp only
    split
    · rename_i more
      have within : index.val < imports.length := by simpa using more
      cases status with
      | Err error => simp [core.result.Result.is_ok, source]
      | Ok value =>
        cases value
        obtain ⟨currentMaps, currentExternals⟩ := mapping rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨external, externalRead⟩
        have sourceBound : index.val < module.module.env.imports.val.length := by omega
        have importBound : index.val < currentInst.module.module.env.imports.length := by rw [source]; omega
        have typed : ∀ idx, currentInst.module.module.env.imports.val[index.val].desc = .Func idx →
            idx.val < currentInst.module.module.env.types.length := by
          intro idx desc
          simp only [source] at desc ⊢
          apply cache.import_indices idx
          exact List.mem_filterMap.mpr ⟨module.module.env.imports.val[index.val],
            List.getElem_mem (by omega), by simp [desc]⟩
        have issued : ExternalIssued store external := handles external (by rw [externalRead]; exact List.getElem_mem within)
        have mapLengths := currentMaps.lengths
        have prefixLen : (module.module.env.imports.val.take index.val).length = index.val := by simp; omega
        rw [prefixLen] at mapLengths
        have hostMax := imports.property
        have room : match currentInst.module.module.env.imports.val[index.val].desc with
            | .Func _ => currentInst.funcs.length < Usize.max
            | .Table _ => currentInst.tables.length < Usize.max
            | .Memory _ => currentInst.memories.length < Usize.max
            | .Global _ => currentInst.globals.length < Usize.max := by
          split <;> omega
        step with link_import_effect memory view laws store shape currentInst index external importBound typed issued room
          as ⟨status, after, nextInst, unchanged, effect⟩
        subst after
        step as ⟨next, increment⟩
        have nextSource : nextInst.module = module := by
          rcases effect with ⟨error, status, rfl⟩ | ⟨ok, linked⟩
          · exact source
          · exact linked.source.trans source
        refine ⟨nextSource, ?_, ?_, ?_⟩
        · omega
        · intro success
          rcases effect with ⟨error, status, rfl⟩ | ⟨ok, linked⟩
          · simp [status] at success
          · have extended := linked.maps currentMaps
            have externalExtended := linked.external_maps currentExternals
            have eq : currentInst.module.module.env.imports.val[index.val] =
                module.module.env.imports.val[index.val] := by simp only [source]
            constructor
            · rw [increment, List.take_succ_eq_append_getElem sourceBound]
              simpa only [eq] using extended
            · rw [increment, List.take_succ_eq_append_getElem within]
              simpa only [externalRead] using externalExtended
        · omega
    · rename_i stopped
      have atEnd : index.val = imports.length := by simp at stopped; omega
      simp only [WP.spec_ok]
      refine ⟨True.intro, source, ?_⟩
      intro success
      have finalMaps := mapping success
      constructor
      · simpa only [atEnd, lengths, List.take_length] using finalMaps.1
      · simpa only [atEnd, hostSize, List.take_length] using finalMaps.2
  · exact ⟨rfl, maps.source, startBound, fun _ => ⟨maps, externals⟩⟩


end Itasca.Runtime.Store

end

/-! ## Link Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The actual complete import loop preserves the store, terminates normally,
and constructs the typed per-index-space maps on successful linking. -/
theorem link_imports_loop {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (shape : Shape view store)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (lengths : imports.length = module.module.env.imports.length)
    (handles : ∀ external ∈ imports.val, ExternalIssued store external)
    {tables memories} (cache : Cache module.module.env tables memories)
    (inst : runtime.store.ModuleInst) (start : Usize) (startBound : start.val ≤ imports.length)
    (maps : LinkedMaps view store module (module.module.env.imports.val.take start.val) inst) :
    runtime.store.instantiate.Store.prepare_instance_loop2 memory store imports (.Ok ()) start inst
      ⦃ out => out.1 = store ∧ out.2.2.module = module ∧
        (out.2.1 = .Ok () → LinkedMaps view store module module.module.env.imports.val out.2.2) ⦄ := by
  have hostSize : imports.length = imports.val.length := rfl
  have sourceSize : module.module.env.imports.length = module.module.env.imports.val.length := rfl
  unfold runtime.store.instantiate.Store.prepare_instance_loop2
  apply loop.spec_decr_nat (fun state => imports.length - state.2.2.1.val)
    (fun state => state.1 = store ∧ state.2.2.2.module = module ∧ state.2.2.1.val ≤ imports.length ∧
      (state.2.1 = .Ok () → LinkedMaps view store module
        (module.module.env.imports.val.take state.2.2.1.val) state.2.2.2))
  · rintro ⟨current, status, index, currentInst⟩ ⟨sameStore, source, indexBound, mapping⟩
    dsimp only at sameStore source indexBound mapping ⊢
    subst current
    unfold runtime.store.instantiate.Store.prepare_instance_loop2.body
    dsimp only
    split
    · rename_i more
      have within : index.val < imports.length := by simpa using more
      cases status with
      | Err error => simp [core.result.Result.is_ok, source]
      | Ok value =>
        cases value
        have currentMaps := mapping rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨external, externalRead⟩
        have sourceBound : index.val < module.module.env.imports.val.length := by omega
        have importBound : index.val < currentInst.module.module.env.imports.length := by rw [source]; omega
        have typed : ∀ idx, currentInst.module.module.env.imports.val[index.val].desc = .Func idx →
            idx.val < currentInst.module.module.env.types.length := by
          intro idx desc
          simp only [source] at desc ⊢
          apply cache.import_indices idx
          exact List.mem_filterMap.mpr ⟨module.module.env.imports.val[index.val],
            List.getElem_mem (by omega), by simp [desc]⟩
        have issued : ExternalIssued store external := handles external (by rw [externalRead]; exact List.getElem_mem within)
        have mapLengths := currentMaps.lengths
        have prefixLen : (module.module.env.imports.val.take index.val).length = index.val := by simp; omega
        rw [prefixLen] at mapLengths
        have hostMax := imports.property
        have room : match currentInst.module.module.env.imports.val[index.val].desc with
            | .Func _ => currentInst.funcs.length < Usize.max
            | .Table _ => currentInst.tables.length < Usize.max
            | .Memory _ => currentInst.memories.length < Usize.max
            | .Global _ => currentInst.globals.length < Usize.max := by
          split <;> omega
        step with link_import_effect memory view laws store shape currentInst index external importBound typed issued room
          as ⟨status, after, nextInst, unchanged, effect⟩
        subst after
        step as ⟨next, increment⟩
        have nextSource : nextInst.module = module := by
          rcases effect with ⟨error, status, rfl⟩ | ⟨ok, linked⟩
          · exact source
          · exact linked.source.trans source
        refine ⟨nextSource, ?_, ?_, ?_⟩
        · omega
        · intro success
          rcases effect with ⟨error, status, rfl⟩ | ⟨ok, linked⟩
          · simp [status] at success
          · have extended := linked.maps currentMaps
            have eq : currentInst.module.module.env.imports.val[index.val] =
                module.module.env.imports.val[index.val] := by simp only [source]
            rw [increment, List.take_succ_eq_append_getElem sourceBound]
            simpa only [eq] using extended
        · omega
    · rename_i stopped
      have atEnd : index.val = imports.length := by simp at stopped; omega
      simp only [WP.spec_ok]
      refine ⟨True.intro, source, ?_⟩
      intro success
      have finalMaps := mapping success
      simpa only [atEnd, lengths, List.take_length] using finalMaps
  · exact ⟨rfl, maps.source, startBound, fun _ => maps⟩

/-- Allocation of the four initially empty import maps cannot invalidate this
seed: AllocCorrect preserves their contents whether reservation succeeds or
fails. -/
theorem linked_maps_empty {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (types : inst.types.val = [])
    (funcs : inst.funcs.val = []) (tables : inst.tables.val = [])
    (memories : inst.memories.val = []) (globals : inst.globals.val = [])
    (elements : inst.elems.val = []) (data : inst.datas.val = []) :
    LinkedMaps view store inst.module [] inst := by
  constructor <;> simp [*, importedFuncs, importedTables, importedMems, importedGlobals]

end Itasca.Runtime.Store

end

end
