import Exec.Code.Module.InitializerOffsetAvailable
import Exec.Code.Local.Capacity.AuxiliaryAvailability

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Element-segment bytecode emission accepts from source offset typing and a
conservative five-instruction demand. Source indices have independent u32 bounds. -/
theorem initializer_emit_element_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.module.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (typed : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val)
    (capacity : function.code.length + 5 ≤ Usize.max) (request : function.code.length + 5 ≤ bound)
    (indexBound : index.val ≤ U32.max) (lengthBound : segment.init.length ≤ U32.max)
    (pairIndex : function.indirect.length ≤ U32.max)
    (pairCapacity : function.indirect.length < Usize.max)
    (pairReserve : function.indirect.length + 1 ≤ bound) :
    runtime.compiler.initialize.emit_element ops module budget function index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val ≤ budget.instructions.val + 5 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.code.length ≤ function.code.length + 5 ∧
      out.2.2.v128_pool = function.v128_pool ∧ out.2.2.indirect.length ≤ function.indirect.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.emit_element
  simp only [runtime.compiler.ExecutableModule.env,Exec.module.Module.env,Itasca.module.Module.impl.env,
    Exec.module.Env.elements,Itasca.module.Env.impl.elements,bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using lookup),bind_ok]
  cases mode : segment.mode with
  | Passive =>
    simp only [mode,WP.spec_ok]
    exact ⟨trivial,by omega,by trivial,by omega,by trivial,by omega⟩
  | Declarative =>
    simp only [mode]
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with initializer_emit_available ops bound available budget function.code (.ElemDrop word)
      (by omega) (by omega) (by omega)
      as ⟨status,charged,code,accepted,used,limits,appended⟩
    refine ⟨accepted,by omega,limits,?_,?_⟩
    · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
      omega
    · omega
  | Active table offset =>
    simp only [mode]
    step with initializer_offset_available ops bound available budget {function with slot_count := 3#u32}
      module.module.env offset (typed table offset mode) (by omega)
      (by change function.code.length < Usize.max; omega)
      (by change function.code.length+1 ≤ bound; omega)
      as ⟨status,b1,first,accepted,used1,limits1,fields,instruction,code1,constant⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have firstLength : first.code.length = function.code.length + 1 := by
      simp only [alloc.vec.Vec.length,code1,List.length_append,List.length_singleton]
    step with initializer_emit_available ops bound available b1 first.code (.Const32 1#u32 0#u32)
      (by rw [limits1]; omega) (by omega) (by omega)
      as ⟨status,b2,second,accepted,used2,limits2,code2⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available (alloc.vec.Vec.len segment.init) lengthBound
      as ⟨status,length,accepted,encodedLength⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have secondLength : second.length = function.code.length + 2 := by
      simp only [alloc.vec.Vec.length,code2,List.length_append,List.length_singleton] at firstLength ⊢
      omega
    step with initializer_emit_available ops bound available b2 second (.Const32 2#u32 length)
      (by rw [limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b3,third,accepted,used3,limits3,code3⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have firstPairs : first.indirect = function.indirect := congrArg (fun value => value.indirect) fields
    step with bounded_index_available (alloc.vec.Vec.len first.indirect) (by simpa [firstPairs] using pairIndex)
      as ⟨status,entry,accepted,entryEq⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have thirdLength : third.length = function.code.length + 3 := by
      simp only [alloc.vec.Vec.length,code3,List.length_append,List.length_singleton] at secondLength ⊢
      omega
    step with budget_push_available ops bound available b3 first.indirect (word,table)
      (by simpa [firstPairs] using pairCapacity) (by simpa [firstPairs] using pairReserve)
      as ⟨status,pairBudget,pairs,accepted,sameBudget,appendedPairs⟩
    subst status pairBudget
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with initializer_emit_available ops bound available b3 third (.TableInit 0#u32 entry)
      (by rw [limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b4,fourth,accepted,used4,limits4,code4⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have fourthLength : fourth.length = function.code.length + 4 := by
      simp only [alloc.vec.Vec.length,code4,List.length_append,List.length_singleton] at thirdLength ⊢
      omega
    step with initializer_emit_available ops bound available b4 fourth (.ElemDrop word)
      (by rw [limits4,limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b5,fifth,accepted,used5,limits5,code5⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    refine ⟨trivial,?_,?_,?_,?_,?_⟩
    · omega
    · exact limits5.trans (limits4.trans (limits3.trans (limits2.trans limits1)))
    · simp only [alloc.vec.Vec.length,code5,List.length_append,List.length_singleton]
      simp only [alloc.vec.Vec.length] at fourthLength capacity
      omega
    · exact congrArg (fun value => value.v128_pool) fields
    · simp only [alloc.vec.Vec.length,appendedPairs,List.length_append,List.length_singleton]
      simp [firstPairs]

end Exec.Code
