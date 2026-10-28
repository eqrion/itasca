import Itasca.Runtime.Code.Module.InitializerOffsetAvailable
import Itasca.Runtime.Code.Local.Capacity.AuxiliaryAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Data-segment bytecode emission accepts from source offset typing and a
conservative five-instruction demand. Source indices have independent u32 bounds. -/
theorem initializer_emit_data_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.module.Data)
    (lookup : module.module.tail.data.val[index.val]? = some segment)
    (typed : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val)
    (capacity : function.code.length + 5 ≤ Usize.max) (request : function.code.length + 5 ≤ bound)
    (indexBound : index.val ≤ U32.max) (lengthBound : segment.init.length ≤ U32.max) :
    runtime.compiler.initialize.emit_data ops module budget function index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val ≤ budget.instructions.val + 5 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.code.length ≤ function.code.length + 5 ∧
      out.2.2.v128_pool = function.v128_pool ∧ out.2.2.indirect = function.indirect ⦄ := by
  unfold runtime.compiler.initialize.emit_data
  simp only [runtime.compiler.ExecutableModule.tail,Itasca.module.Module.impl.tail,bind_ok]
  rw [initializer_vec_index _ _ segment lookup,bind_ok]
  cases mode : segment.mode with
  | Passive =>
    simp only [mode,WP.spec_ok]
    exact ⟨trivial,by omega,by trivial,by omega,by trivial,by trivial⟩
  | Active memory offset =>
    simp only [mode]
    step with initializer_offset_available ops bound available budget {function with slot_count := 3#u32}
      module.module.env offset (typed memory offset mode) (by omega)
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
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have thirdLength : third.length = function.code.length + 3 := by
      simp only [alloc.vec.Vec.length,code3,List.length_append,List.length_singleton] at secondLength ⊢
      omega
    step with initializer_emit_available ops bound available b3 third (.MemoryInit 0#u32 word)
      (by rw [limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b4,fourth,accepted,used4,limits4,code4⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have fourthLength : fourth.length = function.code.length + 4 := by
      simp only [alloc.vec.Vec.length,code4,List.length_append,List.length_singleton] at thirdLength ⊢
      omega
    step with initializer_emit_available ops bound available b4 fourth (.DataDrop word)
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
    · exact congrArg (fun value => value.indirect) fields

end Itasca.Runtime.Code
