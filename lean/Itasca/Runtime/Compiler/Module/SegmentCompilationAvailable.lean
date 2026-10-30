import Itasca.Runtime.Compiler.Module.InitializerOffsetAvailable
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryAvailability
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentAcceptance
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentFinish

/-!
Successful data/element segment compilation from bounded segment demand. Per-segment emission and their folds establish the final segment compilation availability theorem.
-/

/-! ## Initializer Emit Data Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Data-segment bytecode emission accepts from source offset typing and a
conservative five-instruction demand. Source indices have independent u32 bounds. -/
theorem initializer_emit_data_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Data)
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
  simp only [runtime.compiler.ExecutableModule.tail,Itasca.metadata.Module.impl.tail,bind_ok]
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

end Itasca.Runtime.Compiler

end

/-! ## Initializer Emit Datas Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The full source-ordered data bytecode loop accepts with five emitted
instructions per remaining source segment as conservative
demand. Offset literals require no pool allocation. -/
theorem initializer_emit_datas_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ module.module.tail.data.val.length)
    (sourceCount : module.module.tail.data.length ≤ U32.max)
    (sourceLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeCapacity : function.code.length + 5*(module.module.tail.data.val.length-index.val) ≤ Usize.max)
    (codeReserve : function.code.length + 5*(module.module.tail.data.val.length-index.val) ≤ bound) :
    runtime.compiler.initialize.lower_loop4 ops module budget index (.Ok ()) function ⦃ out =>
      out.2.1 = .Ok () ∧ out.1.limits = budget.limits ∧
      out.1.instructions.val ≤ budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
      out.2.2.code.length ≤ function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
      out.2.2.indirect = function.indirect ∧
      out.2.2.v128_pool = function.v128_pool ⦄ := by
  unfold runtime.compiler.initialize.lower_loop4
  apply loop.spec_decr_nat (fun state => module.module.tail.data.val.length-state.2.1.val)
    (fun state => state.1.limits = budget.limits ∧ state.2.2.1 = .Ok () ∧
      state.2.1.val ≤ module.module.tail.data.val.length ∧
      state.1.instructions.val + 5*(module.module.tail.data.val.length-state.2.1.val) ≤
        budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
      state.2.2.2.code.length + 5*(module.module.tail.data.val.length-state.2.1.val) ≤
        function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
      state.2.2.2.indirect = function.indirect ∧
      state.2.2.2.v128_pool = function.v128_pool)
  · rintro ⟨charged,next,status,current⟩ ⟨limits,accepted,position,used,code,pairs,pool⟩
    dsimp only at limits accepted position used code pairs pool
    subst status
    unfold runtime.compiler.initialize.lower_loop4.body
    simp only [runtime.compiler.ExecutableModule.tail,Itasca.metadata.Module.impl.tail,bind_ok]
    split
    · rename_i more
      have sourceBound : next.val < module.module.tail.data.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.len] using more
      let segment := module.module.tail.data.val[next.val]
      have lookup : module.module.tail.data.val[next.val]? = some segment := List.getElem?_eq_getElem sourceBound
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with initializer_emit_data_available ops bound available module charged current next segment lookup
        (typed segment (List.getElem_mem sourceBound)) (by rw [limits]; omega) (by omega) (by omega)
        (by change module.module.tail.data.val.length ≤ U32.max at sourceCount; omega)
        (sourceLengths segment (List.getElem_mem sourceBound))
        as ⟨status,afterBudget,after,accepted,usedAgain,limitsAgain,codeAgain,poolAgain,pairsAgain⟩
      subst status
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      · exact limitsAgain.trans limits
      · scalar_tac
      · omega
      · omega
      · exact pairsAgain.trans pairs
      · exact poolAgain.trans pool
      · scalar_tac
    · rename_i stopped
      have last : next.val = module.module.tail.data.val.length := by
        have ended : module.module.tail.data.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.len] using stopped
        omega
      exact WP.spec.ret ⟨rfl,limits,by simpa [last] using used,by simpa [last] using code,
        pairs,pool⟩
  · exact ⟨rfl,rfl,inside,Nat.le_refl _,Nat.le_refl _,rfl,rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Initializer Emit Element Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Element-segment bytecode emission accepts from source offset typing and a
conservative five-instruction demand. Source indices have independent u32 bounds. -/
theorem initializer_emit_element_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Element)
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
  simp only [runtime.compiler.ExecutableModule.env,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements,bind_ok]
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

end Itasca.Runtime.Compiler

end

/-! ## Initializer Emit Elements Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The full source-ordered element bytecode loop accepts with five emitted
instructions and one descriptor per remaining source segment as conservative
demand. Offset literals require no pool allocation. -/
theorem initializer_emit_elements_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ module.module.env.elements.val.length)
    (sourceCount : module.module.env.elements.length ≤ U32.max)
    (sourceLengths : ∀ segment ∈ module.module.env.elements.val, segment.init.length ≤ U32.max)
    (typed : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeCapacity : function.code.length + 5*(module.module.env.elements.val.length-index.val) ≤ Usize.max)
    (codeReserve : function.code.length + 5*(module.module.env.elements.val.length-index.val) ≤ bound)
    (pairCapacity : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ Usize.max)
    (pairReserve : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ bound)
    (pairWord : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ U32.max) :
    runtime.compiler.initialize.lower_loop3 ops module budget index (.Ok ()) function ⦃ out =>
      out.2.1 = .Ok () ∧ out.1.limits = budget.limits ∧
      out.1.instructions.val ≤ budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ∧
      out.2.2.code.length ≤ function.code.length + 5*(module.module.env.elements.val.length-index.val) ∧
      out.2.2.indirect.length ≤ function.indirect.length + (module.module.env.elements.val.length-index.val) ∧
      out.2.2.v128_pool = function.v128_pool ⦄ := by
  unfold runtime.compiler.initialize.lower_loop3
  apply loop.spec_decr_nat (fun state => module.module.env.elements.val.length-state.2.1.val)
    (fun state => state.1.limits = budget.limits ∧ state.2.2.1 = .Ok () ∧
      state.2.1.val ≤ module.module.env.elements.val.length ∧
      state.1.instructions.val + 5*(module.module.env.elements.val.length-state.2.1.val) ≤
        budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ∧
      state.2.2.2.code.length + 5*(module.module.env.elements.val.length-state.2.1.val) ≤
        function.code.length + 5*(module.module.env.elements.val.length-index.val) ∧
      state.2.2.2.indirect.length + (module.module.env.elements.val.length-state.2.1.val) ≤
        function.indirect.length + (module.module.env.elements.val.length-index.val) ∧
      state.2.2.2.v128_pool = function.v128_pool)
  · rintro ⟨charged,next,status,current⟩ ⟨limits,accepted,position,used,code,pairs,pool⟩
    dsimp only at limits accepted position used code pairs pool
    subst status
    unfold runtime.compiler.initialize.lower_loop3.body
    simp only [runtime.compiler.ExecutableModule.env,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements,bind_ok]
    split
    · rename_i more
      have sourceBound : next.val < module.module.env.elements.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      let segment := module.module.env.elements.val[next.val]
      have lookup : module.module.env.elements.val[next.val]? = some segment := List.getElem?_eq_getElem sourceBound
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with initializer_emit_element_available ops bound available module charged current next segment lookup
        (typed segment (List.getElem_mem sourceBound)) (by rw [limits]; omega) (by omega) (by omega)
        (by change module.module.env.elements.val.length ≤ U32.max at sourceCount; omega)
        (sourceLengths segment (List.getElem_mem sourceBound)) (by omega) (by omega) (by omega)
        as ⟨status,afterBudget,after,accepted,usedAgain,limitsAgain,codeAgain,poolAgain,pairsAgain⟩
      subst status
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      · exact limitsAgain.trans limits
      · scalar_tac
      · omega
      · omega
      · omega
      · exact poolAgain.trans pool
      · scalar_tac
    · rename_i stopped
      have last : next.val = module.module.env.elements.val.length := by
        have ended : module.module.env.elements.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨rfl,limits,by simpa [last] using used,by simpa [last] using code,
        by simpa [last] using pairs,pool⟩
  · exact ⟨rfl,rfl,inside,Nat.le_refl _,Nat.le_refl _,Nat.le_refl _,rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## Segment Compilation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The exact extracted suffix after read-only initializer mappings. This is a
proof-only factorization of `initialize.lower`, retaining its actual error,
allocator, and publication branches. It adds no runtime API or external model. -/
def segmentCompilation {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.ExecutableModule ×
      runtime.compiler.Budget A) := do
  let function ←
    runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new
      _root_.Itasca.runtime.bytecode.Instr) 0#u32
  let (budget4, result3, function1) ←
    runtime.compiler.initialize.lower_loop3 ops module
      budget 0#usize (core.result.Result.Ok ()) function
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch result3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (budget5, result4, function2) ←
      runtime.compiler.initialize.lower_loop4 ops module
        budget4 0#usize result3 function1
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch result4
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (r, budget6, v) ←
        runtime.compiler.initialize.emit ops budget5
          function2.code (runtime.bytecode.Instr.Return 0#u32 0#u32)
      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf5 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let b ←
          runtime.bytecode.CompiledFunction.well_formed
            { function2 with code := v }
        if b
        then
          let i := alloc.vec.Vec.len module.functions
          let (r1, budget7, v1) ←
            runtime.compiler.Budget.push ops budget6
              module.functions { function2 with code := v }
          .ok (r1, { module with functions := v1, initialization := i },
            budget7)
        else
          .ok (core.result.Result.Err
            _root_.Itasca.error.VisitError.OutOfMemory, module, budget6)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        .ok (r1, module, budget6)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      .ok (r, module, budget5)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    .ok (r, module, budget4)

end Itasca.Runtime.Compiler

end

/-! ## Segment Compilation Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def segmentCompilationDemand (module : runtime.compiler.ExecutableModule) : Nat :=
  5*(module.module.env.elements.val.length+module.module.tail.data.val.length)+1

/-- Source-derived requests for the generated segment program. The existing
function vector and native per-request allocation bound are accounted separately. -/
structure SegmentCompilationDemand {A : Type} (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (bound : Nat) : Prop where
  instructions : budget.instructions.val + segmentCompilationDemand module ≤ budget.limits.max_instructions.val
  codeCapacity : segmentCompilationDemand module ≤ Usize.max
  codeReserve : segmentCompilationDemand module ≤ bound
  functionsCapacity : module.functions.length < Usize.max
  functionsReserve : module.functions.length+1 ≤ bound
  elementCount : module.module.env.elements.length ≤ U32.max
  dataCount : module.module.tail.data.length ≤ U32.max
  elementLengths : ∀ segment ∈ module.module.env.elements.val, segment.init.length ≤ U32.max
  dataLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max

/-- The complete extracted segment suffix accepts from source typing and
independent numerical demand. The program certificate and checker result are
constructed before publication, not supplied as compiler-success premises. -/
theorem segment_compilation_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (demand : SegmentCompilationDemand module budget bound)
    (elementsTyped : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (datasTyped : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32) :
    segmentCompilation ops module budget ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.module = module.module ∧ out.2.2.limits = budget.limits ∧
      out.2.2.instructions.val ≤ budget.instructions.val+segmentCompilationDemand module ⦄ := by
  let seed := {initializerSeed .I32 with slot_count := 0#u32}
  have seedEq : runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) 0#u32 = .ok seed := rfl
  have instructionRoom := demand.instructions
  have codeCapacity := demand.codeCapacity
  have codeReserve := demand.codeReserve
  simp only [segmentCompilationDemand] at instructionRoom codeCapacity codeReserve
  obtain ⟨⟨b1,status,first⟩,firstCall,accepted,limits1,used1,code1,pairs1,pool1⟩ := WP.spec_imp_exists
    (initializer_emit_elements_available ops bound available module budget seed 0#usize (by simp)
      demand.elementCount demand.elementLengths elementsTyped
      (by simpa [seed,initializerSeed] using (show budget.instructions.val+
        5*module.module.env.elements.val.length ≤ budget.limits.max_instructions.val by omega))
      (by simp [seed,initializerSeed] <;> omega) (by simp [seed,initializerSeed] <;> omega)
      (by simp [seed,initializerSeed] <;> omega) (by simp [seed,initializerSeed] <;> omega)
      (by simpa [seed,initializerSeed] using demand.elementCount))
  dsimp only at accepted limits1 used1 code1 pairs1 pool1
  subst status
  simp [seed,initializerSeed] at used1 code1 pairs1
  obtain ⟨elements,elementPrefix⟩ := element_program_loop ops law module seed seed first budget b1 0#usize []
    (.empty module seed) (by simp) elementsTyped firstCall
  obtain ⟨⟨b2,status,second⟩,secondCall,accepted,limits2,used2,code2,pairs2,pool2⟩ := WP.spec_imp_exists
    (initializer_emit_datas_available ops bound available module b1 first 0#usize (by simp)
      demand.dataCount demand.dataLengths datasTyped (by rw [limits1]; simp <;> omega)
      (by simp <;> omega) (by simp <;> omega))
  dsimp only at accepted limits2 used2 code2 pairs2 pool2
  subst status
  simp at used2 code2
  obtain ⟨datas,dataPrefix⟩ := data_program_loop ops law module first first second b1 b2 0#usize []
    (.empty module first) (by simp) datasTyped secondCall
  obtain ⟨⟨status,b3,finalCode⟩,emitCall,accepted,used3,limits3,appended⟩ := WP.spec_imp_exists
    (initializer_emit_available ops bound available b2 second.code (.Return 0#u32 0#u32)
      (by rw [limits2,limits1]; omega)
      (by change second.code.val.length < Usize.max; omega)
      (by change second.code.val.length + 1 ≤ bound; omega))
  dsimp only at accepted used3 limits3 appended
  subst status
  have program := segment_program_finish module seed first second finalCode elements datas elementPrefix dataPrefix
    appended (by simp [seed,initializerSeed]) (by simp [seed,initializerSeed]) rfl rfl rfl
  have metadata : second.body_start = 0#usize ∧ second.body_end = 0#usize ∧
      second.source_offsets.val = [] ∧ second.jump_tables.val = [] ∧ second.controls.val = [] := by
    rw [dataPrefix.fields,elementPrefix.fields]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨valid,checkCall,rfl⟩ := WP.spec_imp_exists
    (segment_program_well_formed program elementsTyped datasTyped metadata.1 metadata.2.1
      metadata.2.2.1 metadata.2.2.2.1 metadata.2.2.2.2)
  unfold segmentCompilation
  rw [seedEq,bind_ok,firstCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [secondCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [emitCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [checkCall]
  simp only [bind_ok,↓reduceIte]
  step with budget_push_available ops bound available b3 module.functions {second with code := finalCode}
    demand.functionsCapacity demand.functionsReserve
    as ⟨status,afterBudget,functions,accepted,sameBudget,appendedFunctions⟩
  refine ⟨accepted,?_,?_⟩
  · simpa [sameBudget,limits3,limits2] using limits1
  · simp only [sameBudget]
    unfold segmentCompilationDemand
    omega

end Itasca.Runtime.Compiler

end
