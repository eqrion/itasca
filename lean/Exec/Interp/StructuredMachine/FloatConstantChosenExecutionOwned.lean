import Exec.Interp.StructuredMachine.FloatConstantChosenStep
import Exec.Interp.Relations.ChosenControlSource
import Exec.Interp.StructuredMachine.SupportedControlSemantics
import Exec.Interp.Machines.Core.CoreOwnership
import Exec.Abs.Core.Bound
import Exec.Interp.StructuredMachine.FloatConstantChosenBounded
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Spec.Extend
namespace Exec.Interp.StructuredMachine.FloatConstant
variable {choices : Spec.SourceChoices} (occurrence : Nat)
include occurrence
open Aeneas Aeneas.Std SpecExt Exec.Spec
theorem step_float32_execution_owned_forward_chosen {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame), raw.pc.val < pc.val ∧
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = index.val := by change exec.frames.length-1 = index.val; omega
    rw [position]
    exact frameFound
  obtain ⟨boundInst,fn,boundCompiled,signature,owner,member,found,issued,wasm,lookup,signatureFound,moduleEq,resultEq,localsEq,allocated⟩ :=
    (machine.stack.top raw top).binding
  have instEq : boundInst = inst := by rw [instanceFound] at found; exact Option.some.inj found.symm
  subst boundInst
  have compiledEq : boundCompiled = compiled := by rw [codeFound] at lookup; exact Option.some.inj lookup.symm
  subst boundCompiled
  apply WP.spec_mono (step_float32_core_bounded_forward_chosen occurrence memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest value after last frameFound instanceFound codeFound program.fetchBound slots program.checked allocated point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,forward,fields,represented,retained,fresh,metadata,shape,simulation,footprint⟩ := effect
  have covered : Abs.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | changed
    · rw [same]; exact machine.core
    · apply StructuredMachine.core_step_supported machine.typed machine.core
      rw [changed]
      rfl
  have ownership : ∀ bounds, Abs.Ownership.StatefulOwned bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ →
      Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply StructuredMachine.owned_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have bounded : ∀ bounds, Abs.CodeBound bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ →
      Abs.CodeBound bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply StructuredMachine.bound_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
    rcases footprint with same | ⟨position,word,above,bound,changed⟩
    · rw [same]; exact .refl _ _
    · rw [changed]; exact .set _ _ _ _ above
  exact ⟨success,sameStore,samePlatform,pc,g,forward,
    Execution.ordinary view code ambient {f with code := .CONST .F32 (.mk_num__1 .F32 value)::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,ownership,bounded⟩

theorem step_float32_execution_owned_chosen {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  apply WP.spec_mono (step_float32_execution_owned_forward_chosen occurrence memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest value after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,sameStore,samePlatform,pc,g,forward,rest⟩
  exact ⟨success,sameStore,samePlatform,pc,g,rest⟩

theorem step_float64_execution_owned_forward_chosen {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame), raw.pc.val < pc.val ∧
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = index.val := by change exec.frames.length-1 = index.val; omega
    rw [position]
    exact frameFound
  obtain ⟨boundInst,fn,boundCompiled,signature,owner,member,found,issued,wasm,lookup,signatureFound,moduleEq,resultEq,localsEq,allocated⟩ :=
    (machine.stack.top raw top).binding
  have instEq : boundInst = inst := by rw [instanceFound] at found; exact Option.some.inj found.symm
  subst boundInst
  have compiledEq : boundCompiled = compiled := by rw [codeFound] at lookup; exact Option.some.inj lookup.symm
  subst boundCompiled
  apply WP.spec_mono (step_float64_core_bounded_forward_chosen occurrence memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest value after last frameFound instanceFound codeFound program.fetchBound slots program.checked allocated point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,forward,fields,represented,retained,fresh,metadata,shape,simulation,footprint⟩ := effect
  have covered : Abs.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | changed
    · rw [same]; exact machine.core
    · apply StructuredMachine.core_step_supported machine.typed machine.core
      rw [changed]
      rfl
  have ownership : ∀ bounds, Abs.Ownership.StatefulOwned bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ →
      Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply StructuredMachine.owned_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have bounded : ∀ bounds, Abs.CodeBound bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ →
      Abs.CodeBound bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply StructuredMachine.bound_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
    rcases footprint with same | ⟨position,word,above,bound,changed⟩
    · rw [same]; exact .refl _ _
    · rw [changed]; exact .set _ _ _ _ above
  exact ⟨success,sameStore,samePlatform,pc,g,forward,
    Execution.ordinary view code ambient {f with code := .CONST .F64 (.mk_num__1 .F64 value)::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,ownership,bounded⟩

theorem step_float64_execution_owned_chosen {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  apply WP.spec_mono (step_float64_execution_owned_forward_chosen occurrence memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest value after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,sameStore,samePlatform,pc,g,forward,rest⟩
  exact ⟨success,sameStore,samePlatform,pc,g,rest⟩

end Exec.Interp.StructuredMachine.FloatConstant
