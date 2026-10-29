import Itasca.Runtime.Interp.Machine.Simd.FrameStep
import Itasca.Runtime.Interp.Machine.Control.JumpExecution

/-!
All supported SIMD instructions execute inside the generic compiled stack. The only trap is a checked memory bounds failure; opaque buffer writeback is retained explicitly even when the source store does not change.

Main declarations: `step_execution_forward` and `step_execution`. A direct consumer is `Integration.Execution.Dispatch.Simd`.
-/

namespace Itasca.Runtime.Interp.StructuredMachine.Simd
open Aeneas Aeneas.Std

/-- All supported SIMD instructions execute inside the generic compiled stack.
The only trap is a checked memory bounds failure; opaque buffer writeback is
retained explicitly even when the source store does not change. -/
theorem step_execution_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (source : instr) (after : List instr) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=source::after} compiled C targets next output)
    (simd : Abs.SimdInstr source)
    (project : ∀ before emitted result, Interp.emission compiled C before source emitted result →
      Code.SimdEmission compiled.simd.val compiled.v128_pool.val C before source emitted result)
    (machine : Execution view interpretation store exec
      ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧ FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view interpretation store) (Store.decodeStore view interpretation out.2.2.1) ∧
      ((out.1=.Ok () ∧ ∃ (pc : U32) (updated : Abs.AFrame), raw.pc.val < pc.val ∧
        Execution view interpretation out.2.2.1 out.2.1
          ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩ ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial →
          Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial →
          Abs.CodeBound bound ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .MemoryOutOfBounds) ∧
        Store.decodeStore view interpretation out.2.2.1=Store.decodeStore view interpretation store ∧
        ∃ n, 0<n ∧ Spec.StepsHN n (Abs.decode initial) []
          ⟨⟨Store.decodeStore view interpretation out.2.2.1,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast?=some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1=index.val := by change exec.frames.length-1=index.val; omega
    rw [position]
    exact hf
  obtain ⟨boundInst,fn,boundCompiled,signature,owner,member,found,issued,wasm,lookup,signatureFound,moduleEq,resultEq,localsEq,allocated⟩ :=
    (machine.stack.top raw top).binding
  have instEq : boundInst=inst := Option.some.inj (found.symm.trans hi)
  subst boundInst
  have compiledEq : boundCompiled=compiled := Option.some.inj (lookup.symm.trans hc)
  subst boundCompiled
  rcases frame_point_step memory hooks floats allocator view interpretation memoryLaws floatLaws exec store platform
    raw index inst compiled C targets next output ambient f rest source after last hf hi hc moduleEq program allocated
    machine.typed slots point simd project with jump | operation
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (step_forward_jump memory hooks floats allocator view interpretation exec store platform index raw
      inst compiled ambient {f with code:=source::after} rest expected C targets next output target last hf hi hc
      forward fetch slots retained machine program)
    rintro out ⟨ok,same,platformEq,execEq,fresh,simulation⟩
    rw [same]
    exact ⟨platformEq,Or.inl rfl,.refl store,Spec.extend_store_refl _ machine.typed.typed.store,
      Or.inl ⟨ok,target,_,forward,fresh,simulation,fun _ owned=>owned,fun _ bounded=>bounded⟩⟩
  · apply WP.spec_mono operation
    rintro out ⟨platformEq,mutation,metadata,pc,pcNext,normal | failed⟩
    · obtain ⟨ok,g,effect,preserved,represented,frameMetadata,retained,sourceStep⟩ := normal
      have fresh := machine.simd view interpretation ambient {f with code:=source::after} g rest expected raw.pc.val false
        metadata raw index pc last hf program retained represented frameMetadata effect preserved sourceStep
      exact ⟨platformEq,mutation,metadata,sourceStep.next_extension machine.typed,
        Or.inl ⟨ok,pc,g,by omega,fresh⟩⟩
    · obtain ⟨failed,execEq,decoded,sourceTrap⟩ := failed
      refine ⟨platformEq,mutation,metadata,?_,Or.inr ⟨failed,decoded,?_⟩⟩
      · rw [decoded]; exact Spec.extend_store_refl _ machine.typed.typed.store
      · rw [decoded]
        exact sourceTrap.trap_simulation machine.typed


theorem step_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (source : instr) (after : List instr) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=source::after} compiled C targets next output)
    (simd : Abs.SimdInstr source)
    (project : ∀ before emitted result, Interp.emission compiled C before source emitted result →
      Code.SimdEmission compiled.simd.val compiled.v128_pool.val C before source emitted result)
    (machine : Execution view interpretation store exec
      ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧ FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view interpretation store) (Store.decodeStore view interpretation out.2.2.1) ∧
      ((out.1=.Ok () ∧ ∃ (pc : U32) (updated : Abs.AFrame),
        Execution view interpretation out.2.2.1 out.2.1
          ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩ ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial →
          Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial →
          Abs.CodeBound bound ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .MemoryOutOfBounds) ∧
        Store.decodeStore view interpretation out.2.2.1=Store.decodeStore view interpretation store ∧
        ∃ n, 0<n ∧ Spec.StepsHN n (Abs.decode initial) []
          ⟨⟨Store.decodeStore view interpretation out.2.2.1,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_execution_forward memory hooks floats allocator view interpretation memoryLaws floatLaws exec store platform raw index inst compiled C targets next output ambient f rest source after expected last hf hi hc program slots point simd project machine)
  rintro out ⟨platformEq,mutation,metadata,extension,normal | failed⟩
  · obtain ⟨ok,pc,g,forward,fresh⟩ := normal
    exact ⟨platformEq,mutation,metadata,extension,Or.inl ⟨ok,pc,g,fresh⟩⟩
  · exact ⟨platformEq,mutation,metadata,extension,Or.inr failed⟩

end Itasca.Runtime.Interp.StructuredMachine.Simd
