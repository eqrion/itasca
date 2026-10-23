import Exec.Interp.StructuredMachine.StructuredCallUniform
import Exec.Interp.StructuredMachine.Execution
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem step_call_execution_uniform {M P F A : Type} {emission : FunctionEmission} {supported owned}
    (semantics : CallSemantics supported owned)
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (caller : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (index : U32) (after : List instr)
    (compiledFunctions : CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store)
    (last : frameIndex.val+1 = exec.frames.length) (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some caller)
    (hc : caller.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .CALL (.mk_uN index.val)::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩
    (∃ address function host offset, compiled.code.val[raw.pc.val]? = some (.Call index offset) ∧
      caller.funcs.val[index.val]? = some address ∧ store.funcs.val[address.index.val]? = some function ∧ function.code = .Host host) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧
      (out.1 = .Ok () → ∃ pc source,
        Execution emission supported view code store out.2.1 source expected pc false ∧
        ConcreteSim compiled.code.length raw.pc.val pc false false initial source ∧
        UniformConcreteSim raw.pc.val pc false false initial source [] ∧
        (∀ bounds, owned bounds initial → owned bounds source) ∧ source.ambient = ambient ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound source)) ∧
      (∀ error, out.1 = .Err error → SourceDirectCallCause allocator hooks exec store platform frameIndex raw caller compiled initial error) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]; exact hf
  have binding := (machine.stack.top raw top).binding
  rcases step_call_structured_uniform semantics memory hooks floats allocator allocation interrupts view code exec store platform frameIndex raw caller compiled
    C targets next output (Store.decodeStore view code store) ambient f rest index after rfl compiledFunctions functionTyping last hf hi hc
    machine.typed.typed machine.core binding slots program point machine.stack with host | operation
  · exact Or.inl host
  · apply Or.inr
    apply WP.spec_mono operation
    intro out effect
    refine ⟨effect.1,?_,effect.2.2⟩
    intro success
    obtain ⟨pc,frames,top,stack,typed,covered,simulation,uniform,ready,result,owned,bounded⟩ := effect.2.1 success
    obtain ⟨current,cursor⟩ := ready.cursor
    have same : current = pc.val := by
      cases frames with
      | nil =>
        cases stack with
        | empty empty => simp [empty] at top
      | cons frame rest =>
        have actual := cursor.pc
        have eq := congrArg (Option.map (fun value : U32 => value.val)) top
        simp only [Option.map_map,Option.map_some,Function.comp_def] at eq
        rw [actual] at eq
        exact Option.some.inj eq
    subst current
    exact ⟨pc.val,_,⟨rfl,⟨typed,machine.typed.contents⟩,covered,result expected machine.result,stack,cursor⟩,simulation,uniform,owned,rfl,bounded⟩
end Exec.Interp.StructuredMachine
