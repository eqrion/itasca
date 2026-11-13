import Itasca.Runtime.Interp.Machine.Normalization.IndexedEmpty
import Itasca.Runtime.Interp.Machine.Frames.FrameStack
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunction
import Itasca.Runtime.Interp.Relations.SyntheticInitializerCauses
import Itasca.Runtime.Interp.Machine.Frames.ReturnStack
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.SourceMachine.DecodeDepth

/-!
Sections, each formerly its own module: FunctionEnd, ReturnCompletion, EpilogueExecution, ReturnPoint, StructuredReturn, ReturnExecution, Finished, FrameStorePrefix, FrameDepth.
-/

/-! ## FunctionEnd -/

section

/-!
An empty outer source continuation either skips forward administratively or fetches the compiler's exact final Return. Root alignment rules out falling past the bytecode vector.

Main declarations: `function_end`. A direct consumer is `Interp.Machine.Frames.EpilogueExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- An empty outer source continuation either skips forward administratively
or fetches the compiler's exact final Return. Root alignment rules out falling
past the bytecode vector. -/
theorem function_end {M : Type} {store : runtime.store.Store M}
    {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context} {s : _root_.store} {targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw { source with code := [], labels := [] }
      compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint s { raw with pc := target } { source with code := [], labels := [] }
        compiled C targets next output) ∨
    (∃ count : U32, compiled.code.val[raw.pc.val]? = some (.Return compiled.local_slots count) ∧
      compiled.local_slots.val = Compiler.slots (source.locals.map Compiler.valueType) ∧
      count.val = Compiler.slots source.resultTypes ∧ raw.pc.val < U32.max) := by
  have noTargets : targets = [] := by
    have empty : targets.length = 0 := point.labels.length.symm
    cases targets with
    | nil => rfl
    | cons head tail => simp at empty
  rcases structured_code_empty_inv point.code.current with skip | done
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched,
      point.bindings,point.locals,point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨position, _⟩ := done
    obtain ⟨endpoint, _, src, count, width, rootFetched⟩ := point.code.root noTargets
    obtain ⟨epilogue, actualCount, finalPosition, fetched⟩ := program.epilogue
    have same : raw.pc.val = epilogue.val := by omega
    have endpointSame : next = epilogue.val := by omega
    rw [endpointSame, fetched] at rootFetched
    have counts : actualCount = count := by
      have equal := Option.some.inj rootFetched
      simp only [runtime.bytecode.Instr.Return.injEq] at equal
      exact equal.2
    have actual : compiled.code.val[raw.pc.val]? = some (.Return compiled.local_slots actualCount) := by
      rw [same]; exact fetched
    exact Or.inr ⟨actualCount, actual, program.localSlots, by rw [counts]; exact width,
      program.fetched_bound _ actual⟩

end Itasca.Runtime.Interp.Machine

end

/-! ## ReturnCompletion -/

section

/-!
Completing a return while retaining the execution certificate.

Main declarations: `Execution.return_complete`. A direct consumer is `Interp.Machine.Frames.EpilogueExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem Execution.return_complete {M : Type}
 (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (expected : List valtype)
    (beforePC : Nat) (beforePending : Bool)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected beforePC beforePending)
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw)
    (src count : Nat) (effect : ReturnEffect exec after raw.base.val src count)
    (results : List val) (represented : ValuesAt exec.slots.val (raw.base.val+src) results)
    (types : results.map Compiler.valueType = f.resultTypes) (width : count = Compiler.slots (results.map Compiler.valueType))
    (bounds : raw.base.val+src+count ≤ exec.slots.length)
    (typed : SourceMachine.ATyped (returnedState (Store.decodeStore view code store) ambient rest results))
    (result : SourceMachine.InvocationResult expected (returnedState (Store.decodeStore view code store) ambient rest results)) :
    ∃ pc, Execution view code store after (returnedState (Store.decodeStore view code store) ambient rest results) expected pc false := by
  obtain ⟨stack,ready⟩ := machine.stack.return_complete ambient raw top effect results represented types width bounds
    (fun caller member => machine.typed.typed.heights caller (by simp [member]))
  obtain ⟨pc,cursor⟩ := ready.cursor
  cases rest <;> exact ⟨pc,rfl,⟨typed,machine.typed.contents⟩,Machine.return_supported machine.core results,result,stack,cursor⟩
end Itasca.Runtime.Interp.Machine

end

/-! ## EpilogueExecution -/

section

/-!
Execution of the function-end epilogue.

Main declarations: `step_function_end_execution`. A direct consumer is `Integration.Execution.Dispatch.HostSite`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem step_function_end_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := [],labels := []} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := [],labels := []}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := [],labels := []}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc source, Execution view code store out.2.1 source expected pc false ∧
        ConcreteSim compiled.code.length raw.pc.val pc false false initial source ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds source) ∧ source.ambient = ambient ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound source) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = index.val := by change exec.frames.length-1 = index.val; omega
    rw [position]; exact hf
  have binding := (machine.stack.top raw top).binding
  rcases function_end program point with ⟨target,forward,fetched,retained⟩ | ⟨count,fetched,localSlots,width,pcBound⟩
  · apply WP.spec_mono (step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
      ambient {f with code := [],labels := []} rest expected C targets next output target last hf hi hc forward fetched slots retained machine program)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := effect
    exact ⟨success,sameStore,samePlatform,target.val,_,fresh,simulation,(fun _ h => h),rfl,(fun _ h => h)⟩
  · obtain ⟨types,nextTyped,simulation⟩ := frame_end_source (Store.decodeStore view code store) ambient f rest machine.typed.typed
    have codeTypes : f.vals.map Compiler.valueType = f.resultTypes := by
      simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types
    have actualWidth : count.val = Compiler.slots (f.vals.map Compiler.valueType) := by rw [codeTypes]; exact width
    have capacity := slots.capacity binding
    have bounds : raw.base.val+compiled.local_slots.val+count.val ≤ exec.slots.length := by
      simpa only [List.map_append,Compiler.slots_append,localSlots,actualWidth,Nat.add_assoc] using capacity
    have original : ValuesAt exec.slots.val (raw.base.val+compiled.local_slots.val) f.vals := by
      simpa only [localSlots] using slots.operands
    apply WP.spec_mono (step_epilogue_refines memory hooks floats allocator exec store platform index raw compiled.local_slots count inst compiled
      last hf hi hc fetched pcBound (Store.decodeStore view code store) ambient {f with labels := []} rest (Or.inl rfl)
      machine.typed.typed slots localSlots width capacity)
    intro out effect
    obtain ⟨success,returned,represented,sameStore,samePlatform,preserved,nextState⟩ := effect
    have result := function_end_invocation_result (Store.decodeStore view code store) ambient f rest machine.typed.typed types expected machine.result
    obtain ⟨pc,fresh⟩ := Execution.return_complete view code ambient {f with code := [],labels := []} rest expected raw.pc.val false machine raw top
      compiled.local_slots.val count.val returned f.vals original codeTypes actualWidth bounds nextTyped result
    exact ⟨success,sameStore,samePlatform,pc,_,fresh,ConcreteSim.of_source _ _ _ _ _ simulation,
      Machine.return_owned f.vals (fun _ member => member),by cases rest <;> rfl,(fun _ bounded => returned_state_code_bound bounded f.vals)⟩
end Itasca.Runtime.Interp.Machine

end

/-! ## ReturnPoint -/

section

/-!
Inversion of return code points and their source values.

Main declarations: `code_rel_return_inv` and `code_rel_return_values`. A direct consumer is `Interp.Machine.Frames.StructuredReturn`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}
variable {emission : ContextEmission} [OrdinaryHeads emission]
theorem code_rel_return_inv {C returns locals code labels stack pc next output after}
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.RETURN :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.RETURN :: after) target.val next output) ∨
    (∃ front src count,
      stack = front ++ returns ∧ src.val = Compiler.slots locals + Compiler.slots front ∧
      count.val = Compiler.slots returns ∧ code[pc]? = some (.Return src count)) := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (emission_not_return head)
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | return_ source size instruction remaining scope => exact Or.inr ⟨_, _, _, rfl, source, size, instruction⟩

/-- Static return stack types identify the actual result suffix and every
copied word coordinate. -/
theorem code_rel_return_values {C returns code labels pc next output after}
    (locals values : List val)
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns (locals.map Compiler.valueType) code jumpTables labels
      (values.map Compiler.valueType) (.RETURN :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns (locals.map Compiler.valueType) code jumpTables labels
        (values.map Compiler.valueType) (.RETURN :: after) target.val next output) ∨
    (∃ front results src count,
      values = front ++ results ∧ results.map SourceMachine.valueType = returns ∧
      src.val = Compiler.slots ((locals ++ front).map Compiler.valueType) ∧
      count.val = Compiler.slots (results.map Compiler.valueType) ∧
      code[pc]? = some (.Return src count)) := by
  rcases code_rel_return_inv relation with skip | actual
  · exact Or.inl skip
  · obtain ⟨frontTypes, src, count, stack, source, size, instruction⟩ := actual
    obtain ⟨front, results, split, frontTypesEq, resultTypes⟩ := List.map_eq_append_iff.mp stack
    refine Or.inr ⟨front, results, src, count, split, ?_, ?_, ?_, instruction⟩
    · simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using resultTypes
    · simpa only [List.map_append, Compiler.slots_append, frontTypesEq] using source
    · simpa only [resultTypes] using size

end Itasca.Runtime.Interp.Machine

end

/-! ## StructuredReturn -/

section

/-!
Complete RETURN execution from a structured certificate. The certificate supplies the result suffix and word coordinates; an administrative forward skip retains the same source state and decreases the dispatch potential.

Main declarations: `step_return_structured`. A direct consumer is `Interp.Machine.Frames.ReturnExecution`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Complete RETURN execution from a structured certificate. The certificate
supplies the result suffix and word coordinates; an administrative forward skip
retains the same source state and decreases the dispatch potential. -/
theorem step_return_structured {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType) ≤ exec.slots.length)
    (point : FramePoint s raw { f with code := .RETURN :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((∃ target : U32,
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
        FramePoint s { raw with pc := target } { f with code := .RETURN :: after }
          compiled C targets next output ∧
        dispatchMeasure false compiled.code.length target.val
          ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ <
        dispatchMeasure false compiled.code.length raw.pc.val
          ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) ∨
      (∃ front results src count,
        f.vals = front ++ results ∧ results.map SourceMachine.valueType = f.resultTypes ∧
        src = Compiler.slots ((f.locals ++ front).map Compiler.valueType) ∧
        count = Compiler.slots (results.map Compiler.valueType) ∧
        ValuesAt exec.slots.val (raw.base.val + src) results ∧
        raw.base.val + src + count ≤ exec.slots.length ∧
        ReturnEffect exec out.2.1 raw.base.val src count ∧
        ValuesAt out.2.1.slots.val raw.base.val results ∧
        SourceMachine.ATyped (returnedState s ambient rest results) ∧
        SourceMachine.NextSim ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩
          (returnedState s ambient rest results))) ⦄ := by
  have current := point.code.current
  rw [point.locals] at current
  rcases code_rel_return_values f.locals f.vals current with skip | actual
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    refine ⟨effect.1, effect.2.2.1, effect.2.2.2, Or.inl ⟨target, effect.2.1, ?_, ?_⟩⟩
    · exact ⟨point.bindings,point.locals,point.labels, ⟨by simpa only [point.locals] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    · exact dispatch_measure_forward _ _ _ _ forward continuation.entry_bound
  · obtain ⟨front, results, src, count, split, types, source, width, fetched⟩ := actual
    have bounds : raw.base.val + src.val + count.val ≤ exec.slots.length := by
      simpa only [split, source, width, List.map_append, Compiler.slots_append, Nat.add_assoc] using capacity
    have sourceBound : raw.base.val + src.val ≤ Usize.max := by scalar_tac
    have typed' : SourceMachine.ATyped ⟨s, ambient, { f with code := .RETURN :: after, vals := front ++ results } :: rest, []⟩ := by
      simpa only [← split] using typed
    have next := return_next s ambient f rest after front results types
    have nextTyped := SourceMachine.instruction_preservation s ambient { f with vals := front ++ results }
      rest .RETURN after _ .ret typed' next
    have original : ValuesAt exec.slots.val (raw.base.val + src.val) results := by
      have words : WordsAt exec.slots.val raw.base.val
          (Compiler.encodeValues (f.locals ++ front) ++ Compiler.encodeValues results) := by
        simpa only [FrameSlots, ValuesAt, split, Compiler.encode_values_append, List.append_assoc] using slots
      simpa only [ValuesAt, Compiler.encode_values_length, source] using words.append_right
    apply WP.spec_mono (step_return_refines memory hooks floats allocator exec store platform
      index raw src count inst compiled last hf hi hc fetched pcBound s ambient f rest after front results
      typed' types (by simpa only [← split] using slots) source width bounds sourceBound)
    intro out effect
    obtain ⟨success, returned, represented, sameStore, samePlatform, simulation⟩ := effect
    refine ⟨success, sameStore, samePlatform, Or.inr ⟨front, results, src.val, count.val,
      split, types, source, width, original, bounds, returned, represented, nextTyped, ?_⟩⟩
    simpa only [← split] using simulation

end Itasca.Runtime.Interp.Machine

end

/-! ## ReturnExecution -/

section

/-!
Return-instruction execution in the structured machine.

Main declarations: `step_return_execution`. A direct consumer is `Integration.Execution.Dispatch.Host`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem step_return_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .RETURN::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .RETURN::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .RETURN::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc source, Execution view code store out.2.1 source expected pc false ∧
        ConcreteSim compiled.code.length raw.pc.val pc false false initial source ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds source) ∧ source.ambient = ambient ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound source) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = index.val := by change exec.frames.length-1 = index.val; omega
    rw [position]; exact hf
  have binding := (machine.stack.top raw top).binding
  have capacity := slots.capacity binding
  have current := point.code.current
  rw [point.locals] at current
  have pcBound : raw.pc.val < U32.max := by
    rcases code_rel_return_values f.locals f.vals current with ⟨target,forward,fetched,continuation⟩ | ⟨front,results,src,count,split,types,source,width,fetched⟩
    · exact program.fetched_bound _ fetched
    · exact program.fetched_bound _ fetched
  apply WP.spec_mono (step_return_structured memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest after last hf hi hc pcBound machine.typed.typed slots capacity point)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,operation⟩ := effect
  refine ⟨success,sameStore,samePlatform,?_⟩
  rcases operation with ⟨target,exactState,retained,decrease⟩ | ⟨front,results,src,count,split,types,source,width,original,bounds,returned,represented,nextTyped,simulation⟩
  · have fields : {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := target}} := by rw [exactState]
    have represented : FrameSlots out.2.1 {raw with pc := target} {f with code := .RETURN::after} := by simpa only [FrameSlots,exactState] using slots
    have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by rw [exactState]; exact .refl _ _
    refine ⟨target.val,_,Execution.ordinary view code ambient {f with code := .RETURN::after} {f with code := .RETURN::after} rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index target last hf program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ fields preserved machine.typed machine.core,?_,(fun _ h => h),rfl,(fun _ bounded => bounded)⟩
    exact Or.inl ⟨rfl,decrease⟩
  · have result := return_invocation_result (Store.decodeStore view code store) ambient f rest after front results machine.typed.typed split types expected machine.result
    obtain ⟨pc,fresh⟩ := Execution.return_complete view code ambient {f with code := .RETURN::after} rest expected raw.pc.val false machine raw top
      src count returned results original (by simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using types)
      width bounds nextTyped result
    exact ⟨pc,_,fresh,ConcreteSim.of_source _ _ _ _ _ simulation,
      Machine.return_owned results (by intro value member; change value ∈ f.vals; rw [split]; exact List.mem_append_right _ member),by cases rest <;> rfl,(fun _ bounded => returned_state_code_bound bounded results)⟩
end Itasca.Runtime.Interp.Machine

end

/-! ## Finished -/

section

/-!
The outcome of a finished machine execution.

Main declarations: `Execution.finished`. A direct consumer is `Integration.Execution.History.State`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std
theorem Execution.finished {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {source : SourceMachine.AState}
    {expected : List valtype} {pc : Nat} {pending : Bool}
    (invariant : Execution view code store exec source expected pc pending) (empty : exec.frames.val = []) :
    source.frames = [] ∧ SpecExt.ResultsTyped source.store expected source.results ∧
      ValuesAt exec.slots.val 0 source.results := by
  have sourceEmpty : source.frames = [] := by
    cases frames : source.frames with
    | nil => rfl
    | cons f rest =>
      have stack := invariant.stack
      rw [frames] at stack
      cases stack with
      | active concrete top saved => simp [empty] at concrete
  refine ⟨sourceEmpty,?_,?_⟩
  · simpa only [SourceMachine.InvocationResult,sourceEmpty] using invariant.result
  · have cursor := invariant.cursor
    simp only [Machine.ExecutionCursor,sourceEmpty] at cursor
    exact cursor.2.2
end Itasca.Runtime.Interp.Machine

end

/-! ## FrameStorePrefix -/

section

/-!
Saved-frame transport through a preserved store prefix.

Main declarations: `SavedFrame.store_prefix_extension` and `SavedFrames.store_prefix_extension`. A direct consumer is `Interp.Machine.Calls.HostReturnFrames`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem SavedFrame.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    (extension : Extend_store oldSource newSource) {exec raw source waiting childBase}
    (saved : SavedFrame before oldSource exec raw source waiting childBase) :
    SavedFrame after newSource exec raw source waiting childBase := by
  refine ⟨saved.binding.store_prefix retained bounds,saved.slots,saved.destination,?_⟩
  obtain ⟨compiled,C,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,C,targets,next,output,program.store_prefix retained,point.extend extension⟩

theorem SavedFrames.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    (extension : Extend_store oldSource newSource) {exec raws sources waiting base}
    (saved : SavedFrames before oldSource exec raws sources waiting base) :
    SavedFrames after newSource exec raws sources waiting base := by
  induction saved with
  | nil waiting => exact .nil waiting
  | cons head tail ih => exact .cons (head.store_prefix_extension retained bounds extension) ih

end Itasca.Runtime.Interp.Machine

end

/-! ## FrameDepth -/

section

/-!
Lengths and source frame depth of retained frame-stack relations.

Main declarations: `SavedFrames.length` and `FrameStackRel.depth`. A direct consumer is `Integration.Execution.Resources.BoundaryCauses`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

@[simp] theorem SavedFrames.length {M : Type} {store : runtime.store.Store M}
    {sourceStore exec raws sources waiting base}
    (saved : SavedFrames store sourceStore exec raws sources waiting base) :
    raws.length = sources.length := by
  induction saved with
  | nil => rfl
  | cons head tail ih => simp only [List.length_cons, ih]

theorem FrameStackRel.length {M : Type} {store : runtime.store.Store M}
    {sourceStore exec sources} (stack : FrameStackRel store sourceStore exec sources) :
    exec.frames.length = sources.length := by
  cases stack with
  | empty frames => simp [alloc.vec.Vec.length, frames]
  | active frames top saved =>
    change exec.frames.val.length = _
    rw [frames, List.length_append, List.length_reverse, saved.length]
    simp

/-- The concrete counter is exactly the decoded configuration's FRAME_ depth. -/
theorem FrameStackRel.depth {M : Type} {store : runtime.store.Store M}
    {sourceStore exec} {source : SourceMachine.AState}
    (stack : FrameStackRel store sourceStore exec source.frames) :
    exec.frames.length = Spec.frameDepth (SourceMachine.decode source) := by
  rw [SourceMachine.decode_depth]
  exact stack.length
end Itasca.Runtime.Interp.Machine

end
