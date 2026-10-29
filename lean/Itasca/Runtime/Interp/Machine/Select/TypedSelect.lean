import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.Machine.Select.Emission
import Itasca.Runtime.Interp.Relations.SelectSlots
import Itasca.Runtime.Interp.Relations.TypedSelectOperands
import Itasca.Runtime.Interp.Machine.Control.ForwardJump
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.SourceMachine.TypedSelect.Step
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Spec.Extend

/-!
Typed select machine fetch, step and execution. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Typed Select Point -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.TypedSelect
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [TypedSelectHeads family]
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
theorem point_select_head {declared : valtype} {C returns code labels stack pc next output} (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.SELECT (some [declared]) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.SELECT (some [declared]) :: after) target.val next output) ∨
    (∃ front ty left right condition, stack = front ++ [ty,ty,.I32] ∧
      left.val = Code.slots C.LOCALS+Code.slots front ∧ right.val = left.val+Code.width ty ∧
      condition.val = right.val+Code.width ty ∧
      code[pc]? = some (Code.selectInstruction (decide (Code.width ty = 2)) left right condition) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.SELECT (some [declared]) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    have selected := TypedSelectHeads.project head
    cases selected with
    | select front ty left right condition leftPos rightPos conditionPos =>
      have fetch := fragment.fetch (index := 0) (by rfl)
      obtain ⟨_,_,_,_,nextEq⟩ := fragment
      refine Or.inr ⟨front,declared,left,right,condition,rfl,leftPos,rightPos,conditionPos,by simpa using fetch,?_⟩
      exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq

end Itasca.Runtime.Interp.StructuredMachine.TypedSelect

end

/-! ## Typed Select Step -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.TypedSelect
open Aeneas Aeneas.Std SpecExt

theorem step_select {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (sourceStore : _root_.store) (ambient : frame)
    (f : Abs.AFrame) (rest : List Abs.AFrame) (declared : valtype) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max) (slots : FrameSlots exec raw f)
    (point : FramePoint sourceStore raw {f with code := .SELECT (some [declared])::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨sourceStore,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped {initial with frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with frames := g::rest} ∨ Abs.Core.select initial f rest after = .next {initial with frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  dsimp only
  rcases point_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
  · have retained : FramePoint sourceStore {raw with pc := target} {f with code := .SELECT (some [declared])::after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .SELECT (some [declared])::after} rest C targets next output target
      last frameFound instanceFound codeFound pcBound forward fetched slots retained typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · rw [exactState]; exact .refl _ _
  · have frameTyped : Abs.FrameTyped sourceStore {f with code := .SELECT (some [declared])::after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨front,left,right,bits,valueTy,split,bitsBound,leftType,rightType,heights⟩ := Interp.TypedSelect.select_typed_operands frameTyped
    have conditionType : Code.valueType (Abs.integerVal .I32 bits) = .I32 := rfl
    have stackEq : front.map Code.valueType ++ [valueTy,valueTy,.I32] = types ++ [ty,ty,.I32] := by
      simpa only [split,List.map_append,List.map_cons,List.map_nil,leftType,rightType,conditionType] using input
    have lengthEq : (front.map Code.valueType).length = types.length := by
      have lengths := congrArg List.length stackEq
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨frontEq,typeEq⟩ := List.append_inj stackEq lengthEq
    have sameTy : valueTy = ty := (List.cons.inj typeEq).1
    have leftType' : Code.valueType left = ty := leftType.trans sameTy
    have rightType' : Code.valueType right = ty := rightType.trans sameTy
    have position : a.val = Code.slots ((f.locals++front).map Code.valueType) := by
      simpa only [List.map_append,Code.slots_append,point.locals,← frontEq] using leftPos
    have actual := Interp.TypedSelect.select_source_next (annotation := some [declared]) (s := sourceStore) (ambient := ambient) (rest := rest) (after := after) split (leftType.trans rightType.symm) bitsBound
    obtain ⟨nextState,nextEq,fresh,source⟩ := Abs.TypedSelect.progress sourceStore ambient f rest (some [declared]) after typed
    have nextEq' : Abs.Core.select ⟨sourceStore,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩ f rest after = .next nextState := nextEq
    have sameState := Abs.AResult.next.inj (actual.symm.trans nextEq')
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Code.selectInstruction (decide (Code.width ty = 2)) a b condition) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have continuation : FramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := front++[if bits = 0 then right else left]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (front++[left,right,Abs.integerVal .I32 bits]) f.labels targets := by simpa only [split] using point.labels
        exact labels.replace_suffix heights
      · have selectedType : Code.valueType (if bits = 0 then right else left) = ty := by split <;> first | exact rightType' | exact leftType'
        simpa only [List.map_append,List.map_cons,List.map_nil,selectedType,frontEq,pcNext] using tail
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++[left,right,Abs.integerVal .I32 bits]) := by
      simpa only [FrameSlots,split,List.append_assoc] using slots
    apply WP.spec_mono (select_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw (f.locals++front) left right bits a b condition ty
      represented leftType' rightType' position rightPos conditionPos bitsBound)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,fields,preserved⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,fields,?_,continuation,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr actual,?_,preserved⟩
    · simpa only [FrameSlots,List.append_assoc] using represented
    · exact Or.inr ⟨1,by omega,by simpa using Itasca.Runtime.Spec.StepsHN.cons source (Itasca.Runtime.Spec.StepsHN.refl (Itasca.Runtime.Spec.stepH_wf source).2)⟩
end Itasca.Runtime.Interp.StructuredMachine.TypedSelect

end

/-! ## Typed Select Execution -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.TypedSelect
open Aeneas Aeneas.Std
theorem step_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame)
    (f : Abs.AFrame) (rest : List Abs.AFrame) (declared : valtype) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .SELECT (some [declared])::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases point_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_select memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest declared after last frameFound instanceFound codeFound pcBound slots point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,fields,represented,retained,fresh,metadata,transition,simulation,preserved⟩ := effect
  have covered : Abs.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases transition with same | step
    · rw [← same]; exact machine.core
    · exact (Abs.TypedSelect.Step.next step).next_supported machine.core
  refine ⟨success,sameStore,samePlatform,pc,g,
    Execution.ordinary view code ambient {f with code := .SELECT (some [declared])::after} g rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,?_,?_⟩
  · intro bounds owned
    rcases transition with same | step
    · rw [←same]; exact owned
    · exact (Abs.TypedSelect.Step.next step).next_owned owned
  · intro bound bounded
    rcases transition with same | step
    · rw [←same]; exact bounded
    · exact (Abs.TypedSelect.Step.next step).next_bound bounded
end Itasca.Runtime.Interp.StructuredMachine.TypedSelect

end
