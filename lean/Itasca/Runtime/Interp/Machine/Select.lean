import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.Machine.Select.Emission
import Itasca.Runtime.Interp.Relations.SelectSlots
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Machine.Control.ForwardJump
import Itasca.Runtime.SourceMachine.Core.SelectPositive
import Itasca.Runtime.Interp.Machine.Control.UniformSource
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Spec.Extend

/-!
Untyped select machine fetch, step and ownership. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Select Point -/

section

namespace Itasca.Runtime.Interp.Machine.Select
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
theorem core_point_select_head {C returns code labels stack pc next output} (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.SELECT none :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.SELECT none :: after) target.val next output) ∨
    (∃ front ty left right condition, stack = front ++ [ty,ty,.I32] ∧
      left.val = Compiler.slots C.LOCALS+Compiler.slots front ∧ right.val = left.val+Compiler.width ty ∧
      condition.val = right.val+Compiler.width ty ∧
      code[pc]? = some (Compiler.selectInstruction (decide (Compiler.width ty = 2)) left right condition) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.SELECT none :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,left,right,condition,input,emitted,result,leftPos,rightPos,conditionPos⟩ := scalar_emission_select_inv (FloatHeads.project (.core .select) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,left,right,condition,rfl,leftPos,rightPos,conditionPos,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq

end Itasca.Runtime.Interp.Machine.Select

end

/-! ## Select Step -/

section

namespace Itasca.Runtime.Interp.Machine.Select
open Aeneas Aeneas.Std SpecExt

theorem step_select_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (sourceStore : _root_.store) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max) (slots : FrameSlots exec raw f)
    (point : FramePoint sourceStore raw {f with code := .SELECT none::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped {initial with frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with frames := g::rest} ∨ SourceMachine.Core.step initial = .next {initial with frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  dsimp only
  rcases core_point_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
  · have retained : FramePoint sourceStore {raw with pc := target} {f with code := .SELECT none::after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .SELECT none::after} rest C targets next output target
      last frameFound instanceFound codeFound pcBound forward fetched slots retained typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · rw [exactState]; exact .refl _ _
  · have frameTyped : SourceMachine.FrameTyped sourceStore {f with code := .SELECT none::after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨front,left,right,bits,valueTy,split,bitsBound,leftType,rightType,heights⟩ := select_typed_operands frameTyped
    have conditionType : Compiler.valueType (SourceMachine.integerVal .I32 bits) = .I32 := rfl
    have stackEq : front.map Compiler.valueType ++ [valueTy,valueTy,.I32] = types ++ [ty,ty,.I32] := by
      simpa only [split,List.map_append,List.map_cons,List.map_nil,leftType,rightType,conditionType] using input
    have lengthEq : (front.map Compiler.valueType).length = types.length := by
      have lengths := congrArg List.length stackEq
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨frontEq,typeEq⟩ := List.append_inj stackEq lengthEq
    have sameTy : valueTy = ty := (List.cons.inj typeEq).1
    have leftType' : Compiler.valueType left = ty := leftType.trans sameTy
    have rightType' : Compiler.valueType right = ty := rightType.trans sameTy
    have position : a.val = Compiler.slots ((f.locals++front).map Compiler.valueType) := by
      simpa only [List.map_append,Compiler.slots_append,point.locals,← frontEq] using leftPos
    have actual := select_source_next (s := sourceStore) (ambient := ambient) (rest := rest) (after := after) split (leftType.trans rightType.symm) bitsBound
    obtain ⟨nextState,nextEq,fresh,source⟩ := SourceMachine.Core.select_progress sourceStore ambient f rest after typed
    have nextEq' : SourceMachine.Core.step ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩ = .next nextState := nextEq
    have sameState := SourceMachine.AResult.next.inj (actual.symm.trans nextEq')
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Compiler.selectInstruction (decide (Compiler.width ty = 2)) a b condition) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have continuation : FramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := front++[if bits = 0 then right else left]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (front++[left,right,SourceMachine.integerVal .I32 bits]) f.labels targets := by simpa only [split] using point.labels
        exact labels.replace_suffix heights
      · have selectedType : Compiler.valueType (if bits = 0 then right else left) = ty := by split <;> first | exact rightType' | exact leftType'
        simpa only [List.map_append,List.map_cons,List.map_nil,selectedType,frontEq,pcNext] using tail
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++[left,right,SourceMachine.integerVal .I32 bits]) := by
      simpa only [FrameSlots,split,List.append_assoc] using slots
    apply WP.spec_mono (select_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw (f.locals++front) left right bits a b condition ty
      represented leftType' rightType' position rightPos conditionPos bitsBound)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,fields,preserved⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,fields,?_,continuation,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr actual,?_,preserved⟩
    · simpa only [FrameSlots,List.append_assoc] using represented
    · exact Or.inr ⟨1,by omega,by simpa using Itasca.Runtime.Spec.StepsHN.cons source (Itasca.Runtime.Spec.StepsHN.refl (Itasca.Runtime.Spec.step_h_wf source).2)⟩
end Itasca.Runtime.Interp.Machine.Select

end

/-! ## Select Execution Owned -/

section

namespace Itasca.Runtime.Interp.Machine.Select
open Aeneas Aeneas.Std
theorem step_select_core_execution_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .SELECT none::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        UniformConcreteSim raw.pc.val pc.val false false initial {initial with frames := g::rest} [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_select_core memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest after last frameFound instanceFound codeFound pcBound slots point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,fields,represented,retained,fresh,metadata,transition,simulation,preserved⟩ := effect
  have uniform : UniformConcreteSim raw.pc.val pc.val false false
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
      ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
    rcases transition with same | step
    · rw [← same] at simulation ⊢
      exact simulation.uniform_same (by scalar_tac)
    · exact UniformConcreteSim.single (SourceMachine.Core.select_step_positive _ _ _ _ _ _ machine.typed step)
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases transition with same | step
    · rw [← same]; exact machine.core
    · exact Machine.core_step_supported machine.typed machine.core step
  exact ⟨success,sameStore,samePlatform,pc,g,
    Execution.ordinary view code ambient {f with code := .SELECT none::after} g rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,uniform,Machine.owned_transition machine.typed machine.core transition,Machine.bound_transition machine.typed machine.core transition⟩
theorem step_select_core_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .SELECT none::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  apply WP.spec_mono (step_select_core_execution_owned_uniform memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,same,platform,pc,g,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,same,platform,pc,g,machine,simulation,ownership,bounded⟩

end Itasca.Runtime.Interp.Machine.Select

end
