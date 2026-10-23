import Exec.Abs.Sim.ChosenBasic
import Exec.Interp.Relations.ChosenControlSource
import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.StructuredMachine.SelectPoint
import Exec.Interp.Relations.SelectSlots
import Exec.Interp.Machines.Core.CoreSelectOperands
import Exec.Interp.StructuredMachine.ForwardJump
namespace Exec.Interp.StructuredMachine.Select
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
open Aeneas Aeneas.Std SpecExt

theorem step_select_core_chosen {choices : Exec.Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Exec.Spec.firstVectorChoice) (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (sourceStore : _root_.store) (ambient : frame)
    (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max) (slots : FrameSlots exec raw f)
    (point : FramePoint emission sourceStore raw {f with code := .SELECT none::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped {initial with frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with frames := g::rest} ∨ Abs.Core.step initial = .next {initial with frames := g::rest}) ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  dsimp only
  rcases corePoint_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
  · have retained : FramePoint emission sourceStore {raw with pc := target} {f with code := .SELECT none::after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .SELECT none::after} rest C targets next output target
      last frameFound instanceFound codeFound pcBound forward fetched slots retained typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward tail.current.entry_bound⟩,?_⟩
    · rw [exactState]
    · rw [exactState]; exact .refl _ _
  · have frameTyped : Abs.FrameTyped sourceStore {f with code := .SELECT none::after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨front,left,right,bits,valueTy,split,bitsBound,leftType,rightType,heights⟩ := select_typed_operands frameTyped
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
    have actual := select_source_next (s := sourceStore) (ambient := ambient) (rest := rest) (after := after) split (leftType.trans rightType.symm) bitsBound
    obtain ⟨nextState,nextEq,fresh,source⟩ := Abs.Core.select_progress sourceStore ambient f rest after typed
    have nextEq' : Abs.Core.step ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩ = .next nextState := nextEq
    have sameState := Abs.AResult.next.inj (actual.symm.trans nextEq')
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Code.selectInstruction (decide (Code.width ty = 2)) a b condition) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have continuation : FramePoint emission sourceStore {raw with pc := pc}
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
    · exact ChosenConcreteSim.single admissible (Abs.chosen_neutral_simulation admissible vector occurrence source
        (by simp only [List.map_cons,admininstr_instr,Exec.Spec.neutralActive]))
end Exec.Interp.StructuredMachine.Select
