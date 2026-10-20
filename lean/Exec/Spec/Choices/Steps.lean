import Exec.Spec.Choices.Redex
import Exec.Spec.Choices.HostChoices
import Exec.Spec.Choices.NumericChoices
import Exec.Spec.Choices.VectorChoices
import Exec.Spec.Choices.GrowthChoices

/-! Source reductions with explicit policies at the redex and the same
administrative evaluation contexts. Occurrences count reductions, including
ordinary reductions, so repeated identical requests may choose differently.
Erasure does not assert global determinism of the generated ordinary rules. -/
namespace Exec.Spec
open SpecExt

structure SourceChoices where
  host : HostChoices
  numeric : NumericChoices
  vector : VectorChoices
  memory : MemoryGrowthChoices
  table : TableGrowthChoices

structure SourceChoices.Admissible (choices : SourceChoices) : Prop where
  host : choices.host.Admissible
  numeric : choices.numeric.Admissible
  vector : choices.vector.Admissible
  memory : choices.memory.Admissible
  table : choices.table.Admissible

/-- One admissible collection of source policies, independent of concrete
execution. Its mathematical vector selector is not a native implementation. -/
noncomputable def defaultSourceChoices : SourceChoices :=
  ⟨trappingHostChoice,firstNumericChoice,sourceVectorChoice,(fun _ _ _ => none),(fun _ _ _ _ => none)⟩

theorem defaultSourceChoices_admissible : defaultSourceChoices.Admissible :=
  ⟨trappingHostChoice_admissible,firstNumericChoice_admissible,sourceVectorChoice_admissible,
    refuse_memory_growth_admissible,refuse_table_growth_admissible⟩

/-- Active scalar/SIMD numeric operators and growth must consume a choice.
Labels and frames must be inspected recursively, rather than treated as atoms. -/
def ordinaryChoiceTag : admininstr → Bool
  | .UNOP _ _ | .BINOP _ _ | .CVTOP _ _ _
  | .VUNOP _ _ | .VBINOP _ _ | .VCVTOP _ _ _
  | .MEMORY_GROW | .TABLE_GROW _ | .LABEL_ _ _ _ | .FRAME_ _ _ _ => false
  | _ => true

inductive ChoiceFreeInstruction : admininstr → Prop
  | atom (instruction : admininstr) (ordinary : ordinaryChoiceTag instruction = true) :
      ChoiceFreeInstruction instruction
  | label (arity : Nat) (continuation : List instr) (body : List admininstr)
      (free : ∀ instruction ∈ body, ChoiceFreeInstruction instruction) :
      ChoiceFreeInstruction (.LABEL_ arity continuation body)
  | frame (arity : Nat) (ambient : _root_.frame) (body : List admininstr)
      (free : ∀ instruction ∈ body, ChoiceFreeInstruction instruction) :
      ChoiceFreeInstruction (.FRAME_ arity ambient body)

def ChoiceFreeConfig : config → Prop
  | ⟨_,body⟩ => ∀ instruction ∈ body, ChoiceFreeInstruction instruction

/-- Only ordinary generated reductions may bypass the policy interfaces.
Choosing reductions and their contexts retain exactly the source events. -/
inductive ChoiceStep (choices : SourceChoices) (occurrence : Nat) : config → List HostEvent → config → Prop
  | ordinary {before after} (source : Step before after) (free : ChoiceFreeConfig before) :
      ChoiceStep choices occurrence before [] after
  | ordinary_pure {z : state} {body result : List admininstr}
      (source : Step_pure body result) (free : ChoiceFreePureRedex body)
      (inputWf : wf_config ⟨z,body⟩) (outputWf : wf_config ⟨z,result⟩) :
      ChoiceStep choices occurrence ⟨z,body⟩ [] ⟨z,result⟩
  | ordinary_read {z : state} {body result : List admininstr}
      (source : Step_read ⟨z,body⟩ result)
      (inputWf : wf_config ⟨z,body⟩) (outputWf : wf_config ⟨z,result⟩) :
      ChoiceStep choices occurrence ⟨z,body⟩ [] ⟨z,result⟩
  | ordinary_write {z z' : state} {body result : List admininstr}
      (source : Step ⟨z,body⟩ ⟨z',result⟩) (free : ChoiceFreeWriteRedex body) :
      ChoiceStep choices occurrence ⟨z,body⟩ [] ⟨z',result⟩
  | numeric {s : store} {f : frame} {request : NumericRequest} {result : Option num_}
      (chosen : ChosenNumeric choices.numeric occurrence request result)
      (inputWf : wf_config ⟨⟨s,f⟩,request.instructions⟩)
      (outputWf : wf_config ⟨⟨s,f⟩,numericOutput request.type result⟩) :
      ChoiceStep choices occurrence ⟨⟨s,f⟩,request.instructions⟩ []
        ⟨⟨s,f⟩,numericOutput request.type result⟩
  | vector {s : store} {f : frame} {request : VectorRequest} {result : Option vec_}
      (chosen : ChosenVector choices.vector occurrence request result)
      (inputWf : wf_config ⟨⟨s,f⟩,request.instructions⟩)
      (outputWf : wf_config ⟨⟨s,f⟩,vectorOutput result⟩) :
      ChoiceStep choices occurrence ⟨⟨s,f⟩,request.instructions⟩ [] ⟨⟨s,f⟩,vectorOutput result⟩
  | memory (s : store) (f : frame) (delta : Nat)
      (storeWf : wf_store s) (frameWf : wf_frame f) (deltaBound : delta < 2^32)
      (mapped : choices.memory occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta ≠ none → 0 < f.MODULE.MEMS.length)
      (bounded : choices.memory occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta ≠ none →
        (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536 < 2^32) :
      ChoiceStep choices occurrence ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
        (memoryGrowthOutput s f (choices.memory occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta))
  | table (s : store) (f : frame) (index delta : Nat) (value : ref)
      (storeWf : wf_store s) (frameWf : wf_frame f) (indexBound : index < 2^32) (deltaBound : delta < 2^32)
      (mapped : choices.table occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value ≠ none → index < f.MODULE.TABLES.length)
      (bounded : choices.table occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value ≠ none →
        (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32) :
      ChoiceStep choices occurrence ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
        (tableGrowthOutput s f index (choices.table occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value))
  | host (s : store) (f : frame) (address : funcaddr) (identity : Nat)
      (params results : List valtype) (args : List val)
      (storeTyped : Store_ok s) (frameWf : wf_frame f)
      (host : HostFunction s address identity params results) (arguments : ResultsTyped s params args) :
      ChoiceStep choices occurrence ⟨⟨s,f⟩,vals args ++ [.CALL_ADDR address]⟩
        [.call address args (choices.host occurrence s address identity params results args).result]
        ((choices.host occurrence s address identity params results args).configuration f)
  | label {z z' : state} {arity : Nat} {continuation : List instr} {body body' : List admininstr} {events}
      (source : ChoiceStep choices occurrence ⟨z,body⟩ events ⟨z',body'⟩)
      (inputWf : wf_config ⟨z,[.LABEL_ arity continuation body]⟩)
      (outputWf : wf_config ⟨z',[.LABEL_ arity continuation body']⟩) :
      ChoiceStep choices occurrence ⟨z,[.LABEL_ arity continuation body]⟩ events ⟨z',[.LABEL_ arity continuation body']⟩
  | frame {s s' : store} {ambient inner inner' : _root_.frame} {arity : Nat} {body body' : List admininstr} {events}
      (source : ChoiceStep choices occurrence ⟨⟨s,inner⟩,body⟩ events ⟨⟨s',inner'⟩,body'⟩)
      (inputWf : wf_config ⟨⟨s,ambient⟩,[.FRAME_ arity inner body]⟩)
      (outputWf : wf_config ⟨⟨s',ambient⟩,[.FRAME_ arity inner' body']⟩) :
      ChoiceStep choices occurrence ⟨⟨s,ambient⟩,[.FRAME_ arity inner body]⟩ events ⟨⟨s',ambient⟩,[.FRAME_ arity inner' body']⟩
  | instrs {z z' : state} {front : List val} {body body' after : List admininstr} {events}
      (source : ChoiceStep choices occurrence ⟨z,body⟩ events ⟨z',body'⟩)
      (nonempty : front ≠ [] ∨ after ≠ [])
      (inputWf : wf_config ⟨z,vals front ++ (body ++ after)⟩)
      (outputWf : wf_config ⟨z',vals front ++ (body' ++ after)⟩) :
      ChoiceStep choices occurrence ⟨z,vals front ++ (body ++ after)⟩ events ⟨z',vals front ++ (body' ++ after)⟩

/-- Choice-indexed reductions erase to the strengthened ordinary host semantics. -/
theorem ChoiceStep.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence before events after} (source : ChoiceStep choices occurrence before events after) :
    StepH before events after := by
  induction source with
  | ordinary source _ => exact .step source
  | ordinary_pure source _ inputWf outputWf => exact .step (.pure _ _ _ source inputWf outputWf)
  | ordinary_read source inputWf outputWf => exact .step (.read _ _ _ source inputWf outputWf)
  | ordinary_write source _ => exact .step source
  | numeric chosen inputWf outputWf =>
    exact .step (.pure _ _ _ (chosen.erases admissible.numeric) inputWf outputWf)
  | vector chosen inputWf outputWf =>
    exact .step (.pure _ _ _ chosen.erases inputWf outputWf)
  | memory s f delta storeWf frameWf deltaBound mapped bounded =>
    exact memory_growth_choice_erases_conditional choices.memory admissible.memory occurrence s f delta storeWf frameWf deltaBound mapped bounded
  | table s f index delta value storeWf frameWf indexBound deltaBound mapped bounded =>
    exact table_growth_choice_erases_conditional choices.table admissible.table occurrence s f index delta value
      storeWf frameWf indexBound deltaBound mapped bounded
  | host s f address identity params results args storeTyped frameWf host arguments =>
    exact host_choice_erases choices.host admissible.host occurrence s f address identity params results args
      storeTyped frameWf host arguments
  | label _ inputWf outputWf ih =>
    exact .ctxt_label ih inputWf outputWf (stepH_wf ih).1 (stepH_wf ih).2
  | frame _ inputWf outputWf ih =>
    exact .ctxt_frame ih inputWf outputWf (stepH_wf ih).1 (stepH_wf ih).2
  | instrs _ nonempty inputWf outputWf ih =>
    exact .ctxt_instrs ih nonempty inputWf outputWf (stepH_wf ih).1 (stepH_wf ih).2

inductive ChoiceSteps (choices : SourceChoices) : Nat → config → List HostEvent → config → Prop
  | refl (occurrence : Nat) {config} (wf : wf_config config) : ChoiceSteps choices occurrence config [] config
  | cons {occurrence before middle after events rest}
      (first : ChoiceStep choices occurrence before events middle)
      (tail : ChoiceSteps choices (occurrence + 1) middle rest after) :
      ChoiceSteps choices occurrence before (events ++ rest) after

theorem ChoiceSteps.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence before events after} (source : ChoiceSteps choices occurrence before events after) :
    StepsH before events after := by
  induction source with
  | refl _ wf => exact .refl wf
  | cons first _ ih => exact .cons (first.erases admissible) ih

end Exec.Spec
