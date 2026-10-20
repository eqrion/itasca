import Exec.Spec.Choices.RedexArity
import Exec.Spec.Choices.FreeSyntax
/-! Primitive chosen reductions, with label/frame contexts kept explicit and
instruction-prefix contexts factored out. -/
namespace Exec.Spec
open SpecExt

theorem DirectWrite.choice_free {before after : config} (source : DirectWrite before after) :
    ChoiceFreeWriteRedex (trapCode before) := by
  cases source <;> constructor

inductive CoreChoiceStep (choices : SourceChoices) (occurrence : Nat) : config → List HostEvent → config → Prop
  | ordinary_pure {z : state} {body result : List admininstr}
      (source : Step_pure body result) (free : ChoiceFreePureRedex body)
      (inputWf : wf_config ⟨z,body⟩) (outputWf : wf_config ⟨z,result⟩) :
      CoreChoiceStep choices occurrence ⟨z,body⟩ [] ⟨z,result⟩
  | ordinary_read {z : state} {body result : List admininstr}
      (source : Step_read ⟨z,body⟩ result)
      (inputWf : wf_config ⟨z,body⟩) (outputWf : wf_config ⟨z,result⟩) :
      CoreChoiceStep choices occurrence ⟨z,body⟩ [] ⟨z,result⟩
  | write {z z' : state} {body result : List admininstr}
      (source : DirectWrite ⟨z,body⟩ ⟨z',result⟩) :
      CoreChoiceStep choices occurrence ⟨z,body⟩ [] ⟨z',result⟩
  | numeric {s : store} {f : frame} {request : NumericRequest} {result : Option num_}
      (chosen : ChosenNumeric choices.numeric occurrence request result)
      (inputWf : wf_config ⟨⟨s,f⟩,request.instructions⟩)
      (outputWf : wf_config ⟨⟨s,f⟩,numericOutput request.type result⟩) :
      CoreChoiceStep choices occurrence ⟨⟨s,f⟩,request.instructions⟩ []
        ⟨⟨s,f⟩,numericOutput request.type result⟩
  | vector {s : store} {f : frame} {request : VectorRequest} {result : Option vec_}
      (chosen : ChosenVector choices.vector occurrence request result)
      (inputWf : wf_config ⟨⟨s,f⟩,request.instructions⟩)
      (outputWf : wf_config ⟨⟨s,f⟩,vectorOutput result⟩) :
      CoreChoiceStep choices occurrence ⟨⟨s,f⟩,request.instructions⟩ [] ⟨⟨s,f⟩,vectorOutput result⟩
  | memory (s : store) (f : frame) (delta : Nat)
      (storeWf : wf_store s) (frameWf : wf_frame f) (deltaBound : delta < 2^32)
      (mapped : choices.memory occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta ≠ none → 0 < f.MODULE.MEMS.length)
      (bounded : choices.memory occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta ≠ none →
        (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536 < 2^32) :
      CoreChoiceStep choices occurrence ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
        (memoryGrowthOutput s f (choices.memory occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta))
  | table (s : store) (f : frame) (index delta : Nat) (value : ref)
      (storeWf : wf_store s) (frameWf : wf_frame f) (indexBound : index < 2^32) (deltaBound : delta < 2^32)
      (mapped : choices.table occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value ≠ none → index < f.MODULE.TABLES.length)
      (bounded : choices.table occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value ≠ none →
        (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32) :
      CoreChoiceStep choices occurrence ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
        (tableGrowthOutput s f index (choices.table occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value))
  | host (s : store) (f : frame) (address : funcaddr) (identity : Nat)
      (params results : List valtype) (args : List val)
      (storeTyped : Store_ok s) (frameWf : wf_frame f)
      (host : HostFunction s address identity params results) (arguments : ResultsTyped s params args) :
      CoreChoiceStep choices occurrence ⟨⟨s,f⟩,vals args ++ [.CALL_ADDR address]⟩
        [.call address args (choices.host occurrence s address identity params results args).result]
        ((choices.host occurrence s address identity params results args).configuration f)
  | label {z z' : state} {arity : Nat} {continuation : List instr} {body body' : List admininstr} {events}
      (source : ChoiceStep choices occurrence ⟨z,body⟩ events ⟨z',body'⟩)
      (inputWf : wf_config ⟨z,[.LABEL_ arity continuation body]⟩)
      (outputWf : wf_config ⟨z',[.LABEL_ arity continuation body']⟩) :
      CoreChoiceStep choices occurrence ⟨z,[.LABEL_ arity continuation body]⟩ events ⟨z',[.LABEL_ arity continuation body']⟩
  | frame {s s' : store} {ambient inner inner' : _root_.frame} {arity : Nat} {body body' : List admininstr} {events}
      (source : ChoiceStep choices occurrence ⟨⟨s,inner⟩,body⟩ events ⟨⟨s',inner'⟩,body'⟩)
      (inputWf : wf_config ⟨⟨s,ambient⟩,[.FRAME_ arity inner body]⟩)
      (outputWf : wf_config ⟨⟨s',ambient⟩,[.FRAME_ arity inner' body']⟩) :
      CoreChoiceStep choices occurrence ⟨⟨s,ambient⟩,[.FRAME_ arity inner body]⟩ events ⟨⟨s',ambient⟩,[.FRAME_ arity inner' body']⟩


theorem CoreChoiceStep.toChoiceStep {choices : SourceChoices} {occurrence before events after}
    (source : CoreChoiceStep choices occurrence before events after) :
    ChoiceStep choices occurrence before events after := by
  cases source
  case write source => exact .ordinary_write source.erases source.choice_free
  all_goals solve_by_elim (maxDepth := 16) [ChoiceStep.ordinary_pure,ChoiceStep.ordinary_read,
    ChoiceStep.numeric,ChoiceStep.vector,ChoiceStep.memory,ChoiceStep.table,ChoiceStep.host,
    ChoiceStep.label,ChoiceStep.frame]

inductive ContextualCore (choices : SourceChoices) (occurrence : Nat) : config → List HostEvent → config → Prop
  | intro (before after : state) (front : List val) (body result tail : List admininstr) (events : List HostEvent)
      (core : CoreChoiceStep choices occurrence ⟨before,body⟩ events ⟨after,result⟩) :
      ContextualCore choices occurrence ⟨before,vals front++(body++tail)⟩ events ⟨after,vals front++(result++tail)⟩

theorem CoreChoiceStep.contextual {choices : SourceChoices} {occurrence before events after}
    (source : CoreChoiceStep choices occurrence before events after) :
    ContextualCore choices occurrence before events after := by
  cases before with | mk_config z body =>
  cases after with | mk_config next result =>
  simpa only [vals,List.map_nil,List.nil_append,List.append_nil] using
    ContextualCore.intro z next [] body result [] events source

theorem ContextualCore.instrs {choices : SourceChoices} {occurrence : Nat} {z z' : state}
    {body result : List admininstr} {events : List HostEvent} (front : List val) (tail : List admininstr)
    (source : ContextualCore choices occurrence ⟨z,body⟩ events ⟨z',result⟩) :
    ContextualCore choices occurrence ⟨z,vals front++(body++tail)⟩ events ⟨z',vals front++(result++tail)⟩ := by
  cases source with
  | intro z z' inner body result rest events core =>
    simpa only [vals,List.map_append,List.append_assoc] using
      ContextualCore.intro z z' (front++inner) body result (rest++tail) events core
end Exec.Spec
