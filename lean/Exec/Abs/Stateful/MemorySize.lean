import Exec.Abs.Stateful.TableTyping
import Exec.Abs.Core.Simulation
import Exec.Spec.MemorySize
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

def memorySize (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match f.module.MEMS[0]? with
  | none => .stuck
  | some address => match s.store.MEMS[address]? with
    | none => .stuck
    | some object => advance s {f with code := after, vals := f.vals ++ [integerVal .I32 (object.BYTES.length / 65536)]} rest

theorem memory_pages_aligned {s : store} (contents : StoreContentsTyped s) {object : meminst}
    (member : object ∈ s.MEMS) : object.BYTES.length % 65536 = 0 := by
  have typed := contents.memories object member
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length _ wf typeWf =>
    dsimp only
    rw [length]
    simp [Ki]

theorem memorySize_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_SIZE :: after} :: rest,[]⟩) :
    ∃ next, memorySize ⟨s,ambient,{f with code := .MEMORY_SIZE :: after} :: rest,[]⟩ f rest after = .next next ∧
      CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := .MEMORY_SIZE :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .MEMORY_SIZE :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_size _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes
    have sizeBound : object.BYTES.length / 65536 < 2^32 := by
      have bound := memory_pages_bound typed.contents (List.mem_of_getElem? found)
      omega
    have resultTyped := integer_val_typed typed.typed.store .I32 (object.BYTES.length / 65536) sizeBound
    have freshFrame := continuation [integerVal .I32 (object.BYTES.length / 65536)] (.cons resultTyped .nil)
    have actualFrame : FrameTyped s {f with code := after,vals := f.vals ++ [integerVal .I32 (object.BYTES.length / 65536)]} [] := by
      simpa only [split,List.append_nil] using freshFrame
    refine ⟨_,by simp only [memorySize,mapped,found,advance],
      ⟨active_frame_preservation typed.typed actualFrame rfl,typed.contents⟩,NextSim.single ?_⟩
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
    have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
      simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
    have aligned := memory_pages_aligned typed.contents (List.mem_of_getElem? found)
    have source := Spec.memory_size_step s f.toFrame typed.typed.store frameWf
      (by simpa only [memoryEq] using aligned) (by simpa only [memoryEq] using sizeBound)
    rw [memoryEq] at source
    have height : ∀ label ∈ f.labels, label.height ≤ f.vals.length := by simpa only [split,List.append_nil] using heights
    have full := mutable_stack_simulation s s ambient f rest .MEMORY_SIZE after f.vals []
      [integerVal .I32 (object.BYTES.length / 65536)] typed.typed.ambient labelsWf valuesWf tailWf restWf height
      (by simpa [vals,admininstr_val,integerVal,Segment.i32,numtype_Inn,admininstr_instr] using source)
    simpa only [List.append_nil] using full

end Exec.Abs.Stateful
