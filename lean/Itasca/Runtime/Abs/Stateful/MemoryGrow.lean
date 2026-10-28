import Itasca.Runtime.Abs.Stateful.GrowthTyping
import Itasca.Runtime.Abs.Stateful.ObjectReplacement
import Itasca.Runtime.Abs.Stateful.MemorySize
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

/-- Refusal is permitted independently of the pure successful-growth rule. -/
inductive MemoryGrowthChoice (before : meminst) (delta : Nat) : Option meminst → Prop
  | refused : MemoryGrowthChoice before delta none
  | grown {next} : fun_growmemory before delta (some next) → MemoryGrowthChoice before delta (some next)

def memoryGrow (choice : Option meminst) (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) : AResult :=
  match pop f.vals, f.module.MEMS[0]? with
  | some (front,value), some address => match integer .I32 value, s.store.MEMS[address]? with
    | some _, some object => match choice with
      | none => advance s {f with code := after,vals := front++[integerVal .I32 (2^32-1)]} rest
      | some next => advance {s with store := {s.store with MEMS := s.store.MEMS.set address next}}
          {f with code := after,vals := front++[integerVal .I32 (object.BYTES.length/65536)]} rest
    | _,_ => .stuck
  | _,_ => .stuck

theorem memoryGrow_choices (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩) :
    ∃ front delta address object,
      f.vals = front++[integerVal .I32 delta] ∧ f.module.MEMS[0]? = some address ∧ s.MEMS[address]? = some object ∧
      ∀ choice, MemoryGrowthChoice object delta choice →
      ∃ next, memoryGrow choice ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩ f rest after = .next next ∧
        CoreTyped next ∧ Extend_store s next.store ∧
        NextSim ⟨s,ambient,{f with code := .MEMORY_GROW::after}::rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .MEMORY_GROW::after} [] := by cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,inputs,outputs,bindings,locals,operation,split,operandTypes,frontWf,heights,continuation⟩ := frame_operands hf
  cases operation with
  | memory_grow _ type present selected contextWf typeWf instructionWf =>
    obtain ⟨address,object,mapped,found⟩ := bindings.memory_lookup present
    cases operandTypes with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨delta,rfl,deltaBound⟩ := integer_val_inv (ty:=.I32) valueTyped
      have decoded : integer .I32 (integerVal .I32 delta) = some delta := integer_accepts .I32 delta deltaBound
      refine ⟨front,delta,address,object,split,mapped,found,?_⟩
      intro choice allowed
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frameTyped_wf hf
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact framesTyped_wf tail
      cases allowed with
      | refused =>
        have resultTyped := integer_val_typed typed.typed.store .I32 (2^32-1) (by decide)
        have freshFrame := continuation [integerVal .I32 (2^32-1)] (.cons resultTyped .nil)
        refine ⟨_,by simp only [memoryGrow,split,pop_append,mapped,decoded,found,advance],
          ⟨active_frame_preservation typed.typed freshFrame rfl,typed.contents⟩,extend_store_refl _ typed.typed.store,NextSim.single ?_⟩
        have source := memory_grow_fail_step s f.toFrame delta typed.typed.store frameWf deltaBound
        have full := mutable_stack_simulation s s ambient f rest .MEMORY_GROW after front [integerVal .I32 delta]
          [integerVal .I32 (2^32-1)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
          (by simpa [AFrame.toFrame,vals,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
        simpa only [split] using full
      | @grown grownObject grown =>
        have objectTyped := typed.contents.memories object (List.mem_of_getElem? found)
        obtain ⟨newTyped,objectExtension⟩ := growmemory_typed objectTyped grown
        obtain ⟨extension,contents⟩ := memory_replacement_preserves s address object grownObject typed.typed.store typed.contents found objectExtension newTyped
        have bound : object.BYTES.length/65536 < 2^32 := by
          have := memory_pages_bound typed.contents (List.mem_of_getElem? found); omega
        have resultTyped := integer_val_typed typed.typed.store .I32 (object.BYTES.length/65536) bound
        have frameNext := continuation [integerVal .I32 (object.BYTES.length/65536)] (.cons resultTyped .nil)
        have fresh := (active_frame_preservation typed.typed frameNext rfl).extend_same extension rfl
        refine ⟨_,by simp only [memoryGrow,split,pop_append,mapped,decoded,found,advance],⟨fresh,contents⟩,extension,NextSim.single ?_⟩
        have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
          simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
        have storeEq : {s with MEMS := s.MEMS.modify f.module.MEMS[0]! (fun _ => grownObject)} =
            {s with MEMS := s.MEMS.set address grownObject} := by
          simp [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found]
        have source := memory_grow_success_step s f.toFrame delta grownObject typed.typed.store frameWf deltaBound
          (List.getElem?_eq_some_iff.mp mapped).1 (by simpa only [memoryEq] using bound)
          (by simpa only [memoryEq] using grown) (by simpa only [AFrame.toFrame,storeEq] using (extend_store_wf extension).2)
        rw [memoryEq] at source
        simp only [AFrame.toFrame,storeEq] at source
        have full := mutable_stack_simulation s {s with MEMS:=s.MEMS.set address grownObject} ambient f rest .MEMORY_GROW after front
          [integerVal .I32 delta] [integerVal .I32 (object.BYTES.length/65536)] typed.typed.ambient labelsWf frontWf tailWf restWf heights
          (by simpa [AFrame.toFrame,vals,integerVal,admininstr_val,numtype_Inn,admininstr_instr,Segment.i32] using source)
        simpa only [split] using full
end Itasca.Runtime.Abs.Stateful
