import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Sim.Host

/-!
Sections, each formerly its own module: Bound, MemoryAccess, Correct, Extension, Terminal, PositiveControl, MemoryPositive, SelectPositive.
-/

/-! ## Bound -/

section

namespace Itasca.Runtime.SourceMachine.Core

/-- Code bounds depend on function bodies and frame continuations, so changing
only source object contents retains them. -/
theorem code_bound_store {bound : Nat} {s : AState} {target : _root_.store}
    (bounded : CodeBound bound s) (functions : target.FUNCS = s.store.FUNCS) :
    CodeBound bound {s with store := target} :=
  ⟨bounded.positive,bounded.frames,by simpa only [functions] using bounded.functions⟩

theorem advance_content_bound {bound : Nat} {s target : _root_.store} {ambient : frame}
    {f f' : AFrame} {rest : List AFrame} {next : AState}
    (bounded : CodeBound bound ⟨s,ambient,f::rest,[]⟩)
    (step : advance ⟨target,ambient,f::rest,[]⟩ f' rest = .next next)
    (functions : target.FUNCS = s.FUNCS) (frame : FrameCodeBound bound f') : CodeBound bound next :=
  advance_bound (code_bound_store (target := target) bounded functions) step frame

theorem instruction_bound (bound : Nat) (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreHead op) (typed : FrameTyped s {f with code := op::after} [])
    (bounded : CodeBound bound ⟨s,ambient,{f with code := op::after}::rest,[]⟩)
    (step : instruction s ambient f rest op after = .next next) : CodeBound bound next := by
  have hf := bounded.frames {f with code := op::after} (by simp)
  have ha : sizeOf after ≤ bound := by have hh := hf.1; simp at hh; omega
  have hl := hf.2
  cases covered with
  | pure pure =>
    rw [instruction_slice s ambient f rest op after pure typed] at step
    exact SourceMachine.instruction_bound bound s ambient f rest op after next pure bounded step
  | const ty value => exact advance_bound bounded step ⟨ha,hl⟩
  | select =>
    simp only [instruction,select] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha,hl⟩
  | global_get index =>
    cases index
    simp only [instruction,globalGet] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha,hl⟩
  | global_set index =>
    cases index
    simp only [instruction,globalSet] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_content_bound bounded step rfl ⟨ha,hl⟩
  | load descriptor argument =>
    rw [instruction_load] at step
    simp only [load] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_bound bounded step ⟨ha,hl⟩
  | store descriptor argument =>
    rw [instruction_store] at step
    simp only [store] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_content_bound bounded step rfl ⟨ha,hl⟩

end Itasca.Runtime.SourceMachine.Core

end

/-! ## MemoryAccess -/

section

/-!
Scalar source memory load/store safety and simulation under typed, bounded operands.
-/

/-! ## Memory Load -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

/-- A typed scalar load either produces the value prescribed by the generated
memory rule, or takes a positive source reduction sequence to the bounds trap. -/
theorem load_progress (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Load) (argument : memarg)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    (∃ next, load ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
      f rest after op argument = .next next ∧ CoreTyped next ∧
      StepH (decode ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) [] (decode next)) ∨
    (load ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
      f rest after op argument = .trap ∧ ∃ n, 0 < n ∧
      StepsHN n (decode ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have frameTyped : FrameTyped s {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,split,operandTypes,frontWf,heights⟩ :=
    frame_typed_operands_bounds frameTyped
  obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
  obtain ⟨memoryAddress,object,mapped,found⟩ := bindings.memory_lookup present
  cases operandTypes with
  | cons addressTyped tail =>
    cases tail
    obtain ⟨bits,rfl,bitsBound⟩ := integer_val_inv (ty := .I32) addressTyped
    have decoded : integer .I32 (integerVal .I32 bits) = some bits := by
      simpa only [numtype_Inn] using integer_accepts .I32 bits bitsBound
    obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
    have operationWf := wf_admininstr_instr (codeWf (op.source argument) (by simp))
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by
      cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have objectTyped := typed.contents.memories object (List.mem_of_getElem? found)
    have bytesWf : Forall wf_byte object.BYTES := by
      cases objectTyped with
      | mk_Meminst_ok _ _ _ _ _ _ wf _ => cases wf; assumption
    have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
      simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
    have source := op.source_step s f.toFrame argument bits typed.typed.store frameWf bitsBound operationWf
      (by simpa only [memoryEq] using bytesWf)
    rw [memoryEq] at source
    by_cases inside : bits + proj_uN_0 argument.OFFSET + op.bytes ≤ object.BYTES.length
    · let payload := (object.BYTES.drop (bits + proj_uN_0 argument.OFFSET)).take op.bytes
      have payloadWf : Forall wf_byte payload := by
        intro byte member
        exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
      have payloadLength : payload.length = op.bytes := by
        simp only [payload,List.length_take,List.length_drop]
        omega
      have resultWf := op.value_wf payload payloadWf payloadLength
      have resultTyped : Val_ok s (op.value payload) (valtype_numtype op.type) := by
        cases op <;> exact .numtype _ _ _ typed.typed.store resultWf
      obtain ⟨_,_,_,_,continuation⟩ := memory_load_frame_continuation op argument
        (by simpa only [split] using frameTyped) resultTyped
      have fresh := active_frame_preservation typed.typed continuation rfl
      let next : AState := ⟨s,ambient,{f with code := after, vals := front ++ [op.value payload]} :: rest,[]⟩
      apply Or.inl
      refine ⟨next,?_,⟨fresh,typed.contents⟩,?_⟩
      · simp only [load,split,pop_append,mapped,decoded,found,inside,ite_true,advance,next,payload]
      · simp only [inside,ite_true] at source
        have full := mutable_stack_simulation s s ambient f rest (op.source argument) after front
          [integerVal .I32 bits] [op.value payload] typed.typed.ambient labelsWf frontWf tailWf restWf heights
          (by simpa [vals,admininstr_val,integerVal,Spec.Segment.i32,numtype_Inn,payload] using source)
        simpa only [split,next] using full
    · apply Or.inr
      refine ⟨?_,?_⟩
      · simp only [load,split,pop_append,mapped,decoded,found,inside,ite_false]
      · simp only [inside,ite_false] at source
        have full := operand_trap_simulation s ambient f rest (op.source argument) after front
          [integerVal .I32 bits] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
          (by simpa [vals,admininstr_val,integerVal,Spec.Segment.i32,numtype_Inn] using source)
        simpa only [split] using full

end Itasca.Runtime.SourceMachine.Core

end

/-! ## Memory Store -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

theorem numeric_value_inv {s : _root_.store} {value : val} {ty : numtype}
    (typed : Val_ok s value (valtype_numtype ty)) :
    ∃ number, value = .CONST ty number ∧ wf_num_ ty number := by
  have wf := val_ok_wf typed
  have ht := value_type_of_typed typed
  cases wf with
  | val_case_0 nt number valid =>
    have same : nt = ty := by cases nt <;> cases ty <;> simp_all [valueType,valtype_numtype]
    subst nt
    exact ⟨number,rfl,valid⟩
  | val_case_1 vt bits _ => cases ty <;> simp_all [valueType,valtype_numtype]
  | val_case_2 rt => cases ty <;> cases rt <;> simp_all [valueType,valtype_numtype,valtype_reftype]
  | val_case_3 address => cases ty <;> simp_all [valueType,valtype_numtype]
  | val_case_4 address => cases ty <;> simp_all [valueType,valtype_numtype]

/-- Scalar stores update only an in-bounds payload and retain full source
store/frame typing; an out-of-bounds write reaches the generated trap. -/
theorem store_progress (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Store) (argument : memarg)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    (∃ next, store ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
      f rest after op argument = .next next ∧ CoreTyped next ∧ Extend_store s next.store ∧
      StepH (decode ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) [] (decode next)) ∨
    (store ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
      f rest after op argument = .trap ∧ ∃ n, 0 < n ∧
      StepsHN n (decode ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) []
        ⟨⟨s,ambient⟩,[.TRAP]⟩) := by
  have frameTyped : FrameTyped s {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,split,operandTypes,frontWf,heights⟩ :=
    frame_typed_operands_bounds frameTyped
  obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
  obtain ⟨memoryAddress,object,mapped,found⟩ := bindings.memory_lookup present
  cases operandTypes with
  | cons addressTyped tail =>
    cases tail with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨bits,rfl,bitsBound⟩ := integer_val_inv (ty := .I32) addressTyped
      obtain ⟨number,rfl,numberWf⟩ := numeric_value_inv valueTyped
      have decoded : integer .I32 (integerVal .I32 bits) = some bits := by
        simpa only [numtype_Inn] using integer_accepts .I32 bits bitsBound
      obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
      have operationWf := wf_admininstr_instr (codeWf (op.source argument) (by simp))
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by
        cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
      have memoryEq : fun_mem ⟨s,f.toFrame⟩ (.mk_uN 0) = object := by
        simp [fun_mem,AFrame.toFrame,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
      have source := op.source_step s f.toFrame argument bits number typed.typed.store frameWf bitsBound operationWf numberWf
        (List.getElem?_eq_some_iff.mp mapped).1
      rw [memoryEq] at source
      have shape : f.vals = (front ++ [integerVal .I32 bits]) ++ [.CONST op.type number] := by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
      by_cases inside : bits + proj_uN_0 argument.OFFSET + op.bytes ≤ object.BYTES.length
      · obtain ⟨_,_,_,_,continuation⟩ := memory_store_frame_continuation op argument
          (by simpa only [split] using frameTyped)
        have extension := memory_payload_write_extends s f.toFrame memoryAddress
          (bits+proj_uN_0 argument.OFFSET) object (op.payload number) typed.typed.store typed.contents mapped found (op.payload_wf number)
        have contents := typed.contents.memory_write typed.typed.store f.toFrame memoryAddress
          (bits+proj_uN_0 argument.OFFSET) object (op.payload number) mapped found (op.payload_wf number)
        have old := active_frame_preservation typed.typed continuation rfl
        have fresh := old.extend_same extension rfl
        let next : AState := ⟨memoryPayloadWrite s f.toFrame (bits+proj_uN_0 argument.OFFSET) (op.payload number),ambient,
          {f with code := after, vals := front} :: rest,[]⟩
        apply Or.inl
        refine ⟨next,?_,⟨fresh,contents⟩,extension,?_⟩
        · simp only [store,shape,pop_append,mapped,ite_true,decoded,found,inside,advance,next]
        · simp only [inside,ite_true] at source
          have full := mutable_stack_simulation s next.store ambient f rest (op.source argument) after front
            [integerVal .I32 bits,.CONST op.type number] [] typed.typed.ambient labelsWf frontWf tailWf restWf heights
            (by simpa [vals,admininstr_val,integerVal,Spec.Segment.i32,numtype_Inn,next] using source)
          simpa only [split,next,List.append_nil] using full
      · apply Or.inr
        refine ⟨?_,?_⟩
        · simp only [store,shape,pop_append,mapped,ite_true,decoded,found,inside,ite_false]
        · simp only [inside,ite_false] at source
          have full := operand_trap_simulation s ambient f rest (op.source argument) after front
            [integerVal .I32 bits,.CONST op.type number] typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
            (by simpa [vals,admininstr_val,integerVal,Spec.Segment.i32,numtype_Inn] using source)
          simpa only [split] using full

end Itasca.Runtime.SourceMachine.Core

end

end

/-! ## Correct -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

/-- Every successful covered instruction preserves source store/frame typing
and has a counted source simulation (or the bounded constant stutter). -/
theorem instruction_correct (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) :
    CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ next := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | pure allowed =>
    rw [instruction_slice s ambient f rest _ after allowed frameTyped] at equation
    refine ⟨⟨Itasca.Runtime.SourceMachine.instruction_preservation s ambient f rest _ after next allowed typed.typed equation,?_⟩,
      Itasca.Runtime.SourceMachine.instruction_simulation s ambient f rest _ after next allowed typed.typed equation⟩
    simpa only [astep_store equation] using typed.contents
  | const ty value =>
    obtain ⟨actual,actualEq,fresh,simulation⟩ := constant_progress s ambient f rest after ty value typed
    rw [actualEq] at equation
    cases equation
    exact ⟨fresh,simulation⟩
  | select =>
    obtain ⟨actual,actualEq,fresh,simulation⟩ := select_progress s ambient f rest after typed
    change select _ _ _ _ = .next next at equation
    rw [actualEq] at equation
    cases equation
    exact ⟨fresh,.single simulation⟩
  | global_get index =>
    cases index with
    | mk_uN index =>
      obtain ⟨actual,actualEq,fresh,simulation⟩ := global_get_progress s ambient f rest index after typed
      change globalGet _ _ _ _ _ = .next next at equation
      rw [actualEq] at equation
      cases equation
      exact ⟨fresh,.single simulation⟩
  | global_set index =>
    cases index with
    | mk_uN index =>
      obtain ⟨actual,actualEq,fresh,extension,simulation⟩ := global_set_progress s ambient f rest index after typed
      change globalSet _ _ _ _ _ = .next next at equation
      rw [actualEq] at equation
      cases equation
      exact ⟨fresh,.single simulation⟩
  | load op argument =>
    rw [instruction_load] at equation
    rcases load_progress s ambient f rest after op argument typed with
      ⟨actual,actualEq,fresh,simulation⟩ | ⟨actualEq,_⟩
    · rw [actualEq] at equation
      cases equation
      exact ⟨fresh,.single simulation⟩
    · rw [actualEq] at equation
      contradiction
  | store op argument =>
    rw [instruction_store] at equation
    rcases store_progress s ambient f rest after op argument typed with
      ⟨actual,actualEq,fresh,extension,simulation⟩ | ⟨actualEq,_⟩
    · rw [actualEq] at equation
      cases equation
      exact ⟨fresh,.single simulation⟩
    · rw [actualEq] at equation
      contradiction

theorem empty_correct (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := []} :: rest,[]⟩)
    (equation : astep ⟨s,ambient,{f with code := []} :: rest,[]⟩ = .next next) :
    CoreTyped next ∧ NextSim ⟨s,ambient,{f with code := []} :: rest,[]⟩ next := by
  have contents : StoreContentsTyped next.store := by simpa only [astep_store equation] using typed.contents
  cases f with
  | mk address resultTypes locals module labels code values =>
    let frame : AFrame := ⟨address,resultTypes,locals,module,labels,[],values⟩
    have frameTyped : FrameTyped s frame [] := by
      cases typed.typed.frames with | cons head _ => exact head
    cases labels with
    | nil =>
      have valuesTyped := frame_end_typed (f := frame) frameTyped
      change ResultsTyped s resultTypes values at valuesTyped
      have count := results_typed_length valuesTyped
      have returned : ResultsTyped s resultTypes (values.drop (values.length-resultTypes.length)) := by
        simpa only [count,Nat.sub_self,List.drop_zero] using valuesTyped
      exact ⟨⟨return_frame_preservation typed.typed returned equation,contents⟩,
        .single (typed_frame_end_simulation s ambient frame rest next typed.typed equation)⟩
    | cons label labels =>
      have simulation := typed_label_end_simulation s ambient frame rest label labels next typed.typed equation
      refine ⟨⟨?_,contents⟩,simulation⟩
      simp only [astep] at equation
      split at equation
      · simp only [advance,AResult.next.injEq] at equation
        rw [← equation]
        exact active_frame_preservation typed.typed (label_exit_frame_preservation (f := frame) frameTyped) rfl
      · contradiction

end Itasca.Runtime.SourceMachine.Core

end

/-! ## Extension -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

theorem instruction_extends (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .next next) : Extend_store s next.store := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  have unchanged (same : next.store = s) : Extend_store s next.store := by
    rw [same]
    exact extend_store_refl s typed.typed.store
  cases covered with
  | pure pure =>
    rw [instruction_slice s ambient f rest _ after pure frameTyped] at equation
    exact unchanged (astep_store equation)
  | const ty value =>
    simp only [instruction,advance,AResult.next.injEq] at equation
    cases equation
    exact unchanged rfl
  | select =>
    apply unchanged
    simp only [instruction,select] at equation
    repeat' first | contradiction | split at equation
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      rfl
  | global_get index =>
    apply unchanged
    cases index
    simp only [instruction,globalGet] at equation
    repeat' first | contradiction | split at equation
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      rfl
  | global_set index =>
    cases index with
    | mk_uN index =>
      obtain ⟨actual,actualEq,_,extension,_⟩ := global_set_progress s ambient f rest index after typed
      change globalSet _ _ _ _ _ = .next next at equation
      rw [actualEq] at equation
      cases equation
      exact extension
  | load descriptor argument =>
    apply unchanged
    rw [instruction_load] at equation
    simp only [load] at equation
    repeat' first | contradiction | split at equation
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      rfl
  | store descriptor argument =>
    rw [instruction_store] at equation
    rcases store_progress s ambient f rest after descriptor argument typed with
      ⟨actual,actualEq,_,extension,_⟩ | ⟨actualEq,_⟩
    · rw [actualEq] at equation
      cases equation
      exact extension
    · rw [actualEq] at equation
      contradiction

end Itasca.Runtime.SourceMachine.Core

end

/-! ## Terminal -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

/-- Core traps are generated source traps: integer exceptional arithmetic,
explicit unreachable, and scalar memory bounds failures. -/
theorem instruction_trap (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : CoreHead op)
    (typed : CoreTyped ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩)
    (equation : instruction s ambient f rest op after = .trap) :
    ∃ n, 0 < n ∧ StepsHN n (decode ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  have frameTyped : FrameTyped s {f with code := op :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  cases covered with
  | pure pure =>
    rw [instruction_slice s ambient f rest _ after pure frameTyped] at equation
    rcases instruction_trap_eq s ambient f rest _ after pure equation with rfl | ⟨descriptor,rfl⟩
    · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
      have restWf : Forall FrameWf rest := by
        cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
      exact unreachable_simulation s ambient f rest after typed.typed.store typed.typed.ambient
        frameWf labelsWf valuesWf (fun i member => codeWf i (by simp [member])) restWf
    · exact Numeric.astep_trap_simulation s ambient f rest after descriptor typed.typed equation
  | const ty value => simp [instruction,advance] at equation
  | select =>
    obtain ⟨next,actual,_,_⟩ := select_progress s ambient f rest after typed
    change select _ _ _ _ = .trap at equation
    rw [actual] at equation
    contradiction
  | global_get index =>
    cases index with
    | mk_uN index =>
      obtain ⟨next,actual,_,_⟩ := global_get_progress s ambient f rest index after typed
      change globalGet _ _ _ _ _ = .trap at equation
      rw [actual] at equation
      contradiction
  | global_set index =>
    cases index with
    | mk_uN index =>
      obtain ⟨next,actual,_,_,_⟩ := global_set_progress s ambient f rest index after typed
      change globalSet _ _ _ _ _ = .trap at equation
      rw [actual] at equation
      contradiction
  | load descriptor argument =>
    rw [instruction_load] at equation
    rcases load_progress s ambient f rest after descriptor argument typed with ⟨next,actual,_,_⟩ | ⟨actual,source⟩
    · rw [actual] at equation
      contradiction
    · exact source
  | store descriptor argument =>
    rw [instruction_store] at equation
    rcases store_progress s ambient f rest after descriptor argument typed with ⟨next,actual,_,_,_⟩ | ⟨actual,source⟩
    · rw [actual] at equation
      contradiction
    · exact source

end Itasca.Runtime.SourceMachine.Core

end

/-! ## PositiveControl -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem typed_loop_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (body : List instr)
    (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ = .next next) :
    StepH (decode ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, _, hc⟩ := frame_typed_wf hf
    obtain ⟨C, first, args, inputs, outputs, bindings, _, hop, hsplit, hargs, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop with
    | loop _ _ _ ins outs hbt hbody hC hi hnew =>
      have hbt' := block_type_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
      have hlen := results_typed_length hargs
      have htypes := results_type_of_typed hargs
      have hheight : f.vals.length - inputs.length = first.length := by rw [hsplit, List.length_append, hlen]; omega
      have hbound : inputs.length ≤ f.vals.length := by rw [hsplit, List.length_append, hlen]; omega
      have htail : (f.vals.drop (f.vals.length - inputs.length)).map valueType = inputs := by
        rw [hheight, hsplit, List.drop_left]
        exact htypes
      have result := loop_simulation s ambient f rest after body first args bt inputs outputs
        typed.store typed.ambient hw hl hfirst (results_typed_wf hargs)
        (fun i hm => hc i (by simp [hm])) (frames_typed_wf hr) heights hi
        (block_type_spec s f bt _ hbt') hlen
      have hnext : next = ⟨s, ambient,
          { f with code := body, labels := ⟨inputs, outputs, [.LOOP bt body], first.length, after⟩ :: f.labels } :: rest, []⟩ := by
        simpa [astep, enterLabel, hbt', hbound, htail, hheight, hsplit, hlen, htypes, advance] using step.symm
      rw [hnext]
      simpa only [← hsplit] using result

theorem typed_if_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (yes no : List instr) (next : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩) [] (decode next) := by
  have hf : FrameTyped s { f with code := .IFELSE bt yes no :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact frames_typed_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frame_typed_wf hf
  have hafter : Forall wf_instr after := fun i hm => hc i (by simp [hm])
  have hi : wf_instr (.IFELSE bt yes no) := hc (.IFELSE bt yes no) (by simp)
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
  cases hop
  obtain ⟨args, conditions, rfl, hargs, hcond⟩ := results_typed_split hoperands
  cases hcond with
  | cons hvalue hend =>
    cases hend
    obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hvalue
    have hbits : integer .I32 (integerVal .I32 bits) = some bits := integer_accepts .I32 bits hb
    have hvals : f.vals = (first ++ args) ++ [integerVal .I32 bits] := by simpa only [List.append_assoc] using hsplit
    simp only [astep, hvals, pop_append, hbits, advance, AResult.next.injEq] at step
    rw [← step]
    have result := if_simulation s ambient f rest after (first ++ args) bits bt yes no
      typed.store typed.ambient hw hl (forall_append hfirst (results_typed_wf hargs)) hafter hr
      (by intro label hm; have hh := heights label hm; simp only [List.length_append]; omega) hb hi
    simpa only [← hvals] using result

theorem typed_br_if_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (depth : Nat) (next : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩) [] (decode next) := by
  have hf : FrameTyped s { f with code := .BR_IF (.mk_uN depth) :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact frames_typed_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frame_typed_wf hf
  have hafter : Forall wf_instr after := fun i hm => hc i (by simp [hm])
  have hi : wf_instr (.BR_IF (.mk_uN depth)) := hc (.BR_IF (.mk_uN depth)) (by simp)
  have hi32 : depth < 2 ^ 32 := by
    cases hi with
    | instr_case_8 _ hu => cases hu with
      | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
  cases hop
  obtain ⟨args, conditions, rfl, hargs, hcond⟩ := results_typed_split hoperands
  cases hcond with
  | cons hvalue hend =>
    cases hend
    obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hvalue
    have hbits : integer .I32 (integerVal .I32 bits) = some bits := integer_accepts .I32 bits hb
    have hvals : f.vals = (first ++ args) ++ [integerVal .I32 bits] := by simpa only [List.append_assoc] using hsplit
    simp only [astep, hvals, pop_append, hbits, advance, AResult.next.injEq] at step
    rw [← step]
    have result := br_if_simulation s ambient f rest after (first ++ args) bits depth
      typed.store typed.ambient hw hl (forall_append hfirst (results_typed_wf hargs)) hafter hr
      (by intro label hm; have hh := heights label hm; simp only [List.length_append]; omega) hb hi32
    simpa only [← hvals] using result

end Itasca.Runtime.SourceMachine

end

/-! ## MemoryPositive -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt
theorem load_step_positive (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Load) (argument : memarg) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩) [] (decode next) := by
  simp only [step] at equation
  rw [instruction_load] at equation
  rcases load_progress s ambient {f with code := op.source argument::after} rest after op argument typed with
    ⟨actual,actualEq,fresh,simulation⟩ | ⟨actualEq,_⟩
  · rw [actualEq] at equation
    cases equation
    exact simulation
  · rw [actualEq] at equation
    contradiction

theorem store_step_positive (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Store) (argument : memarg) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩)
    (equation : step ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := op.source argument::after}::rest,[]⟩) [] (decode next) := by
  simp only [step] at equation
  rw [instruction_store] at equation
  rcases store_progress s ambient {f with code := op.source argument::after} rest after op argument typed with
    ⟨actual,actualEq,fresh,extension,simulation⟩ | ⟨actualEq,_⟩
  · rw [actualEq] at equation
    cases equation
    exact simulation
  · rw [actualEq] at equation
    contradiction

end Itasca.Runtime.SourceMachine.Core

end

/-! ## SelectPositive -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt

theorem select_step_positive (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := .SELECT none::after}::rest,[]⟩)
    (step : step ⟨s,ambient,{f with code := .SELECT none::after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := .SELECT none::after}::rest,[]⟩) [] (decode next) := by
  obtain ⟨actual,actualEq,fresh,simulation⟩ := select_progress s ambient {f with code := .SELECT none::after} rest after typed
  change select _ _ _ _ = .next next at step
  rw [actualEq] at step
  cases step
  exact simulation
end Itasca.Runtime.SourceMachine.Core

end
