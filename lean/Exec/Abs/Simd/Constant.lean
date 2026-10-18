import Exec.Abs.Simd.Invariants

namespace Exec.Abs.Simd
open SpecExt Exec.Spec Ownership

def constant (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) (value : vec_) : AState :=
  ⟨s.store,s.ambient,{f with code := after, vals := f.vals ++ [.VCONST .V128 value]} :: rest,[]⟩

theorem constant_frame_preservation {s : store} {f : AFrame} {after : List instr}
    {value : vec_} (storeWf : wf_store s)
    (typed : FrameTyped s {f with code := .VCONST .V128 value :: after} []) :
    FrameTyped s {f with code := after, vals := f.vals ++ [.VCONST .V128 value]} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns code contextWf =>
    have instructionWf := codeStack_wf code (.VCONST .V128 value) (by simp)
    have resultWf : wf_val (.VCONST .V128 value) := by
      cases instructionWf
      constructor <;> assumption
    simp only [List.append_nil] at code
    obtain ⟨prefixTypes, ins, outs, instruction, stack, continuation⟩ :=
      codeStack_after (value_types_concrete f.vals) code
    cases instruction
    simp only [List.append_nil] at stack
    have resultTyped := Val_ok.vectype s .V128 value storeWf resultWf
    apply FrameTyped.mk (f := {f with code := after, vals := f.vals ++ [.VCONST .V128 value]}) C
      bindings localTypes locals ?_ returns ?_ contextWf
    · simpa [ResultsTyped,List.map_append,valueType,valtype_vectype] using
        List.rel_append values (List.Forall₂.cons resultTyped List.Forall₂.nil)
    · simpa [List.map_append,valueType,stack] using continuation

theorem constant_typed {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {value : vec_}
    (typed : CoreTyped ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩) :
    CoreTyped (constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩ f rest after value) := by
  have hf : FrameTyped s {f with code := .VCONST .V128 value :: after} [] := by
    cases typed.typed.frames with | cons h _ => exact h
  exact ⟨active_frame_preservation typed.typed (constant_frame_preservation typed.typed.store hf) rfl,typed.contents⟩

theorem constant_simulation {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {value : vec_}
    (typed : ATyped ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩) :
    NextSim ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩
      (constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩ f rest after value) := by
  have hf : FrameTyped s {f with code := .VCONST .V128 value :: after} [] := by
    cases typed.frames with | cons h _ => exact h
  have heights := frameTyped_heights hf
  apply Or.inl
  constructor
  · simp only [constant,decode,decodeFrames,vals,List.map_nil,List.nil_append,
      AFrame.toFrame,List.map_cons,admininstr_instr]
    rw [decodeLabels_move_values _ _ _ _ heights]
    rfl
  · simp [constant,administrativeMeasure]

theorem constant_owned {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {value : vec_} {bounds}
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩) :
    StatefulOwned bounds (constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩ f rest after value) := by
  refine ⟨⟨valuesOwned_nil _,?_⟩,owned.heap⟩
  intro item member
  simp only [constant,List.mem_cons] at member
  rcases member with rfl | member
  · have active := owned.values.2 _ (List.mem_cons_self ..)
    exact ⟨active.1,valuesOwned_append.mpr ⟨active.2,by simp [ValuesOwned,ValueOwned]⟩⟩
  · exact owned.values.2 item (List.mem_cons_of_mem _ member)

theorem constant_bound {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {after : List instr} {value : vec_} {bound}
    (bounded : CodeBound bound ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩) :
    CodeBound bound (constant ⟨s,ambient,{f with code := .VCONST .V128 value :: after} :: rest,[]⟩ f rest after value) := by
  apply bound_replace_frame bounded
  have active := bounded.frames _ (List.mem_cons_self ..)
  refine ⟨?_,active.2⟩
  have size : sizeOf after < sizeOf (instr.VCONST .V128 value :: after) := by simp
  exact Nat.le_trans (Nat.le_of_lt size) active.1

end Exec.Abs.Simd
