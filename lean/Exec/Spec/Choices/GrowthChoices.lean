import Exec.Spec.MemoryGrowth

/-! Allocation-dependent Wasm growth is a source choice. It is separate from
compiler allocation failure and invocation resource exhaustion. Refusal is
always permitted; success must satisfy the independent generated grow rule. -/
namespace Exec.Spec
open SpecExt

abbrev MemoryGrowthChoices := Nat → meminst → Nat → Option meminst
abbrev TableGrowthChoices := Nat → tableinst → Nat → ref → Option tableinst

def MemoryGrowthChoices.Admissible (choices : MemoryGrowthChoices) : Prop :=
  ∀ occurrence before delta after, choices occurrence before delta = some after →
    fun_growmemory before delta (some after)

def TableGrowthChoices.Admissible (choices : TableGrowthChoices) : Prop :=
  ∀ occurrence before delta value after, choices occurrence before delta value = some after →
    fun_growtable before delta value (some after)

private theorem replace_memory_wf (s : store) (address : Nat) (next : meminst)
    (old : wf_store s) (fresh : wf_meminst next) :
    wf_store {s with MEMS := s.MEMS.modify address (fun _ => next)} := by
  cases old
  constructor <;> first | assumption | exact Segment.forall_modify _ _ _ _ (by assumption) (fun _ _ => fresh)

private theorem replace_table_wf (s : store) (address : Nat) (next : tableinst)
    (old : wf_store s) (fresh : wf_tableinst next) :
    wf_store {s with TABLES := s.TABLES.modify address (fun _ => next)} := by
  cases old
  constructor <;> first | assumption | exact Segment.forall_modify _ _ _ _ (by assumption) (fun _ _ => fresh)

def memoryGrowthOutput (s : store) (f : frame) : Option meminst → config
  | none => ⟨⟨s,f⟩,[Segment.i32 (2^32-1)]⟩
  | some next => ⟨⟨{s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun _ => next)},f⟩,
      [Segment.i32 ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536)]⟩

def tableGrowthOutput (s : store) (f : frame) (index : Nat) : Option tableinst → config
  | none => ⟨⟨s,f⟩,[Segment.i32 (2^32-1)]⟩
  | some next => ⟨⟨{s with TABLES := s.TABLES.modify f.MODULE.TABLES[index]! (fun _ => next)},f⟩,
      [Segment.i32 (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length]⟩

/-- An independently admissible memory choice takes the ordinary source step;
refusal returns the Wasm failure sentinel, rather than an API resource error. -/
theorem memory_growth_choice_erases (choices : MemoryGrowthChoices)
    (admissible : choices.Admissible) (occurrence : Nat) (s : store) (f : frame) (delta : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (deltaBound : delta < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length)
    (bounded : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536 < 2^32) :
    StepH ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
      (memoryGrowthOutput s f (choices occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta)) := by
  generalize selected : choices occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta = reply
  cases reply with
  | none => exact memory_grow_fail_step s f delta storeWf frameWf deltaBound
  | some next =>
    have grown := admissible _ _ _ _ selected
    have fresh : wf_meminst next := by cases grown; assumption
    exact memory_grow_success_step s f delta next storeWf frameWf deltaBound mapped bounded grown
      (replace_memory_wf _ _ _ storeWf fresh)

/-- Table growth uses the same explicit independent success/refusal boundary. -/
theorem table_growth_choice_erases (choices : TableGrowthChoices)
    (admissible : choices.Admissible) (occurrence : Nat) (s : store) (f : frame)
    (index delta : Nat) (value : ref)
    (storeWf : wf_store s) (frameWf : wf_frame f) (indexBound : index < 2^32) (deltaBound : delta < 2^32)
    (mapped : index < f.MODULE.TABLES.length)
    (bounded : (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32) :
    StepH ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
      (tableGrowthOutput s f index (choices occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value)) := by
  generalize selected : choices occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value = reply
  cases reply with
  | none => exact table_grow_fail_step s f index delta value storeWf frameWf indexBound deltaBound
  | some next =>
    have grown := admissible _ _ _ _ _ selected
    have fresh : wf_tableinst next := by cases grown; assumption
    exact table_grow_success_step s f index delta value next storeWf frameWf indexBound deltaBound mapped bounded grown
      (replace_table_wf _ _ _ storeWf fresh)

/-- Refusal needs no successful lookup or old-size bound. The additional
premises are required only when the independent policy selects success. -/
theorem memory_growth_choice_erases_conditional (choices : MemoryGrowthChoices)
    (admissible : choices.Admissible) (occurrence : Nat) (s : store) (f : frame) (delta : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (deltaBound : delta < 2^32)
    (mapped : choices occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta ≠ none → 0 < f.MODULE.MEMS.length)
    (bounded : choices occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta ≠ none →
      (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536 < 2^32) :
    StepH ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
      (memoryGrowthOutput s f (choices occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta)) := by
  by_cases refused : choices occurrence (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta = none
  · rw [refused]
    exact memory_grow_fail_step s f delta storeWf frameWf deltaBound
  · exact memory_growth_choice_erases choices admissible occurrence s f delta storeWf frameWf deltaBound
      (mapped refused) (bounded refused)

theorem table_growth_choice_erases_conditional (choices : TableGrowthChoices)
    (admissible : choices.Admissible) (occurrence : Nat) (s : store) (f : frame)
    (index delta : Nat) (value : ref)
    (storeWf : wf_store s) (frameWf : wf_frame f) (indexBound : index < 2^32) (deltaBound : delta < 2^32)
    (mapped : choices occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value ≠ none → index < f.MODULE.TABLES.length)
    (bounded : choices occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value ≠ none →
      (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32) :
    StepH ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
      (tableGrowthOutput s f index (choices occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value)) := by
  by_cases refused : choices occurrence (fun_table ⟨s,f⟩ (.mk_uN index)) delta value = none
  · rw [refused]
    exact table_grow_fail_step s f index delta value storeWf frameWf indexBound deltaBound
  · exact table_growth_choice_erases choices admissible occurrence s f index delta value
      storeWf frameWf indexBound deltaBound (mapped refused) (bounded refused)

/-- Refusing every growth request is an admissible source allocation policy. -/
theorem refuse_memory_growth_admissible :
    MemoryGrowthChoices.Admissible (fun _ _ _ => none) := by
  intro occurrence before delta after selected
  cases selected

theorem refuse_table_growth_admissible :
    TableGrowthChoices.Admissible (fun _ _ _ _ => none) := by
  intro occurrence before delta value after selected
  cases selected

end Exec.Spec
