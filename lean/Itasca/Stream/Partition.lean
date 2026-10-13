import Itasca.Stream.Scheduler
import Itasca.Stream.Header

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler

variable {profile : ValidationProfile}

/-- Issued batches partition bytes and defined-function indices in submission
order. Worker completion order is deliberately absent from this relation. -/
inductive Partition (code : Slice U8) (env : module.Env) :
    Usize → Nat → List StreamBatch.Issued → Usize → Nat → Prop where
  | nil (pos : Usize) (func : Nat) : pos.val ≤ code.length →
      Partition code env pos func [] pos func
  | cons {pos func issued rest middle finish next} :
      issued.env = env → issued.code_offset = pos → issued.first_func.val = func →
      Wasm.BytesAt code pos issued.code.val middle →
      Partition code env middle (func + issued.num_funcs.val) rest finish next →
      Partition code env pos func (issued :: rest) finish next

theorem Partition.snoc {code env pos func history middle next issued finish}
    (h : Partition code env pos func history middle next)
    (henv : issued.env = env) (hoffset : issued.code_offset = middle)
    (hfunc : issued.first_func.val = next)
    (hbytes : Wasm.BytesAt code middle issued.code.val finish) :
    Partition code env pos func (history ++ [issued]) finish (next + issued.num_funcs.val) := by
  induction h with
  | nil => exact .cons henv hoffset hfunc hbytes (.nil _ _ hbytes.bound)
  | cons he ho hf hb _ ih => exact .cons he ho hf hb (ih hoffset hfunc hbytes)

/-- Assemble independent entry certificates in issuance order. The completion
premise is populated only by checked successful retirements. -/
theorem Partition.encoding {code env pos func history finish next}
    (h : Partition code env pos func history finish next)
    (hcompleted : ∀ issued ∈ history, Completed issued profile) :
    ∃ entries, next = func + entries.length ∧
      ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding profile)) code pos entries finish ∧
      ModuleCode.EntriesTyped (profile := profile) env func entries := by
  induction h with
  | nil pos func hbound =>
    exact ⟨[], by simp, ⟨[], .nil, Wasm.BytesAt.nil _ _ hbound⟩, .nil _⟩
  | @cons pos func issued rest middle finish next he ho hf hb hp ih =>
    obtain ⟨entries, hn, hr, ht⟩ := hcompleted issued (by simp)
    obtain ⟨restEntries, hnext, hrestBytes, hrestTyped⟩ := ih (fun issued hm => hcompleted issued (by simp [hm]))
    have hfirst : ModuleCode.EntriesTyped (profile := profile) env func entries := by simpa [he, hf] using ht
    refine ⟨entries ++ restEntries, ?_, ModuleCode.entries_at_append ⟨issued.code.val, hr, hb⟩ hrestBytes,
      hfirst.append (by simpa [hn] using hrestTyped)⟩
    simp only [List.length_append]
    omega

/-- A checked header plus the complete batch partition gives the padded code
region and the exact function/type pairing needed by semantic module assembly. -/
theorem Partition.code {code env entries history}
    (hheader : StreamFraming.HeaderAt code env entries)
    (h : Partition code env entries 0 history (Slice.len code) env.func_type_indices.val.length)
    (hcompleted : ∀ issued ∈ history, Completed issued profile) :
    ∃ codes, ModuleBinary.PaddedEncoding 10#u8
      (ModuleBinary.VecEncoding (Profile.CodeEncoding profile)) [] codes code.val ∧
      List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) env.func_type_indices.val codes := by
  obtain ⟨codes, hn, hb, ht⟩ := h.encoding hcompleted
  have hcount : codes.length = env.func_type_indices.val.length := by omega
  have htyped := ht.forall₂ (by omega)
  rcases hheader with ⟨hbytes, _, hfuncs⟩ | ⟨count, hs, _⟩
  · have hcodes : codes = [] := by simpa [hfuncs] using hcount
    refine ⟨codes, ?_, by simpa using htyped⟩
    simp only [hcodes, hbytes]
    exact ⟨[], [], .nil, .absent, rfl⟩
  · obtain ⟨bytes, he, hspan⟩ := ModuleCode.Section.encoding hs hb hcount
    have heq : code.val = bytes := by simpa using hspan.suffix
    exact ⟨codes, ⟨[], code.val, .nil, heq ▸ he, rfl⟩, by simpa using htyped⟩

end Itasca.StreamScheduler
