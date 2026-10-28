import Itasca.Runtime.Equations
import Itasca.Stream.Source

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open runtime.compiler

/-- Region offsets come from the module scanner; they are ordered positions in
one immutable byte slice. -/
def SourceBounds (source : CompileSource) : Prop :=
  source.code_start.val ≤ source.code_end.val ∧ source.code_end.val ≤ source.bytes.length

def sourceEnvironment (source : CompileSource) := source.bytes.val.take source.code_start.val

def sourceCode (source : CompileSource) :=
  source.bytes.val.slice source.code_start.val source.code_end.val

def sourceTail (source : CompileSource) := source.bytes.val.drop source.code_end.val

@[step] theorem source_environment_spec (source : CompileSource) (h : SourceBounds source) :
    CompileSource.Insts.ItascaStreamSource.environment source ⦃ r =>
      ∃ bytes, r = .Ok bytes ∧ bytes.val = sourceEnvironment source ⦄ := by
  unfold CompileSource.Insts.ItascaStreamSource.environment
  simp only [SourceBounds] at h
  step*
  simp_all [sourceEnvironment]

@[step] theorem source_tail_spec (source : CompileSource) (h : SourceBounds source) :
    CompileSource.Insts.ItascaStreamSource.tail source ⦃ r =>
      ∃ bytes, r = .Ok bytes ∧ bytes.val = sourceTail source ⦄ := by
  unfold CompileSource.Insts.ItascaStreamSource.tail
  simp only [SourceBounds] at h
  step*
  simp_all [sourceTail]

@[step] theorem source_code_len_spec (source : CompileSource) (h : SourceBounds source) :
    CompileSource.Insts.ItascaStreamSource.code_len source ⦃ n =>
      n.val = source.code_end.val - source.code_start.val ⦄ := by
  unfold CompileSource.Insts.ItascaStreamSource.code_len
  simp only [SourceBounds] at h
  step*

@[step] theorem source_code_spec (source : CompileSource) (h : SourceBounds source)
    (first last : Usize) :
    CompileSource.Insts.ItascaStreamSource.code source first last ⦃ r => match r with
      | .Ok bytes => first.val ≤ last.val ∧ last.val ≤ (sourceCode source).length ∧
          bytes.val = (sourceCode source).slice first.val last.val
      | .Err e => e = .Host ∧
          (last.val < first.val ∨ (sourceCode source).length < last.val) ⦄ := by
  have hc : (sourceCode source).length = source.code_end.val - source.code_start.val := by
    simp only [sourceCode, List.slice_length]
    have := h.2
    change source.code_end.val ≤ source.bytes.val.length at this
    omega
  unfold CompileSource.Insts.ItascaStreamSource.code
  step*
  refine ⟨by scalar_tac, by scalar_tac, ?_⟩
  have hl : last.val - first.val ≤ (source.code_end.val - source.code_start.val) - first.val := by
    scalar_tac
  simp only [s_post, i1_post, i2_post, sourceCode, List.slice, List.drop_take,
    List.drop_drop, List.take_take]
  congr 1; omega


theorem source_code_length (source : CompileSource) (h : SourceBounds source) :
    (sourceCode source).length = source.code_end.val - source.code_start.val := by
  simp only [sourceCode, List.slice_length]
  have := h.2
  change source.code_end.val ≤ source.bytes.val.length at this
  omega

/-- These views reconstruct the same complete module bytes. -/
theorem source_recombine (source : CompileSource) (h : SourceBounds source) :
    sourceEnvironment source ++ sourceCode source ++ sourceTail source = source.bytes.val := by
  unfold sourceEnvironment sourceCode sourceTail List.slice
  rw [← List.take_add, Nat.add_sub_of_le h.1, List.take_append_drop]

theorem source_coherent (source : CompileSource) (h : SourceBounds source) :
    Itasca.StreamSource.Coherent CompileSource.Insts.ItascaStreamSource source
      (sourceEnvironment source) (sourceCode source) (sourceTail source) := by
  constructor
  · intro bytes hr
    have hs := source_environment_spec source h
    change CompileSource.Insts.ItascaStreamSource.environment source = _ at hr
    simp only [hr, WP.spec_ok] at hs
    obtain ⟨other, heq, hb⟩ := hs
    cases heq
    exact hb
  · intro len hr
    have hs := source_code_len_spec source h
    change CompileSource.Insts.ItascaStreamSource.code_len source = _ at hr
    simpa only [hr, WP.spec_ok, source_code_length source h] using hs
  · intro first last bytes _ _ hr
    have hs := source_code_spec source h first last
    change CompileSource.Insts.ItascaStreamSource.code source first last = _ at hr
    simp only [hr, WP.spec_ok] at hs
    exact hs.2.2
  · intro bytes hr
    have hs := source_tail_spec source h
    change CompileSource.Insts.ItascaStreamSource.tail source = _ at hr
    simp only [hr, WP.spec_ok] at hs
    obtain ⟨other, heq, hb⟩ := hs
    cases heq
    exact hb

theorem source_available (source : CompileSource) (h : SourceBounds source) :
    Itasca.StreamSource.Available CompileSource.Insts.ItascaStreamSource source
      (sourceEnvironment source) (sourceCode source) (sourceTail source) := by
  constructor
  · obtain ⟨_, hr, bytes, rfl, hb⟩ := WP.spec_imp_exists (source_environment_spec source h)
    exact ⟨bytes, hr, hb⟩
  · obtain ⟨len, hr, hb⟩ := WP.spec_imp_exists (source_code_len_spec source h)
    exact ⟨len, hr, by simpa only [source_code_length source h] using hb⟩
  · intro first last horder hbound
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (source_code_spec source h first last)
    cases r with
    | Ok bytes => exact ⟨bytes, hr, hp.2.2⟩
    | Err e => simp only at hp; omega
  · obtain ⟨_, hr, bytes, rfl, hb⟩ := WP.spec_imp_exists (source_tail_spec source h)
    exact ⟨bytes, hr, hb⟩

/-- Invalid read ranges return an ordinary source error; valid bounds suffice
for every callback to return without a modeled panic or divergence. -/
theorem source_callbacks_total (source : CompileSource) (h : SourceBounds source) :
    Itasca.StreamSource.CallbacksTotal CompileSource.Insts.ItascaStreamSource source := by
  constructor
  · obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (source_environment_spec source h)
    exact ⟨r, hr⟩
  · obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (source_code_len_spec source h)
    exact ⟨r, hr⟩
  · intro first last
    obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (source_code_spec source h first last)
    exact ⟨r, hr⟩
  · obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (source_tail_spec source h)
    exact ⟨r, hr⟩

end Itasca.Runtime.Code
