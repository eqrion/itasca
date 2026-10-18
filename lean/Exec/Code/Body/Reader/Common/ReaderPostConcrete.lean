import Exec.Code.Body.Reader.Common.ReaderWasm1
import Exec.Code.Body.Reader.Common.ReaderWasm2
import Exec.Code.Local.Source.SourceStacks
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderPostWasm1.concrete {data env ctx bt st out instruction poly values}
    {p : Wasm1.Pending data env ctx bt st}
    (post : ReaderPostWasm1 p out instruction poly values)
    (before : ConcreteStack st.vals.val) (segment : ConcreteStack values) :
    ConcreteStack out.vals.val := by
  obtain ⟨_, outer, spine, _, _, _, _, stack⟩ := p.opened
  have outerKnown := (concreteStack_append.mp (stack ▸ before)).1
  obtain ⟨_, nextOuter, nextSpine, _, _, _, _, nextStack⟩ := post.opened
  have same : nextOuter = outer := (wasm1_spine_values nextSpine).trans (wasm1_spine_values spine).symm
  have valuesEq : out.vals.val = outer ++ values := by simpa only [same, Wasm1.Frames.Saved.advance] using nextStack
  exact valuesEq ▸ concreteStack_append.mpr ⟨outerKnown, segment⟩

theorem ReaderPostWasm2.concrete {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderPostWasm2 p out instruction poly values)
    (before : ConcreteStack st.core.vals.val) (segment : ConcreteStack values) :
    ConcreteStack out.vals.val := by
  obtain ⟨_, outer, spine, _, _, _, _, _, stack⟩ := p.opened
  have outerKnown := (concreteStack_append.mp (stack ▸ before)).1
  obtain ⟨_, nextOuter, nextSpine, _, _, _, _, _, nextStack⟩ := post.opened
  have same : nextOuter = outer := (wasm2_spine_values nextSpine).trans (wasm2_spine_values spine).symm
  have valuesEq : out.vals.val = outer ++ values := by simpa only [same, Wasm2.Frames.Saved.advance] using nextStack
  exact valuesEq ▸ concreteStack_append.mpr ⟨outerKnown, segment⟩
end Exec.Code
