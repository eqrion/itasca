import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Relations.Common.EntryLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The exact saved operand segments, rather than only their slot widths,
identify the source front of a Wasm 1 child scope. -/
theorem ReaderEnterPostWasm1.scope_fronts {data env ctx bodyBt st out form bt remaining token}
    {p : Wasm1.Pending data env ctx bodyBt st}
    (post : ReaderEnterPostWasm1 p out form bt remaining token)
    {parents current} (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (child : SourceScope) (same : Sequence.stackTypes out.vals.val = child.front) :
    ReaderScopeFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.vals) := by
  have values := post.front.2.2
  have front : child.front = Sequence.stackTypes ((p.parents.map Wasm1.Frames.Saved.vals).flatten ++ remaining) := by
    simpa only [List.flatMap_def] using (same.symm.trans (congrArg Sequence.stackTypes values))
  simpa only [List.map_append, List.map_cons, List.map_nil] using fronts.push child remaining front

/-- The complete post-reader stack recovers a live Wasm 2 child front by
cancelling its exact translated parameter suffix. -/
theorem ReaderEnterPostWasm2.scope_fronts {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    (initial : form.Initial)
    {parents current} (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (child : SourceScope)
    (same : Sequence.stackTypes out.core.vals.val = child.front ++ ins.map Translate.valueType) :
    ReaderScopeFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.vals) := by
  have values := (post.front initial).2.2.2
  have equal : Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining) = child.front := by
    have appended : Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining) ++ ins.map Translate.valueType = child.front ++ ins.map Translate.valueType := by
      simpa only [values, Sequence.stackTypes, List.map_append, List.map_map, Function.comp_def] using same
    exact List.append_cancel_right appended
  have front : child.front = Sequence.stackTypes ((p.parents.map Wasm2.Frames.Saved.vals).flatten ++ remaining) := by
    simpa only [List.flatMap_def] using equal.symm
  simpa only [List.map_append, List.map_cons, List.map_nil] using fronts.push child remaining front

/-- A dormant Wasm 2 entry retains the exact saved prefix even when operand
popping used the polymorphic stack rule. -/
theorem ReaderEnterPostWasm2.scope_fronts_dormant {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    (initial : form.Initial)
    {parents current} (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (child : SourceScope)
    (same : child.front = Sequence.stackTypes (out.core.vals.val.take base.val)) :
    ReaderScopeFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.vals) := by
  have values := (post.front initial).2.2.1
  have front : child.front = Sequence.stackTypes ((p.parents.map Wasm2.Frames.Saved.vals).flatten ++ remaining) := by
    simpa only [List.flatMap_def] using same.trans (congrArg Sequence.stackTypes values)
  simpa only [List.map_append, List.map_cons, List.map_nil] using fronts.push child remaining front

end Exec.Code
