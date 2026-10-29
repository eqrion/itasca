import Itasca.Runtime.Compiler.Body.Reader.Control.KnownFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterStacks

/-!
Known operand fronts when entering a reader scope.

Main declarations: `ReaderEnterPostWasm2.known_fronts`. A direct consumer is `Compiler.Body.Reader.Control.EnterCompilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderEnterPostWasm2.known_fronts {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env .Wasm2 locals index st}
    (post : ReaderEnterPostWasm2 p out form bt ins outs remaining base)
    {parents current} (fronts : ReaderKnownFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (child : SourceScope)
    (live : child.entered = true → p.current.ctrl.polymorphic_base = false)
    (known : child.entered = true → ConcreteStack st.core.vals.val) :
    ReaderKnownFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.vals) := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply fronts.push child remaining
  intro entered
  obtain ⟨C, outer, spine, header, position, typed, controls, blocks, old⟩ := id p.opened
  have old' : st.core.vals.val = (p.parents.map Wasm2.Frames.Saved.vals).flatten ++ p.current.vals := by
    simpa only [wasm2_spine_values spine, List.flatMap_def] using old
  have knownParts := concrete_stack_append.mp (old' ▸ known entered)
  have transfer := post.popped
  rw [live entered] at transfer
  exact concrete_stack_append.mpr ⟨knownParts.1, concrete_stack_transfer knownParts.2 transfer⟩
end Itasca.Runtime.Compiler
