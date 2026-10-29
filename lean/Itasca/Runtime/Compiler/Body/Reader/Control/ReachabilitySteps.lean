import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeZipper
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrame
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability

/-!
Reader scope initialization and reachability preservation through advance, else and closure.
-/

/-! ## Reader Scope Initial -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderScopeZipperWasm2.initial (bt : signature.BlockType) (base : Usize)
    (ins outs : List types.ValueType) :
    ReaderScopeZipperWasm2 [] (SourceScope.initial (outs.map Translate.valueType)) []
      (Wasm2.Frames.Saved.fresh base .body bt ins outs) := by
  refine ⟨.nil, ?_⟩
  constructor
  · exact .body
  · rfl
  · rfl
  · rfl
end Itasca.Runtime.Code

end

/-! ## Reader Reachability Steps -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderReachabilityWasm2.advance {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm2 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (token : Wasm2.Token) (instruction : instr) (poly : Bool)
    (values : List code.StackType) (mono : nextReachable = true → poly = false) :
    ReaderReachabilityWasm2 nextReachable parents (current.advance instruction) savedParents
      (savedCurrent.advance token instruction poly values) :=
  invariant.change_current nextReachable _ _ rfl mono

theorem ReaderReachabilityWasm2.begin_else {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm2 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderReachabilityWasm2 nextReachable parents (current.begin_else bt condition yesExit noEntry normal)
      savedParents savedCurrent.nextElse :=
  invariant.change_current nextReachable _ _ rfl (fun _ => rfl)

theorem ReaderReachabilityWasm2.close {reachable parents parent child savedParents savedParent savedCurrent}
    (invariant : ReaderReachabilityWasm2 reachable (parents ++ [parent]) child
      (savedParents ++ [savedParent]) savedCurrent)
    (nextReachable : Bool) (instruction : instr)
    (entered : nextReachable = true → child.entered = true) :
    ReaderReachabilityWasm2 nextReachable parents (parent.advance instruction) savedParents
      (resumedSource savedParent savedCurrent instruction) :=
  invariant.pop nextReachable instruction _ rfl entered

end Itasca.Runtime.Code

end
