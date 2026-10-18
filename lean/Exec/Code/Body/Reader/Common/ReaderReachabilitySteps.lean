import Exec.Code.Body.Reader.Common.ReaderReachability
import Exec.Code.Body.Reader.Control.ReaderScopeInitial
namespace Exec.Code
open Aeneas Aeneas.Std Itasca


theorem ReaderReachabilityWasm1.advance {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm1 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (token : Wasm1.Token) (instruction : instr) (poly : Bool)
    (values : List code.StackType) (mono : nextReachable = true → poly = false) :
    ReaderReachabilityWasm1 nextReachable parents (current.advance instruction) savedParents
      (savedCurrent.advance token instruction poly values) :=
  invariant.change_current nextReachable _ _ rfl mono

theorem ReaderReachabilityWasm1.enter {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm1 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (child : SourceScope) (entered : child.entered = reachable)
    (remaining : List code.StackType) (state : code.OpIterState) (form : Wasm1.Frames.Form) (bt : code.BlockType) :
    ReaderReachabilityWasm1 nextReachable (parents ++ [current]) child
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Wasm1.Frames.Saved.fresh state form bt) :=
  invariant.push nextReachable child _ _ rfl (fun live => entered.symm.trans live) (fun _ => rfl)

theorem ReaderReachabilityWasm1.begin_else {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm1 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderReachabilityWasm1 nextReachable parents (current.begin_else bt condition yesExit noEntry normal)
      savedParents savedCurrent.nextElse :=
  invariant.change_current nextReachable _ _ rfl (fun _ => rfl)

theorem ReaderReachabilityWasm1.close {reachable parents parent child savedParents savedParent savedCurrent}
    (invariant : ReaderReachabilityWasm1 reachable (parents ++ [parent]) child
      (savedParents ++ [savedParent]) savedCurrent)
    (nextReachable : Bool) (instruction : instr)
    (entered : nextReachable = true → child.entered = true) :
    ReaderReachabilityWasm1 nextReachable parents (parent.advance instruction) savedParents
      (resumedSourceWasm1 savedParent savedCurrent instruction) :=
  invariant.pop nextReachable instruction _ rfl entered


theorem ReaderReachabilityWasm2.advance {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm2 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (token : Wasm2.Token) (instruction : instr) (poly : Bool)
    (values : List code.StackType) (mono : nextReachable = true → poly = false) :
    ReaderReachabilityWasm2 nextReachable parents (current.advance instruction) savedParents
      (savedCurrent.advance token instruction poly values) :=
  invariant.change_current nextReachable _ _ rfl mono

theorem ReaderReachabilityWasm2.enter {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm2 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (child : SourceScope) (entered : child.entered = reachable)
    (remaining : List code.StackType) (base : Usize) (form : Wasm2.Frames.Form) (bt : signature.BlockType) (ins outs : List types.ValueType) :
    ReaderReachabilityWasm2 nextReachable (parents ++ [current]) child
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Wasm2.Frames.Saved.fresh base form bt ins outs) :=
  invariant.push nextReachable child _ _ rfl (fun live => entered.symm.trans live) (fun _ => rfl)

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

end Exec.Code
