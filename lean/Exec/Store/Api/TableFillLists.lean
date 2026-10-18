import Exec.Store.Api.TableFillLoop
import Exec.Spec.TableFillAlgebra
namespace Exec.Store
open Aeneas Aeneas.Std

theorem fillTableWords_front (before : List U64) (start count : Nat) (value : U64) :
    fillTableWords before start value (count+1) =
      fillTableWords (before.set start value) (start+1) value count := by
  induction count with
  | zero => simp [fillTableWords]
  | succ count ih =>
    rw [fillTableWords,ih,fillTableWords]
    simp only [Nat.add_assoc,Nat.add_comm 1 count]

theorem fillTableWords_eq (before : List U64) (start count : Nat) (value : U64) :
    fillTableWords before start value count = Spec.Segment.fillInto before start value count := by
  induction count generalizing before start with
  | zero => rfl
  | succ count ih => rw [fillTableWords_front,Spec.Segment.fillInto,ih]
end Exec.Store
