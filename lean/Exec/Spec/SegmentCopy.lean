import Exec.Spec.Wf

namespace Exec.Spec.Segment

/-- Successive writes from an independent source segment. -/
def copyInto {T : Type} [Inhabited T] (before source : List T) (dst src : Nat) : Nat → List T
  | 0 => before
  | count+1 => copyInto (before.set dst source[src]!) source (dst+1) (src+1) count

theorem copyInto_length {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat) :
    (copyInto before source dst src count).length = before.length := by
  induction count generalizing before dst src with
  | zero => rfl
  | succ count ih => simp only [copyInto,ih,List.length_set]

end Exec.Spec.Segment
