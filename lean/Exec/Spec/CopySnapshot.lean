import Exec.Spec.CopyInterval
import Exec.Spec.MemoryInitSource
namespace Itasca.Runtime.Spec.Segment

def copyForward {T : Type} [Inhabited T] (words : List T) (dst src : Nat) : Nat → List T
  | 0 => words
  | count+1 => copyForward (words.set dst words[src]!) (next32 dst) (next32 src) count

def copyBackward {T : Type} [Inhabited T] (words : List T) (dst src : Nat) : Nat → List T
  | 0 => words
  | count+1 => copyBackward (words.set (dst+count) words[src+count]!) dst src count

theorem copyForward_snapshot {T : Type} [Inhabited T] (before current : List T) (dst src index remaining count : Nat)
    (state : CopyPrefix before current dst src index) (progress : index+remaining=count)
    (direction : dst ≤ src) (sourceBound : src+count ≤ before.length) (targetBound : dst+count ≤ before.length)
    (lengthBound : before.length ≤ 2^32) :
    copyForward current (dst+index) (src+index) remaining = before.setSlice! dst (before.slice src (src+count)) := by
  induction remaining generalizing current index with
  | zero =>
    have last : index=count := by omega
    exact (last ▸ state).complete sourceBound targetBound
  | succ remaining ih =>
    have srcInside : src+index < before.length := by omega
    have dstInside : dst+index < before.length := by omega
    have fresh := state.write direction srcInside dstInside
    by_cases done : remaining=0
    · subst remaining
      simp only [copyForward]
      have last : index+1=count := by omega
      exact (last ▸ fresh).complete sourceBound targetBound
    · have dstNext : next32 (dst+index) = dst+(index+1) := by
        unfold next32
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      have srcNext : next32 (src+index) = src+(index+1) := by
        unfold next32
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [copyForward,dstNext,srcNext]
      exact ih _ (index+1) fresh (by omega)

theorem copyBackward_snapshot {T : Type} [Inhabited T] (before current : List T) (dst src remaining count : Nat)
    (state : CopySuffix before current dst src remaining count) (progress : remaining≤count)
    (direction : src ≤ dst) (sourceBound : src+count ≤ before.length) (targetBound : dst+count ≤ before.length) :
    copyBackward current dst src remaining = before.setSlice! dst (before.slice src (src+count)) := by
  induction remaining generalizing current with
  | zero => exact state.complete sourceBound targetBound
  | succ remaining ih =>
    have fresh := state.write direction (by omega) progress (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at fresh
    rw [copyBackward]
    exact ih _ fresh (by omega)
end Itasca.Runtime.Spec.Segment
