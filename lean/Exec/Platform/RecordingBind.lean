import Exec.Platform.Recording
namespace Exec.Platform.Recording
open Aeneas Aeneas.Std SpecExt

/-- Bind erasure composes independently checked instrumentation, without any
normal-return or platform assumption. -/
theorem bind_erase {α β : Type}
    (recorded : Result (α × List HostEvent)) (original : Result α)
    (next : α → List HostEvent → Result (β × List HostEvent)) (plainNext : α → Result β)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (continued : ∀answer trace, (do let (out,_) ← next answer trace; Result.ok out)=plainNext answer) :
    (do let (answer,trace) ← recorded
        let (out,_) ← next answer trace
        Result.ok out) = (do let answer ← original; plainNext answer) := by
  rw [←erase]
  simp only [Std.bind_assoc,bind_ok]
  apply congrArg (Std.bind recorded)
  funext pair
  rcases pair with ⟨answer,trace⟩
  simp only [Std.uncurry,bind_ok]
  apply Eq.trans _ (continued answer trace)
  apply congrArg (Std.bind (next answer trace))
  funext pair
  rcases pair with ⟨out,log⟩
  rfl
theorem bind_erase_cont {α β : Type}
    (recorded : Result (α × List HostEvent)) (original : Result α)
    (next : α × List HostEvent → Result β) (plainNext : α → Result β)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (continued : ∀answer trace, next (answer,trace)=plainNext answer) :
    Std.bind recorded next = Std.bind original plainNext := by
  rw [←erase]
  simp only [Std.bind_assoc]
  apply congrArg (Std.bind recorded)
  funext pair
  rcases pair with ⟨answer,trace⟩
  simpa only [Std.uncurry,bind_ok] using continued answer trace
end Exec.Platform.Recording
