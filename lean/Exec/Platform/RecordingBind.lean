import Exec.Platform.Recording
namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt

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
end Itasca.Runtime.Platform.Recording
