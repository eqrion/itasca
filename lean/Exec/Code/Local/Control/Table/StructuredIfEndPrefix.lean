import Exec.Code.Local.Control.Table.StructuredPrefixControl
namespace Exec.Code
open Aeneas.Std

/-- An implicit empty ELSE joins directly at the normal exit. Its input and
output stacks agree, so the compiler emits no skip instruction. -/
theorem StructuredPrefix.ifEnd {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels front params yes bt pc exit cond yesNormal yesBranch}
    (signature : BlockSignature types bt params params)
    (condition : cond.val = slots locals + slots (front ++ params))
    (guard : code[pc]? = some (.JumpIfZero cond exit))
    (yesCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, params, params, exit, exit.val, [], [], yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes (pc + 1) exit.val (front ++ params)) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params ++ [.I32]) [.IFELSE bt yes []]
      pc exit.val (front ++ params) := by
  exact StructuredPrefix.ifElse (noNormal := true) (noBranch := false) signature condition guard yesCode (.direct rfl rfl)
    (.nil _ _ _ yesCode.next_le_length (NormalLive.cons rfl))

end Exec.Code

