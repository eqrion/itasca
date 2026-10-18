import Exec.Abs.Slice
import Exec.Code.Local.Lowering.Common.NumericEncoding
namespace Exec.Code
open Aeneas.Std

theorem slice_block {ty body} (supported : Abs.SliceInstr (.BLOCK ty body)) :
    Forall Abs.SliceInstr body := by
  generalize target : instr.BLOCK ty body = instruction at supported
  cases supported <;> try simp_all
  rename_i op
  exact False.elim (integer_source_not_block op ty body target.symm)

theorem slice_loop {ty body} (supported : Abs.SliceInstr (.LOOP ty body)) :
    Forall Abs.SliceInstr body := by
  generalize target : instr.LOOP ty body = instruction at supported
  cases supported <;> try simp_all
  rename_i op
  exact False.elim (integer_source_not_loop op ty body target.symm)

theorem slice_ifelse {ty yes no} (supported : Abs.SliceInstr (.IFELSE ty yes no)) :
    Forall Abs.SliceInstr yes ∧ Forall Abs.SliceInstr no := by
  generalize target : instr.IFELSE ty yes no = instruction at supported
  cases supported <;> try simp_all
  rename_i op
  exact False.elim (integer_source_not_ifelse op ty yes no target.symm)
end Exec.Code
