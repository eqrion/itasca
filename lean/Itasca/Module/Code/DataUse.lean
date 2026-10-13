import Itasca.Binary.Module

namespace Itasca.ModuleBinary

@[simp] theorem instructionsUseData_append (xs ys : List instr) :
    instructionsUseData (xs ++ ys) = (instructionsUseData xs || instructionsUseData ys) := by
  induction xs with
  | nil => rfl
  | cons op ops ih => simp [instructionsUseData, ih, Bool.or_assoc]

/-- Generated typing cannot mention a data index when its data space is empty,
even in nested or unreachable instructions. -/
theorem typed_no_data {C : context} {ops : List instr} {ft : functype}
    (h : Instrs_ok C ops ft) : C.DATAS = [] → instructionsUseData ops = false := by
  induction h using Instrs_ok.rec
    (motive_1 := fun C op _ _ => C.DATAS = [] → instructionUsesData op = false)
  all_goals first
    | rfl
    | (intro hd; simp_all [instructionUsesData, instructionsUseData, instructionsUseData_append])
    | (simp_all [instructionUsesData, instructionsUseData, instructionsUseData_append])

  case block => apply_assumption; assumption
  case loop => apply_assumption; assumption
  case «if» => constructor <;> (apply_assumption; assumption)

end Itasca.ModuleBinary
