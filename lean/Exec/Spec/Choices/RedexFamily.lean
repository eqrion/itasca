import Exec.Spec.Choices.CoreChoiceStep
namespace Exec.Spec
open SpecExt

def redexFamily : admininstr → Nat
  | .UNOP _ _ | .BINOP _ _ | .CVTOP _ _ _ => 3
  | .VUNOP _ _ | .VBINOP _ _ | .VCVTOP _ _ _ => 4
  | .MEMORY_GROW => 5
  | .TABLE_GROW _ => 6
  | .LOCAL_SET _ | .GLOBAL_SET _ | .TABLE_SET _ | .ELEM_DROP _ | .STORE _ _ _
  | .VSTORE _ _ | .VSTORE_LANE _ _ _ _ | .DATA_DROP _ => 2
  | .BLOCK _ _ | .LOOP _ _ | .CALL _ | .CALL_INDIRECT _ _ | .CALL_ADDR _
  | .REF_FUNC _ | .LOCAL_GET _ | .GLOBAL_GET _ | .TABLE_GET _ | .TABLE_SIZE _
  | .TABLE_FILL _ | .TABLE_COPY _ _ | .TABLE_INIT _ _ | .LOAD _ _ _ | .VLOAD _ _ _
  | .VLOAD_LANE _ _ _ _ | .MEMORY_SIZE | .MEMORY_FILL | .MEMORY_COPY | .MEMORY_INIT _ => 1
  | _ => 0

def codeRedexFamily (code : List admininstr) : Nat := redexFamily (residualCode code).head!

set_option maxHeartbeats 2000000 in
theorem pure_redex_family {before after : List admininstr} (source : Step_pure before after)
    (free : ChoiceFreePureRedex before) (nonactive : activeTrap before=false) : codeRedexFamily before=0 := by
  cases source
  all_goals try { simp [ChoiceFreePureRedex,pureRedexUsesChoice] at free }
  all_goals try { simp [activeTrap,activeTrap_value,activeTrap_map] at nonactive }
  all_goals try { simp [codeRedexFamily,redexFamily,residualCode,residualCode_value,residualCode_map] }
  all_goals try { casesm* ref; all_goals simp [codeRedexFamily,admininstr_ref,redexFamily,residualCode] }

set_option maxHeartbeats 2000000 in
theorem read_redex_family {before : config} {after : List admininstr} (source : Step_read before after) :
    codeRedexFamily (trapCode before)=1 := by
  cases source
  all_goals simp [trapCode,codeRedexFamily,redexFamily,residualCode,residualCode_value,residualCode_map]

theorem DirectWrite.redex_family {before after : config} (source : DirectWrite before after) :
    codeRedexFamily (trapCode before)=2 := by
  cases source
  all_goals try { simp [trapCode,codeRedexFamily,redexFamily,residualCode,residualCode_value] }
  all_goals casesm* ref
  all_goals simp [trapCode,codeRedexFamily,admininstr_ref,redexFamily,residualCode]

theorem NumericRequest.redex_family (request : NumericRequest) : codeRedexFamily request.instructions=3 := by
  cases request <;> rfl

theorem VectorRequest.redex_family (request : VectorRequest) : codeRedexFamily request.instructions=4 := by
  cases request <;> rfl
end Exec.Spec
