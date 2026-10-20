import Exec.Spec.Choices.RedexShape
import Exec.Spec.Choices.DirectWriteDeterminism
namespace Exec.Spec
open SpecExt

def functionInputCount : functype → Nat
  | .mk_functype (.mk_list inputs) _ => inputs.length

def operandArity (state : _root_.state) : admininstr → Nat
  | .BLOCK type _ | .LOOP type _ => functionInputCount (fun_blocktype state type)
  | .CALL_ADDR address => functionInputCount (fun_funcinst state)[address]!.TYPE
  | .SELECT _ | .VVTERNOP _ _ | .TABLE_FILL _ | .TABLE_COPY _ _ | .TABLE_INIT _ _
  | .MEMORY_FILL | .MEMORY_COPY | .MEMORY_INIT _ => 3
  | .BINOP _ _ | .RELOP _ _ | .VVBINOP _ _ | .VBINOP _ _ | .VRELOP _ _
  | .VSHIFTOP _ _ | .VSWIZZLE _ | .VSHUFFLE _ _ | .VREPLACE_LANE _ _
  | .VEXTBINOP _ _ _ | .VNARROW _ _ _ | .TABLE_SET _ | .TABLE_GROW _
  | .STORE _ _ _ | .VLOAD_LANE _ _ _ _ | .VSTORE _ _ | .VSTORE_LANE _ _ _ _ => 2
  | .DROP | .IFELSE _ _ _ | .BR_IF _ | .BR_TABLE _ _ | .CALL_INDIRECT _ _
  | .UNOP _ _ | .TESTOP _ _ | .CVTOP _ _ _ | .EXTEND _ _ | .VVUNOP _ _
  | .VVTESTOP _ _ | .VUNOP _ _ | .VTESTOP _ _ | .VBITMASK _ | .VSPLAT _
  | .VEXTRACT_LANE _ _ _ | .VEXTUNOP _ _ _ | .VCVTOP _ _ _ | .REF_IS_NULL
  | .LOCAL_SET _ | .LOCAL_TEE _ | .GLOBAL_SET _ | .TABLE_GET _ | .LOAD _ _ _
  | .VLOAD _ _ _ | .MEMORY_GROW => 1
  | _ => 0

set_option maxHeartbeats 2000000 in
theorem pure_operand_arity (state : _root_.state) {before after : List admininstr}
    (source : Step_pure before after) (nonactive : activeTrap before=false) :
    before.length=operandArity state (residualCode before).head!+1 := by
  cases source
  all_goals try { simp [activeTrap,activeTrap_value,activeTrap_map] at nonactive }
  all_goals try { simp [operandArity,residualCode,residualCode_value,residualCode_map,Map] }
  all_goals try { casesm* ref; all_goals simp [admininstr_ref,operandArity,residualCode] }

set_option maxHeartbeats 2000000 in
theorem read_operand_arity {z : state} {before after : List admininstr}
    (source : Step_read ⟨z,before⟩ after) :
    before.length=operandArity z (residualCode before).head!+1 := by
  cases source
  all_goals try { simp [operandArity,residualCode,residualCode_value,residualCode_map,Map] }
  all_goals simp only [residualCode_map]
  all_goals simp_all [operandArity,residualCode,functionInputCount,Map]
  all_goals omega

theorem DirectWrite.residual_single {before after : config} (source : DirectWrite before after) :
    (residualCode (trapCode before)).length=1 := by
  cases source
  all_goals simp [trapCode,residualCode,residualCode_value]
  all_goals casesm* ref
  all_goals simp [trapCode,admininstr_ref,residualCode]

theorem DirectWrite.operand_arity {z z' : state} {before after : List admininstr}
    (source : DirectWrite ⟨z,before⟩ ⟨z',after⟩) :
    before.length=operandArity z (residualCode before).head!+1 := by
  cases source
  all_goals simp [operandArity,residualCode,residualCode_value]
  all_goals casesm* ref
  all_goals simp [admininstr_ref,operandArity,residualCode]

theorem NumericRequest.operand_arity (state : _root_.state) (request : NumericRequest) :
    request.instructions.length=operandArity state (residualCode request.instructions).head!+1 := by
  cases request <;> rfl

theorem VectorRequest.operand_arity (state : _root_.state) (request : VectorRequest) :
    request.instructions.length=operandArity state (residualCode request.instructions).head!+1 := by
  cases request <;> rfl

theorem host_operand_arity {s : store} {f : frame} {address : funcaddr} {identity : Nat}
    {params results : List valtype} {args : List val}
    (host : HostFunction s address identity params results) (arguments : ResultsTyped s params args) :
    (vals args++[admininstr.CALL_ADDR address]).length=
      operandArity ⟨s,f⟩ (residualCode (vals args++[admininstr.CALL_ADDR address])).head!+1 := by
  obtain ⟨object,found⟩ := host
  have count := arguments.length_eq
  simp only [residualCode_vals,residualCode]
  simp [operandArity,functionInputCount,fun_funcinst,List.getElem!_eq_getElem?_getD,found,vals]
  omega
end Exec.Spec
