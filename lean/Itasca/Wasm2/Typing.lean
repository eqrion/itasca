import Itasca.Wasm2.Signature
import Itasca.Support.ControlTranslation

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

def inputs : signature.BlockType → signature.ResultType
  | .TypeIndex i => .Type i .Params
  | _ => .Empty

def outputs : signature.BlockType → signature.ResultType
  | .Empty => .Empty
  | .Value t => .One t
  | .TypeIndex i => .Type i .Results

/-- Resolving both views of an indexed block selects the same function type
    used by the generated Wasm 2.0 block typing rule. -/
theorem blockType_ok (env : module.Env) (C : context) (hC : wf_context C)
    (htypes : C.TYPES = env.types.val.map EnvTranslation.funcType)
    (bt : signature.BlockType) (ins outs : List types.ValueType)
    (hi : resolve env (inputs bt) = some ins)
    (ho : resolve env (outputs bt) = some outs) :
    Blocktype_ok C (blockType bt)
      (.mk_functype (.mk_list (ins.map Translate.valueType))
        (.mk_list (outs.map Translate.valueType))) := by
  cases bt with
  | Empty =>
    simp [inputs, outputs, resolve] at hi ho
    subst ins; subst outs
    exact .valtype C none hC (.blocktype_case_0 _)
  | Value t =>
    simp [inputs, outputs, resolve] at hi ho
    subst ins; subst outs
    exact .valtype C (some (Translate.valueType t)) hC (.blocktype_case_0 _)
  | TypeIndex i =>
    by_cases hb : i.val < env.types.val.length
    · simp [inputs, outputs, resolve, List.getElem?_eq_getElem hb] at hi ho
      subst ins; subst outs
      apply Blocktype_ok.typeidx C (.mk_uN i.val) _ _
      · simpa [htypes, proj_uN_0] using hb
      · rw [htypes, getElem!_pos _ _ (by simpa [proj_uN_0] using hb), List.getElem_map]
        rfl
      · exact hC
      · exact blockType_wf (.TypeIndex i)
    · simp [inputs, resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ i.val)] at hi

end Itasca.Wasm2

namespace Itasca

@[simp]
theorem signature.BlockType.params.spec (bt : signature.BlockType) :
    signature.BlockType.params bt = .ok (Wasm2.inputs bt) := by cases bt <;> rfl

@[simp]
theorem signature.BlockType.results.spec (bt : signature.BlockType) :
    signature.BlockType.results bt = .ok (Wasm2.outputs bt) := by cases bt <;> rfl

end Itasca
