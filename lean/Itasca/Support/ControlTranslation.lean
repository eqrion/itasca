import Itasca.Support.EnvTranslation

/-!
# Block type translation

Translates `signature.BlockType` into SpecTec `blocktype` with a well-formedness proof.
`labelContext` is the context extension entered by structured control, and `Matches.enter` shows
that it preserves the static fields of `EnvTranslation.Matches`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- The context that adds one label with result types `ts`, to be prepended to the outer context. -/
def labelContext (ts : List valtype) : context :=
  ⟨[], [], [], [], [], [], [], [], [.mk_list ts], none⟩

@[simp]
theorem labelContext_labels (C : context) (ts : List valtype) :
    (labelContext ts ++ C).LABELS = .mk_list ts :: C.LABELS := rfl

theorem labelContext_wf (ts : List valtype) : wf_context (labelContext ts) := by
  constructor <;> simp [Forall]

theorem enter_context_wf (C : context) (hC : wf_context C) (ts : List valtype) :
    wf_context (labelContext ts ++ C) := by
  cases hC
  constructor <;> assumption

end Itasca.Control

namespace Itasca.EnvTranslation

theorem Matches.enter {env ctx C} (h : Matches env ctx C) (ts : List valtype) :
    Matches env ctx (Control.labelContext ts ++ C) := by
  exact ⟨h.types, h.funcs, h.globals, h.tables, h.mems, h.elems, h.datas, h.locals, h.ret⟩

end Itasca.EnvTranslation

namespace Itasca.Wasm2

/-- The SpecTec block type of a Wasm 2.0 block type, including type-index blocks. -/
def blockType : signature.BlockType → blocktype
  | .Empty => ._RESULT none
  | .Value t => ._RESULT (some (Translate.valueType t))
  | .TypeIndex i => ._IDX (.mk_uN i.val)

theorem blockType_wf (bt : signature.BlockType) : wf_blocktype (blockType bt) := by
  cases bt with
  | Empty => exact .blocktype_case_0 _
  | Value _ => exact .blocktype_case_0 _
  | TypeIndex i => exact .blocktype_case_1 _ (EnvTranslation.index_wf i)

end Itasca.Wasm2
