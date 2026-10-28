import Exec.Code.Body.Reader.Control.StructuredRootMapPublication
import Exec.Code.Local.Relations.Control.ControlSources
import Exec.Code.Body.Reader.Control.ReaderEndPublication
import Exec.Code.Body.Reader.Control.ReaderScopeZipper

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

private theorem source_body_form_wasm2 {bt : signature.BlockType} {form : ScopeForm}
    (matched : ScopeFormMatchesWasm2 bt form .body) : form = .body := by
  cases matched
  rfl

/-- Actual Wasm 2 root END establishes the strict final map checker bounds.
The source zipper and empty returned control stack identify the sole root frame. -/
theorem reader_root_map_publication_wasm2 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Wasm2.Pending data env .Wasm2 localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (closed : out.core.ctrls.val = [])
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    FinalControlMapBounds after.function ∧ SourceAligned after := by
  obtain ⟨callback,_,_,_,zipper,afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have root : p.current.form = .body ∧ p.parents = [] := by
    rcases zipper with ⟨root,empty,_⟩ | ⟨grandparents,parent,instruction,split,finished,opened⟩
    · exact ⟨root,empty⟩
    · obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := opened
      rw [controls] at closed
      simp at closed
  have parentsEmpty : parents = [] := by
    have paired := same.parents
    rw [root.2] at paired
    cases paired
    rfl
  have rootForm : current.form = .body := by
    have matched := same.current.form
    rw [root.1] at matched
    exact source_body_form_wasm2 matched
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    omega
  rw [parentsEmpty] at invariant
  refine ⟨structured_root_map_publication ops law invariant rootForm sourceBound out.core p.current.ctrl.kind
    p.current.bt maps consumed endBound callback,?_⟩
  exact (compiler_end_sources ops law before after out.core p.current.ctrl.kind p.current.bt callback).aligned invariant.sources

end Itasca.Runtime.Code
