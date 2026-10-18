import Exec.Code.Body.Reader.Common.ReaderWasm1
import Exec.Code.Body.Reader.Common.ReaderWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A particular running source zipper, including its exact consumed bytes.
This retains the witness needed for the next reader, instead of choosing an
unrelated existential zipper from a general validator-state theorem. -/
structure ReaderBoundaryWasm1 (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (st : code.OpIterState)
    (parents : List Wasm1.Frames.Saved) (current : Wasm1.Frames.Saved) : Prop where
  bounds : Wasm1.Bounds data st
  opened : Wasm1.Frames.Open (EnvTranslation.context env ctx) st parents current
  bodyType : Wasm1.Frames.bodyType parents current = some bt
  consumed : Wasm1.Consumed data 0#usize (Wasm1.Frames.trace parents current) st.pos

structure ReaderBoundaryWasm2 (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (st : code.BodyState) (parents : List Wasm2.Frames.Saved) (current : Wasm2.Frames.Saved) : Prop where
  signature : env.types.val[index.val]? = some ft
  bounds : Wasm2.Bounds data st
  opened : Wasm2.Frames.Open env (Wasm2.bodyContext env locals ft) st parents current
  bodyType : Wasm2.Frames.bodyType parents current = some (.TypeIndex index)
  consumed : Wasm2.Consumed data 0#usize (Wasm2.Frames.trace parents current) st.core.pos
  declared : Wasm2.TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
    (Wasm2.Frames.trace parents current)

def ReaderBoundaryWasm1.pending {data env ctx bt st parents current}
    (boundary : ReaderBoundaryWasm1 data env ctx bt st parents current)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length) :
    Wasm1.Pending data env ctx bt {st with pos := next} :=
  ⟨st.pos, parents, current, boundary.bounds.size, boundary.opened,
    boundary.bodyType, boundary.consumed, inbounds, advance, boundary.bounds.vals, boundary.bounds.ctrls⟩

def ReaderBoundaryWasm2.pending {data env locals index ft st parents current}
    (boundary : ReaderBoundaryWasm2 data env locals index ft st parents current)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length) :
    Wasm2.Pending data env locals index {core := {st.core with pos := next}} :=
  ⟨st.core.pos, ft, parents, current, boundary.signature, boundary.bounds.size, boundary.opened.with_pos next,
    boundary.bodyType, boundary.consumed, boundary.declared, inbounds, advance, boundary.bounds.ctrls⟩

theorem ReaderPostWasm1.boundary {data env ctx bt st out instruction poly values}
    {p : Wasm1.Pending data env ctx bt st}
    (post : ReaderPostWasm1 p out instruction poly values) :
    ReaderBoundaryWasm1 data env ctx bt out p.parents
      (p.current.advance (.plain instruction) instruction poly values) := by
  refine ⟨post.after.1.bounds, post.opened, ?_, ?_⟩
  · simpa only [Wasm1.Frames.bodyType_advance] using p.bodyType
  · have consumed := Wasm1.Consumed.snoc p.consumed post.encoded
    simpa [Wasm1.Frames.trace, Wasm1.Frames.Saved.trace, Wasm1.Frames.Saved.advance, List.append_assoc] using consumed

theorem ReaderPostWasm2.boundary {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env locals index st}
    (post : ReaderPostWasm2 p out instruction poly values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    ReaderBoundaryWasm2 data env locals index p.ft {core := out} p.parents
      (p.current.advance (.plain instruction) instruction poly values) := by
  refine ⟨p.signature, post.after.1.bounds, post.opened, ?_, ?_, ?_⟩
  · simpa only [Wasm2.Frames.bodyType_advance] using p.bodyType
  · have consumed := Wasm2.Consumed.snoc p.consumed post.encoded
    simpa [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.advance, List.append_assoc] using consumed
  · have trace : Wasm2.Frames.trace p.parents (p.current.advance (.plain instruction) instruction poly values) =
        Wasm2.Frames.trace p.parents p.current ++ [.plain instruction] := by
      simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.advance, List.append_assoc]
    rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, declared⟩

end Exec.Code
