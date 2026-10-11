import Itasca.MultiValue.Invariant

open Aeneas Aeneas.Std

namespace Itasca.MultiValueGrammar

open MultiValue

/-- A type index uses signed LEB, including nonminimal positive encodings. -/
theorem padded_index : BlockEncoding (.TypeIndex 0#u32) [128#u8, 0#u8] := by
  refine ⟨[128#u8], 0#u8, rfl, by decide, ?_, by decide, ?_, by decide, by decide⟩
  · simp
  · norm_num [SignedLeb33.finalValue, Leb128.payload]

/-- Padded negative s33 encodings are not inline value-type tags. -/
theorem padded_negative_not_inline (t : types.ValueType) :
    ¬ BlockEncoding (.Value t) [255#u8, 127#u8] := by
  simp [BlockEncoding]

def bytes : Slice U8 := alloc.vec.Vec.deref (alloc.vec.Vec.from
  [0x02#u8, 0x80#u8, 0x00#u8, 0x0B#u8, 0x0B#u8] (by scalar_tac))

/-- Syntax decoding remains independent of whether type index zero exists. -/
theorem indexed_body : BodyEncoding bytes [.BLOCK (blockType (.TypeIndex 0#u32)) []] := by
  have hb : At bytes 0#usize (.block (.TypeIndex 0#u32)) 3#usize :=
    ⟨_, ⟨0x02#u8, [0x80#u8, 0x00#u8], rfl, .block padded_index⟩, rfl, rfl, by decide⟩
  have he : At bytes 3#usize .end_ 4#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have hf : At bytes 4#usize .end_ 5#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  exact ⟨_, 5#usize, (((Consumed.nil 0#usize (by decide)).snoc hb).snoc he).snoc hf,
    rfl, _, rfl, Emits.block _ .nil .nil⟩

/-- An if without an explicit else may preserve multiple parameters/results.
This exercises the identity-arm rule that the Wasm 1.0 frame invariant lacks. -/
theorem identity_if (env : module.Env) (C : context) (hC : wf_context C)
    (htypes : C.TYPES = env.types.val.map EnvTranslation.funcType) (index : U32)
    (hin : resolve env (inputs (.TypeIndex index)) = some [.I32, .I64])
    (hout : resolve env (outputs (.TypeIndex index)) = some [.I32, .I64]) :
    Instr_ok C (.IFELSE (blockType (.TypeIndex index)) [] [])
      (.mk_functype (.mk_list [.I32, .I64, .I32]) (.mk_list [.I32, .I64])) := by
  let f := MultiValue.Frames.Saved.fresh 0#usize .then_ (.TypeIndex index) [.I32, .I64] [.I32, .I64]
  have hh : MultiValue.Frames.Header env C f := ⟨rfl, rfl, hin, hout, trivial, .nil⟩
  have ht := TypedPrefix.start (MultiValue.Frames.enter C .then_ [.I32, .I64] [.I32, .I64])
    (MultiValue.Frames.enter_wf C hC _ _ _) [.I32, .I64]
  exact (MultiValue.Frames.Closed.then_ _ _).typed (f := f) hC htypes hh ht
    (Sequence.realizes_default false [.Val .I32, .Val .I64]) (fun _ => rfl)

end Itasca.MultiValueGrammar
