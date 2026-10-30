import Itasca.Runtime.Interp.Relations.Readback

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem decode_words_scalar (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (scalar : ty ≠ .V128) : Store.decodeWords ty lo hi = Store.decodeWords ty lo 0#u64 := by
  cases ty <;> simp_all [Store.decodeWords]

/-- Recover a represented source value using the pure mathematical word
decoder. Reference addresses remain naturals here, so no usize cast is assumed. -/
theorem decode_words_represents (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (value : val) (wellFormed : wf_val value) (typed : sourceType ty = Compiler.valueType value)
    (represented : pairWords ty (lo,hi) = Compiler.encodeValue value) :
    Store.decodeWords ty lo hi = value := by
  have floatBound : ty = .F32 → lo.val < 2^32 := by
    intro same
    subst ty
    have low := congrArg (fun words : List Nat => words[0]!) represented
    simp only [pairWords,sourceType,reduceCtorEq,ite_false,List.getElem!_cons_zero] at low
    rw [low]
    exact encode_value_f32_low value wellFormed typed.symm
  have source := Compiler.decode_encode value wellFormed []
  simp only [List.append_nil] at source
  rw [←typed,←represented,decode_words_code ty lo hi floatBound] at source
  exact congrArg Prod.fst (Option.some.inj source)

theorem WordsAt.decode_value {words : List U64} {position : Nat} (ty : Itasca.wasm_types.ValueType)
    (value : val) (wellFormed : wf_val value) (typed : sourceType ty = Compiler.valueType value)
    (represented : WordsAt words position (Compiler.encodeValue value)) :
    Store.decodeWords ty (Itasca.Runtime.Interp.readPair words position ty).1 (Itasca.Runtime.Interp.readPair words position ty).2 = value := by
  apply decode_words_represents ty _ _ value wellFormed typed
  exact represented.read_pair ty (by rw [Compiler.encode_value_length,←typed])

end Itasca.Runtime.Interp
