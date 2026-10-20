import Exec.Spec.Choices.VectorDeterminism
import Exec.Spec.Typing.FunctionEntryTyping
import Exec.Spec.MemoryReadBounds
import Exec.Spec.SimdReadBounds
/-! Uniqueness of generated function-entry defaults and the bounded scalar/SIMD
byte-decoding facts used by source read determinism. -/

namespace Exec.Spec
open SpecExt

theorem source_some_default_unique {type : valtype} {left right : val}
    (first : fun_default_ type (some left)) (second : fun_default_ type (some right)) : left=right := by
  cases first <;> cases second
  all_goals try rfl
  all_goals casesm* fun_fzero _ _
  all_goals rfl

theorem source_default_options_unique {type : valtype} {left right : Option val}
    (first : fun_default_ type left) (second : fun_default_ type right)
    (leftPresent : left≠none) (rightPresent : right≠none) : left=right := by
  cases left with
  | none => contradiction
  | some left =>
    cases right with
    | none => contradiction
    | some right => exact congrArg some (source_some_default_unique first second)

theorem source_defaults_unique (types : List valtype) (left right : List (Option val))
    (leftCount : left.length=types.length) (rightCount : right.length=types.length)
    (first : Forall₂ (fun option type => fun_default_ type option) left types)
    (second : Forall₂ (fun option type => fun_default_ type option) right types)
    (leftPresent : Forall (fun option => option≠none) left)
    (rightPresent : Forall (fun option => option≠none) right) : left=right := by
  apply forall2_functional_left (fun option type => fun_default_ type option ∧ option≠none)
    (fun _ _ _ one two => source_default_options_unique one.1 two.1 one.2 two.2)
    types left right leftCount rightCount
  · intro pair member
    exact ⟨first pair member,leftPresent pair.1 (List.of_mem_zip member).1⟩
  · intro pair member
    exact ⟨second pair member,rightPresent pair.1 (List.of_mem_zip member).1⟩

theorem numeric_read_rule_bound {bytes : List byte} {address : Nat} {type : numtype} {value : num_}
    (typed : wf_num_ type value)
    (read : nbytes_ type value = (bytes.drop address).take
      (rat_to_nat (((size (valtype_numtype type)).bind (fun n => some (n : Rat))).get! / 8))) :
    address+rat_to_nat (((size (valtype_numtype type)).bind (fun n => some (n : Rat))).get! / 8)≤bytes.length := by
  cases type <;> simp only [valtype_numtype,size,Option.bind_some,Option.get!_some] at read ⊢
  all_goals norm_num [rat_to_nat] at read ⊢
  all_goals apply numeric_read_bounds _ _ _ _ typed
  all_goals simpa [scalarNumBytes] using read

theorem source_load_packed_width {z : state} {address : num_} {type : Inn} {bits : Nat} {sign : sx} {argument : memarg}
    (wellFormed : wf_config ⟨z,[.CONST .I32 address,.LOAD (numtype_Inn type)
      (some (.mk_loadop__0 type (.mk_loadop_Inn (.mk_sz bits) sign))) argument]⟩) :
    bits=8 ∨ bits=16 ∨ bits=32 ∨ bits=64 := by
  have instruction := (wf_config_parts wellFormed).2 (.LOAD (numtype_Inn type)
    (some (.mk_loadop__0 type (.mk_loadop_Inn (.mk_sz bits) sign))) argument) (by simp)
  cases instruction
  have packed : wf_loadop_ (numtype_Inn type) (.mk_loadop__0 type (.mk_loadop_Inn (.mk_sz bits) sign)) := by
    have all : Forall (fun op => wf_loadop_ (numtype_Inn type) op)
      (Option.toList (some (.mk_loadop__0 type (.mk_loadop_Inn (.mk_sz bits) sign)))) := by assumption
    exact all _ (by simp)
  cases packed
  casesm* wf_loadop_Inn _ _
  casesm* wf_sz _
  tauto

theorem source_lane_word_bound (type : Jnn) (count : Nat) (word : uN)
    (typed : wf_lane_ (fun_lanetype (.X (lanetype_Jnn type) (.mk_dim count)))
      (.mk_lane__0 type (.mk_uN (proj_uN_0 word)))) : proj_uN_0 word<2^(jsize type) := by
  cases typed
  casesm* wf_uN _ _
  cases type <;> norm_num [lsize,lanetype_Jnn,jsize,sizenn,size,valtype_numtype,psize] at * <;> omega

theorem bounded_integer_encoding_unique {bits : Nat} {left right : uN}
    (width : bits=8 ∨ bits=16 ∨ bits=32 ∨ bits=64 ∨ bits=128)
    (leftBound : proj_uN_0 left<2^bits) (rightBound : proj_uN_0 right<2^bits)
    (same : ibytes_ bits left=ibytes_ bits right) : left=right :=
  ibytes_injective bits (by rcases width with rfl | rfl | rfl | rfl | rfl <;> decide) left right leftBound rightBound same

theorem bounded_integer_read_inside {bits : Nat} {bytes : List byte} {address : Nat} {word : uN}
    (width : bits=8 ∨ bits=16 ∨ bits=32 ∨ bits=64 ∨ bits=128)
    (read : ibytes_ bits word=(bytes.drop address).take (rat_to_nat ((bits : Rat)/8))) :
    address+rat_to_nat ((bits : Rat)/8)≤bytes.length := Simd.integer_read_rat_bounds bytes address bits word width read
theorem unsigned_bound_of_wf (width : Nat) (word : uN) (typed : wf_uN width word) : proj_uN_0 word<2^width := by
  cases typed
  rename_i value relation
  have positive : (0 : Int)<2^width := by positivity
  have integerBound : (value : Int)<2^width := by omega
  exact_mod_cast integerBound

theorem source_packed_read_inside {z : state} {address : num_} {type : Inn} {bits : Nat} {sign : sx} {argument : memarg} {word : uN}
    (wellFormed : wf_config ⟨z,[.CONST .I32 address,.LOAD (numtype_Inn type)
      (some (.mk_loadop__0 type (.mk_loadop_Inn (.mk_sz bits) sign))) argument]⟩)
    (read : ibytes_ bits word=((fun_mem z (.mk_uN 0)).BYTES.drop
      (proj_uN_0 (proj_num__0 address).get!+proj_uN_0 argument.OFFSET)).take (rat_to_nat ((bits : Rat)/8))) :
    proj_uN_0 (proj_num__0 address).get!+proj_uN_0 argument.OFFSET+rat_to_nat ((bits : Rat)/8)≤
      (fun_mem z (.mk_uN 0)).BYTES.length := by
  have width := source_load_packed_width wellFormed
  exact bounded_integer_read_inside (by tauto) read
end Exec.Spec
