import Exec.Spec.Choices.NumericInputUniqueness
/-! Bitmask results and shuffle lane arrays are determined by their exact
source encodings, without imposing irrelevant high-bit bounds. -/

namespace Exec.Spec
open SpecExt

theorem word_lane_list_injective (type : Jnn) {left right : List uN}
    (same : Map (fun word => lane_.mk_lane__0 type word) left=Map (fun word => lane_.mk_lane__0 type word) right) : left=right := by
  apply (List.map_inj_right ?_).mp same
  intro left right same
  have words := congrArg proj_lane__0 same
  simpa only [proj_lane__0,Option.some.injEq] using words

theorem word_lane_lists_unique {type : Jnn} {left right : List uN} {payload : List lane_}
    (first : Map (fun word => lane_.mk_lane__0 type word) left=payload)
    (second : Map (fun word => lane_.mk_lane__0 type word) right=payload) : left=right :=
  word_lane_list_injective type (first.trans second.symm)

theorem reversed_bits_unique (width : Nat) {left right : uN} (same : ibits_ width left=ibits_ width right) :
    irev_ width left=irev_ width right := by
  change inv_ibits_ width (ibits_ width left).reverse=inv_ibits_ width (ibits_ width right).reverse
  rw [same]

theorem bitmask_values_unique (width : Nat) (inputs : List lane_) {left right : uN}
    {leftWords rightWords : List uN} {padding : List bit}
    (firstBits : ibits_ 32 left=leftWords.map (fun word => .mk_bit (proj_uN_0 word))++padding)
    (secondBits : ibits_ 32 right=rightWords.map (fun word => .mk_bit (proj_uN_0 word))++padding)
    (first : Forall₂ (fun result lane => fun_ilt_ width .S (proj_lane__0 lane).get! (.mk_uN 0) result) leftWords inputs)
    (second : Forall₂ (fun result lane => fun_ilt_ width .S (proj_lane__0 lane).get! (.mk_uN 0) result) rightWords inputs)
    (leftLength : leftWords.length=inputs.length) (rightLength : rightWords.length=inputs.length) :
    [admininstr.CONST .I32 (.mk_num__0 .I32 (irev_ 32 left))]=
      [admininstr.CONST .I32 (.mk_num__0 .I32 (irev_ 32 right))] := by
  have words := signed_lane_negative_list_unique width inputs leftWords rightWords leftLength rightLength first second
  cases words
  have sameBits := firstBits.trans secondBits.symm
  have sameWord := reversed_bits_unique 32 sameBits
  exact congrArg (fun word => [admininstr.CONST .I32 (.mk_num__0 .I32 word)]) sameWord

theorem shuffle_values_unique (type : packtype) (count : Nat) (indices : List laneidx)
    {left right : List uN} {payload : List lane_}
    (first : Map (fun word => lane_.mk_lane__0 (Jnn_packtype type) word) left=payload)
    (second : Map (fun word => lane_.mk_lane__0 (Jnn_packtype type) word) right=payload) :
    [admininstr.VCONST .V128 (inv_lanes_ (.X (lanetype_packtype type) (.mk_dim count))
      ((List.range count).map (fun index => .mk_lane__0 (Jnn_packtype type) left[proj_uN_0 indices[index]!]!)))] =
    [admininstr.VCONST .V128 (inv_lanes_ (.X (lanetype_packtype type) (.mk_dim count))
      ((List.range count).map (fun index => .mk_lane__0 (Jnn_packtype type) right[proj_uN_0 indices[index]!]!)))] := by
  have words := word_lane_lists_unique first second
  cases words
  rfl
end Exec.Spec
