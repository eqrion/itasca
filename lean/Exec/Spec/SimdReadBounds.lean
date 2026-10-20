import Exec.Spec.MemoryReadBounds
import Exec.Spec.SimdMemoryExtend

namespace Exec.Spec.Simd
open SpecExt.Builtins

/-- Every specified positive byte width gives disjoint read-success and trap
bounds, including effective addresses larger than the address word. -/
theorem integer_read_rat_bounds (bytes : List byte) (address bits : Nat) (value : uN)
    (width : bits = 8 ∨ bits = 16 ∨ bits = 32 ∨ bits = 64 ∨ bits = 128)
    (read : ibytes_ bits value = (bytes.drop address).take (rat_to_nat ((bits : Rat)/8))) :
    address+rat_to_nat ((bits : Rat)/8) ≤ bytes.length := by
  have count : rat_to_nat ((bits : Rat)/8) = bits/8 := by
    rcases width with rfl | rfl | rfl | rfl | rfl <;> norm_num [rat_to_nat] <;> rfl
  rw [count] at read ⊢
  exact integer_read_bounds bytes address bits value (by rcases width with rfl | rfl | rfl | rfl | rfl <;> decide) read

/-- Plain vector loads read exactly sixteen bytes. -/
theorem vector_read_bounds (bytes : List byte) (address : Nat) (value : vec_)
    (read : vbytes_ .V128 value = (bytes.drop address).take 16) : address+16 ≤ bytes.length := by
  apply integer_read_bounds bytes address 128 value (by decide)
  simpa only [vbytes_,vsize] using read

/-- The shared source equality for splat and lane loads enforces every lane
width's bounds, rather than relying on the clamping behavior of List.take. -/
theorem lane_read_bounds (ty : Jnn) (bytes : List byte) (address : Nat) (value : uN)
    (read : ibytes_ (lsize (lanetype_Jnn ty)) value =
      (bytes.drop address).take (rat_to_nat ((lsize (lanetype_Jnn ty) : Rat)/8))) :
    address+rat_to_nat ((lsize (lanetype_Jnn ty) : Rat)/8) ≤ bytes.length := by
  apply integer_read_rat_bounds bytes address _ value _ read
  cases ty <;> decide

/-- Both zero-extending load widths enforce their complete source byte range. -/
theorem zero_read_bounds (bytes : List byte) (address bits : Nat) (value : uN)
    (width : bits = 32 ∨ bits = 64)
    (read : ibytes_ bits value = (bytes.drop address).take (rat_to_nat ((bits : Rat)/8))) :
    address+rat_to_nat ((bits : Rat)/8) ≤ bytes.length :=
  integer_read_rat_bounds bytes address bits value (by tauto) read

/-- Widening loads read eight bytes in total. The final lane's exact source
slice supplies the end bound for all three widening shapes. -/
theorem extending_read_bounds (ty : WidenWidth) (bytes : List byte) (address : Nat) (words : List uN)
    (count : words.length = ty.count)
    (reads : Forall₂ (fun (index : Nat) word => ibytes_ ty.width word =
      (bytes.drop (address+rat_to_nat ((index : Rat)*(ty.width : Rat)/8))).take (rat_to_nat ((ty.width : Rat)/8)))
      (List.range ty.count) words) : address+8 ≤ bytes.length := by
  let index := ty.count-1
  have last : index < ty.count := by cases ty <;> decide
  have wordBound : index < words.length := by omega
  have member : ((List.range ty.count)[index]'(by simpa using last),words[index]'wordBound) ∈ (List.range ty.count).zip words := by
    apply List.mem_iff_getElem.mpr
    refine ⟨index,by simp only [List.length_zip,List.length_range,count]; omega,?_⟩
    simp only [List.getElem_zip]
  have read := reads _ member
  simp only [List.getElem_range,memory_extend_bytes,memory_extend_offset] at read
  have bounded := integer_read_bounds bytes (address+index*(ty.width/8)) ty.width words[index]
    (by cases ty <;> decide) read
  have endpoint : index*(ty.width/8)+ty.width/8 = 8 := by cases ty <;> decide
  omega

private theorem range_relation_get {T : Type} (relation : Nat → T → Prop)
    (count : Nat) (values : List T) (sized : values.length = count)
    (related : Forall₂ relation (List.range count) values)
    (index : Nat) (inside : index < values.length) : relation index values[index] := by
  have indexBound : index < (List.range count).length := by simp only [List.length_range]; omega
  have member : ((List.range count)[index]'indexBound,values[index]) ∈
      (List.range count).zip values := by
    apply List.mem_iff_getElem.mpr
    refine ⟨index,by simp only [List.length_zip,List.length_range]; omega,?_⟩
    simp only [List.getElem_zip]
  simpa only [List.getElem_range] using related _ member

/-- The explicit source-width premises rule out distinct widening-load lane
values with identical truncated encodings. Length premises are necessary
because the generated Forall₂ quantifies over a zip. -/
theorem extending_read_values_unique (ty : WidenWidth) (payload : Nat → List byte)
    (left right : List uN) (leftCount : left.length = ty.count) (rightCount : right.length = ty.count)
    (leftBound : Forall (fun word => proj_uN_0 word < 2^ty.width) left)
    (rightBound : Forall (fun word => proj_uN_0 word < 2^ty.width) right)
    (leftRead : Forall₂ (fun index word => ibytes_ ty.width word = payload index) (List.range ty.count) left)
    (rightRead : Forall₂ (fun index word => ibytes_ ty.width word = payload index) (List.range ty.count) right) :
    left = right := by
  apply List.ext_getElem
  · omega
  · intro index leftInside rightInside
    exact integer_read_value_unique ty.width (by cases ty <;> decide) (payload index) _ _
      (leftBound _ (List.getElem_mem leftInside)) (rightBound _ (List.getElem_mem rightInside))
      (range_relation_get _ _ _ leftCount leftRead index leftInside)
      (range_relation_get _ _ _ rightCount rightRead index rightInside)

/-- Every successful SIMD read equality excludes its complementary source
out-of-bounds guard; this lemma is shared by the instruction families above. -/
theorem successful_read_excludes_trap {address width length : Nat} (success : address+width ≤ length) :
    ¬ length < address+width := Nat.not_lt.mpr success

end Exec.Spec.Simd
