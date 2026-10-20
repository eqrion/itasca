import Exec.Spec.ByteEncoding

/-! Source reads equate an exactly sized encoding with a list slice. Unlike a
write's clamping splice, this equality enforces the positive-width read bound. -/
namespace Exec.Spec
open SpecExt.Builtins

/-- A positive-width complete slice must be inside the original list. -/
theorem full_slice_bounds {T : Type} (bytes payload : List T) (address width : Nat)
    (positive : 0 < width) (sized : payload.length = width)
    (read : payload = (bytes.drop address).take width) : address + width ≤ bytes.length := by
  have lengths := congrArg List.length read
  simp only [List.length_take,List.length_drop,sized] at lengths
  omega

/-- Source scalar encodings have their type's full byte width. -/
theorem numericBytes_length (type : numtype) (value : num_) (typed : wf_num_ type value) :
    (nbytes_ type value).length = scalarNumBytes type := by
  cases typed with
  | num__case_0 ty bits _ _ same =>
    subst type
    cases ty <;> simp [numtype_Inn,nbytes_,ibytes_,scalarNumBytes,integerBytes_length]
  | num__case_1 ty value _ same =>
    subst type
    cases ty <;> simp [numtype_Fnn,nbytes_,fbytes_,scalarNumBytes,integerBytes_length]

/-- The scalar load success equality excludes the complementary bounds trap,
including large effective addresses. -/
theorem numeric_read_bounds (bytes : List byte) (address : Nat) (type : numtype) (value : num_)
    (typed : wf_num_ type value)
    (read : nbytes_ type value = (bytes.drop address).take (scalarNumBytes type)) :
    address + scalarNumBytes type ≤ bytes.length := by
  exact full_slice_bounds bytes _ address _ (by cases type <;> decide)
    (numericBytes_length type value typed) read

/-- This shared lemma covers packed, vector, splat, zero, and individual lane
reads whenever their source equality supplies the exact positive byte width. -/
theorem integer_read_bounds (bytes : List byte) (address bits : Nat) (value : uN)
    (positive : 0 < bits / 8)
    (read : ibytes_ bits value = (bytes.drop address).take (bits / 8)) :
    address + bits / 8 ≤ bytes.length :=
  full_slice_bounds bytes _ address _ positive (by simp [ibytes_,integerBytes_length]) read

end Exec.Spec
