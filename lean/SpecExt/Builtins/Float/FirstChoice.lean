import SpecExt.Builtins.Float.Canonical
namespace SpecExt.Builtins.Float

/-- The pinned floating-point result sets are a singleton or one of the two
explicit NaN sets. Their ordering fixes a canonical first-result policy. -/
inductive ReplyFamily (width : Nat) : List fN → Prop where
  | singleton (value : fN) : ReplyFamily width [value]
  | canonical : ReplyFamily width (canonicalNaNs width)
  | arithmetic : ReplyFamily width (arithmeticNaNs width)

theorem nans_reply_family (width : Nat) (inputs : List fN) : ReplyFamily width (nans width inputs) := by
  unfold nans
  split <;> constructor

theorem arithmeticNaNs_head (width : Nat) (positive : 0<canon_ width) :
    (arithmeticNaNs width).head?=some (.POS (.NAN (canon_ width))) := by
  cases count : canon_ width with
  | zero => omega
  | succ n => simp [arithmeticNaNs,count,List.range_succ_eq_map]

theorem canonicalNaNs_member_isNaN {width : Nat} {value : fN} (member : value∈canonicalNaNs width) :
    isNaN value=true := by
  simp only [canonicalNaNs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem arithmeticNaNs_member_isNaN {width : Nat} {value : fN} (member : value∈arithmeticNaNs width) :
    isNaN value=true := by
  obtain ⟨offset,inside,member⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem ReplyFamily.head_of_canonical_result {width : Nat} {allowed : List fN} {value : fN}
    (family : ReplyFamily width allowed) (positive : 0<canon_ width) (member : value∈allowed)
    (canonical : isNaN value=true → value=.POS (.NAN (canon_ width))) : allowed.head?=some value := by
  cases family with
  | singleton result =>
    have same : value=result := List.mem_singleton.mp member
    rw [same]
    rfl
  | canonical =>
    have same := canonical (canonicalNaNs_member_isNaN member)
    rw [same]
    rfl
  | arithmetic =>
    have same := canonical (arithmeticNaNs_member_isNaN member)
    rw [same]
    exact arithmeticNaNs_head width positive


theorem add_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fadd_ width a b) := by
  unfold fadd_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem sub_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fsub_ width a b) := by
  unfold fsub_
  split
  · exact nans_reply_family _ _
  · exact add_reply_family _ _ _

theorem mul_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fmul_ width a b) := by
  unfold fmul_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem div_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fdiv_ width a b) := by
  unfold fdiv_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem sqrt_reply_family (width : Nat) (a : fN) : ReplyFamily width (fsqrt_ width a) := by
  unfold fsqrt_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem integral_reply_family (op : Rat → Int) (width : Nat) (a : fN) : ReplyFamily width (integral op width a) := by
  unfold integral
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem ceil_reply_family (width : Nat) (a : fN) : ReplyFamily width (fceil_ width a) := integral_reply_family _ _ _
theorem floor_reply_family (width : Nat) (a : fN) : ReplyFamily width (ffloor_ width a) := integral_reply_family _ _ _
theorem trunc_reply_family (width : Nat) (a : fN) : ReplyFamily width (ftrunc_ width a) := integral_reply_family _ _ _
theorem nearest_reply_family (width : Nat) (a : fN) : ReplyFamily width (fnearest_ width a) := integral_reply_family _ _ _

theorem min_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fmin_ width a b) := by
  unfold fmin_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem max_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fmax_ width a b) := by
  unfold fmax_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem demote_reply_family (source target : Nat) (a : fN) : ReplyFamily target (demote__ source target a) := by
  unfold demote__
  split_ifs <;> constructor

theorem promote_reply_family (source target : Nat) (a : fN) : ReplyFamily target (promote__ source target a) :=
  demote_reply_family _ _ _
end SpecExt.Builtins.Float
