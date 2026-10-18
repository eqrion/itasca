import Exec.Spec.ExtensionTyping
namespace Exec.Spec

/-- Numerical limit compatibility retains the presence of optional maxima. -/
def LimitsCompatible : limits → limits → Prop
  | .mk_limits (.mk_uN size) maximum, .mk_limits (.mk_uN requiredMin) requiredMax =>
    requiredMin ≤ size ∧ ∀ bound, requiredMax = some bound →
      ∃ actual, maximum = some actual ∧ proj_uN_0 actual ≤ proj_uN_0 bound

theorem limits_compatible_refl (a : limits) : LimitsCompatible a a := by
  cases a with | mk_limits minimum maximum =>
    cases minimum
    exact ⟨Nat.le_refl _, fun bound found => ⟨bound, found, Nat.le_refl _⟩⟩

theorem limits_compatible_trans {a b c : limits}
    (left : LimitsCompatible a b) (right : LimitsCompatible b c) : LimitsCompatible a c := by
  cases a with | mk_limits amin amax =>
    cases b with | mk_limits bmin bmax =>
      cases c with | mk_limits cmin cmax =>
        cases amin; cases bmin; cases cmin
        refine ⟨Nat.le_trans right.1 left.1, ?_⟩
        intro bound found
        obtain ⟨middle, middleFound, middleLe⟩ := right.2 bound found
        obtain ⟨actual, actualFound, actualLe⟩ := left.2 middle middleFound
        exact ⟨actual, actualFound, Nat.le_trans actualLe middleLe⟩

theorem limits_sub_compatible {actual required} (sub : Limits_sub actual required) :
    LimitsCompatible actual required := by
  cases sub with
  | eps _ _ minimum _ _ => exact ⟨minimum, by simp⟩
  | max size maximum required desired minimum ordered _ _ =>
    refine ⟨minimum, ?_⟩
    intro bound found
    cases desired with
    | none => cases found
    | some wanted =>
      cases found
      exact ⟨.mk_uN maximum, rfl, ordered wanted (by simp)⟩

/-- The observable external type comparisons used at the import boundary. -/
def ExternalCompatible : externtype → externtype → Prop
  | .FUNC actual, .FUNC required => actual = required
  | .GLOBAL actual, .GLOBAL required => actual = required
  | .MEM (.PAGE actual), .MEM (.PAGE required) => LimitsCompatible actual required
  | .TABLE (.mk_tabletype actual actualElem), .TABLE (.mk_tabletype required requiredElem) =>
    actualElem = requiredElem ∧ LimitsCompatible actual required
  | _, _ => False

theorem external_compatible_refl (a : externtype) : ExternalCompatible a a := by
  cases a with
  | FUNC _ | GLOBAL _ => rfl
  | MEM ty => cases ty; exact limits_compatible_refl _
  | TABLE ty => cases ty; exact ⟨rfl, limits_compatible_refl _⟩

theorem external_sub_compatible {actual required} (sub : Externtype_sub actual required) :
    ExternalCompatible actual required := by
  cases sub with
  | func _ _ inner _ _ => cases inner; rfl
  | global _ _ inner _ _ => cases inner; rfl
  | mem _ _ inner _ _ => cases inner with | mk_Memtype_sub _ _ sub _ _ => exact limits_sub_compatible sub
  | table _ _ inner _ _ => cases inner with | mk_Tabletype_sub _ _ _ sub _ _ => exact ⟨rfl, limits_sub_compatible sub⟩

theorem external_compatible_trans {a b c : externtype}
    (left : ExternalCompatible a b) (right : ExternalCompatible b c) : ExternalCompatible a c := by
  cases a <;> cases b <;> cases c <;> try contradiction
  case FUNC.FUNC.FUNC a b c => exact Eq.trans left right
  case GLOBAL.GLOBAL.GLOBAL a b c => exact Eq.trans left right
  case MEM.MEM.MEM a b c => cases a; cases b; cases c; exact limits_compatible_trans left right
  case TABLE.TABLE.TABLE a b c =>
    cases a; cases b; cases c
    exact ⟨Eq.trans left.1 right.1, limits_compatible_trans left.2 right.2⟩

/-- Inspect an external address's actual store type. Issuance is separately
provided by the external-address typing derivation. -/
def externalActualType (s : store) : externaddr → externtype
  | .FUNC address => .FUNC s.FUNCS[address]!.TYPE
  | .GLOBAL address => .GLOBAL s.GLOBALS[address]!.TYPE
  | .TABLE address => .TABLE s.TABLES[address]!.TYPE
  | .MEM address => .MEM s.MEMS[address]!.TYPE

/-- Generated external-address typing, including any number of subtyping
steps, implies the actual import-boundary comparison. -/
theorem externaddr_compatible {s address required} (typed : Externaddr_ok s address required) :
    ExternalCompatible (externalActualType s address) required := by
  induction typed with
  | func address value bound found _ _ =>
    simp only [externalActualType, found]
    exact external_compatible_refl _
  | global address value bound found _ _ =>
    simp only [externalActualType, found]
    exact external_compatible_refl _
  | mem address value bound found _ _ =>
    simp only [externalActualType, found]
    exact external_compatible_refl _
  | table address value bound found _ _ =>
    simp only [externalActualType, found]
    exact external_compatible_refl _
  | sub address wanted actual prior sub _ _ _ ih =>
    exact external_compatible_trans ih (external_sub_compatible sub)
end Exec.Spec
