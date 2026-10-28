import Itasca.Runtime.Interp.Numeric.Integer.Int
import Itasca.Runtime.Interp.Numeric.Float.Float

/-! The scalar dispatch boundary reads both operands before writing the result.
A numeric trap leaves the complete execution state unchanged. These lemmas
connect the separately checked opcode handlers to their actual slot mutations. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Every field other than slot contents is preserved. -/
def SlotsEffect (before after : runtime.interp.Execution) (words : List U64) : Prop :=
  after.slots.val = words ∧ { after with slots := before.slots } = before

def ScalarEffect (before : runtime.interp.Execution) (position : Nat)
    (numeric : core.result.Result U64 runtime.ExecError)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match numeric with
  | .Ok value => out.1 = .Ok () ∧ SlotsEffect before out.2 (before.slots.val.set position value)
  | .Err error => out = (.Err error, before)

theorem execute_scalar_effect {F : Type} (ops : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : U16) (dst a b : U32)
    (ha : base.val + a.val < exec.slots.length)
    (hb : base.val + b.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length)
    (numeric : core.result.Result U64 runtime.ExecError)
    (hn : runtime.interp.int.scalar ops op
      exec.slots.val[base.val + a.val]! exec.slots.val[base.val + b.val]! = .ok numeric) :
    runtime.interp.execute_scalar ops exec base op dst a b ⦃ out =>
      ScalarEffect exec (base.val + dst.val) numeric out ⦄ := by
  unfold runtime.interp.execute_scalar
  simp only [lift, bind_ok]
  step as ⟨pa, hpa⟩
  step as ⟨va, hva⟩
  step as ⟨pb, hpb⟩
  step as ⟨vb, hvb⟩
  have ha' : base.val + a.val < exec.slots.val.length := ha
  have hb' : base.val + b.val < exec.slots.val.length := hb
  have hva' : va = exec.slots.val[base.val + a.val]! := by
    rw [_root_.getElem!_pos exec.slots.val (base.val + a.val) ha']
    simpa only [hpa, U32.cast_Usize_val_eq] using hva
  have hvb' : vb = exec.slots.val[base.val + b.val]! := by
    rw [_root_.getElem!_pos exec.slots.val (base.val + b.val) hb']
    simpa only [hpb, U32.cast_Usize_val_eq] using hvb
  rw [hva', hvb', hn]
  cases numeric <;> step* <;> simp_all [ScalarEffect, SlotsEffect]

end Itasca.Runtime.Interp
