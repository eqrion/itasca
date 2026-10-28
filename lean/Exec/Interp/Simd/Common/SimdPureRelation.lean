import Exec.Code.Local.Lowering.Simd.SimdEmission
import Exec.Spec.SimdPureValues
import Exec.Interp.Simd.Common.SimdWholeSound
import Exec.Interp.Simd.Common.SimdSwizzleSound
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

def pureResult (signature : Signature) (bits : BitVec 128) : val :=
  match signature with
  | .test => .CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.toNat))
  | _ => .VCONST .V128 (.mk_uN bits.toNat)

def PureSourceEffect (op : Operation) (x y z value : BitVec 128) : Prop :=
  Step_pure ((Spec.Simd.operandValues op.signature.inputs x y z).map admininstr_val ++ [admininstr_instr op.instruction])
    [admininstr_val (pureResult op.signature value)]

def PureEntrySound {F : Type} (floats : runtime.platform.FloatOps F) (opcode : U32) : Prop :=
  ∀ op : Operation, pureMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)),
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧ PureSourceEffect op x.bv y.bv z.bv value.bv ⦄

theorem pure_entry_14 {F : Type} (floats : runtime.platform.FloatOps F) : PureEntrySound floats 14#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure14 = some op at meaning
  cases meaning
  with_unfolding_all exact swizzle_dispatch_sound floats offset laneIndex bits x y z memory

theorem pure_entry_77 {F : Type} (floats : runtime.platform.FloatOps F) : PureEntrySound floats 77#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure77 = some op at meaning
  cases meaning
  with_unfolding_all exact not_dispatch_sound floats offset laneIndex bits x y z memory

theorem pure_entry_78 {F : Type} (floats : runtime.platform.FloatOps F) : PureEntrySound floats 78#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure78 = some op at meaning
  cases meaning
  with_unfolding_all exact binary_dispatch_sound floats .AND offset laneIndex bits x y z memory

theorem pure_entry_79 {F : Type} (floats : runtime.platform.FloatOps F) : PureEntrySound floats 79#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure79 = some op at meaning
  cases meaning
  with_unfolding_all exact binary_dispatch_sound floats .ANDNOT offset laneIndex bits x y z memory

theorem pure_entry_80 {F : Type} (floats : runtime.platform.FloatOps F) : PureEntrySound floats 80#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure80 = some op at meaning
  cases meaning
  with_unfolding_all exact binary_dispatch_sound floats .OR offset laneIndex bits x y z memory

theorem pure_entry_81 {F : Type} (floats : runtime.platform.FloatOps F) : PureEntrySound floats 81#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure81 = some op at meaning
  cases meaning
  with_unfolding_all exact binary_dispatch_sound floats .XOR offset laneIndex bits x y z memory

theorem pure_entry_82 {F : Type} (floats : runtime.platform.FloatOps F) : PureEntrySound floats 82#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure82 = some op at meaning
  cases meaning
  with_unfolding_all exact bitselect_dispatch_sound floats offset laneIndex bits x y z memory

theorem pure_entry_83 {F : Type} (floats : runtime.platform.FloatOps F) : PureEntrySound floats 83#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure83 = some op at meaning
  cases meaning
  with_unfolding_all exact any_true_dispatch_sound floats offset laneIndex bits x y z memory
end Itasca.Runtime.Interp.Simd
