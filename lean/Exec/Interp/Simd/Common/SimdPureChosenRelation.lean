import Exec.Interp.Simd.Common.SimdPureSound
import Exec.Spec.Choices.ChosenPureNeutral
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec Itasca.Wasm2.Simd

def PureChosenEffect (choices : SourceChoices) (occurrence : Nat) (op : Operation) (x y z value : BitVec 128) : Prop :=
  ChosenPure choices occurrence
    ((Spec.Simd.operandValues op.signature.inputs x y z).map admininstr_val ++ [admininstr_instr op.instruction])
    [admininstr_val (pureResult op.signature value)]

def PureEntryChosen {F : Type} (choices : SourceChoices) (occurrence : Nat)
    (floats : runtime.platform.FloatOps F) (opcode : U32) : Prop :=
  ∀ op : Operation, pureMeaning opcode.val = some op →
    ∀ (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)),
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧ PureChosenEffect choices occurrence op x.bv y.bv z.bv value.bv ⦄

theorem pure_entry_chosen_neutral {F : Type} (floats : runtime.platform.FloatOps F)
    {choices : SourceChoices} (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (opcode : U32)
    (sound : PureEntrySound floats opcode)
    (neutral : ∀ op : Operation, pureMeaning opcode.val = some op → ∀ x y z : BitVec 128,
      neutralPureRedex ((Spec.Simd.operandValues op.signature.inputs x y z).map admininstr_val ++
        [admininstr_instr op.instruction]) = true) : PureEntryChosen choices occurrence floats opcode := by
  intro op meaning offset laneIndex bits x y z memory
  apply WP.spec_mono (sound op meaning offset laneIndex bits x y z memory)
  rintro out ⟨value,returned,source⟩
  refine ⟨value,returned,?_⟩
  exact chosen_pure_neutral occurrence vector source (neutral op meaning x.bv y.bv z.bv)
end Exec.Interp.Simd
