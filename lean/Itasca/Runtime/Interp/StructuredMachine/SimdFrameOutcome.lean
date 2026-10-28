import Itasca.Runtime.Interp.StructuredMachine.SimdExecutionJoin
import Itasca.Runtime.Interp.Simd.Common.SimdMutation

namespace Itasca.Runtime.Interp.StructuredMachine.Simd
open Aeneas.Std

def FrameOutcome {M P : Type} (view : M → Slice U8)
    (interpretation : Store.CodeInterpretation) (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (raw : runtime.interp.Frame) (index : Usize)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (source : Abs.AFrame) (rest : List Abs.AFrame)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧ FrameStoreMetadata store out.2.2.1 ∧
  ∃ pc : U32, pc.val=raw.pc.val+1 ∧
  ((out.1=.Ok () ∧ ∃ updated : Abs.AFrame,
    {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
    SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
    FrameSlots out.2.1 {raw with pc:=pc} updated ∧ FrameMetadata source updated ∧
    FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc} updated compiled C targets next output ∧
    Abs.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,source::rest,[]⟩
      (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩)) ∨
  (out.1=.Err (.Trap .MemoryOutOfBounds) ∧
    out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
    Store.decodeStore view interpretation out.2.2.1=Store.decodeStore view interpretation store ∧
    Abs.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,source::rest,[]⟩ .trap))

end Itasca.Runtime.Interp.StructuredMachine.Simd
