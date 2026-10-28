import Exec.Abs.Core.Step
namespace Itasca.Runtime.Interp.MemoryDescriptor

theorem core_step_load_eq (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (op : Abs.Memory.Load) (argument : memarg) :
    Abs.Core.step ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ =
      Abs.Core.load ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ f rest after op argument := by
  simp only [Abs.Core.step,Abs.Core.instruction,Abs.Memory.Load.source,Abs.Memory.decodeLoad_descriptor]
  rfl

theorem core_step_store_eq (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (op : Abs.Memory.Store) (argument : memarg) :
    Abs.Core.step ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ =
      Abs.Core.store ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ f rest after op argument := by
  simp only [Abs.Core.step,Abs.Core.instruction,Abs.Memory.Store.source,Abs.Memory.decodeStore_descriptor]
  rfl
end Itasca.Runtime.Interp.MemoryDescriptor
