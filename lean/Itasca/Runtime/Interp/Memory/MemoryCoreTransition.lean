import Itasca.Runtime.SourceMachine.Core.Step
namespace Itasca.Runtime.Interp.MemoryDescriptor

theorem core_step_load_eq (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (op : SourceMachine.Memory.Load) (argument : memarg) :
    SourceMachine.Core.step ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ =
      SourceMachine.Core.load ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ f rest after op argument := by
  simp only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Memory.Load.source,SourceMachine.Memory.decode_load_descriptor]
  rfl

theorem core_step_store_eq (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (op : SourceMachine.Memory.Store) (argument : memarg) :
    SourceMachine.Core.step ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ =
      SourceMachine.Core.store ⟨s,ambient,{f with code := op.source argument :: after}::rest,[]⟩ f rest after op argument := by
  simp only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Memory.Store.source,SourceMachine.Memory.decode_store_descriptor]
  rfl
end Itasca.Runtime.Interp.MemoryDescriptor
