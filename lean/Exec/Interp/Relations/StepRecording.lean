import Exec.Interp.Host.HostRecording

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

/-- The host target selected by the actual call bytecode. Failed lookups,
null references, and indirect signature mismatches select no host site. -/
def hostInstructionAddress {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) : Option runtime.FuncAddr := do
  let address ← match instruction with
    | .Call index _ => inst.funcs.val[index.val]?
    | .CallIndirect entry selector _ => do
      let (table,type) ← compiled.indirect.val[entry.val]?
      let tableAddress ← inst.tables.val[table.val]?
      let object ← store.tables.val[tableAddress.index.val]?
      let word ← exec.slots.val[raw.base.val+selector.val]?
      let reference ← object.elements.val[(UScalar.cast .U32 word).val]?
      if reference=0#u64 then none else do
        let index := UScalar.cast .Usize reference
        if index.val=0 then none else do
          let address : Usize := UScalar.ofNatCore (index.val-1) (by have := index.hBounds; omega)
          let function ← store.funcs.val[address.val]?
          let signature ← inst.types.val[type.val]?
          if function.signature=signature then some ⟨store.id,address⟩ else none
    | _ => none
  let function ← store.funcs.val[address.index.val]?
  match function.code with
  | .Host _ => some address
  | .Wasm .. => none

/-- Host-call selection uses only the pre-dispatch concrete frame, bytecode,
slots, tables and function metadata. It does not inspect a source trace. -/
def hostStepAddress {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) : Option runtime.FuncAddr := do
  let raw ← exec.frames.val[exec.frames.length-1]?
  let inst ← store.instances.val[raw.instance.val]?
  let compiled ← inst.module.functions.val[raw.function.val]?
  let instruction ← compiled.code.val[raw.pc.val]?
  hostInstructionAddress exec store raw inst compiled instruction

def stepHostEvents {M P : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : List HostEvent :=
  match hostStepAddress exec store with
  | some address => hostCallEvents address out
  | none => []

end Itasca.Runtime.Interp
