import Exec.Abs.Core.MemoryStep
import Exec.Abs.Memory.Decode

namespace Itasca.Runtime.Abs.Core

/-- Execute a scalar Core instruction. Pure integer/control instructions reuse
the established transition; mutable instructions resolve their own store maps. -/
def instruction (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (op : instr) (after : List instr) : AResult :=
  let state : AState := ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩
  match op with
  | .CONST ty value => advance state {f with code := after, vals := f.vals ++ [.CONST ty value]} rest
  | .SELECT none => select state f rest after
  | .GLOBAL_GET (.mk_uN index) => globalGet state f rest index after
  | .GLOBAL_SET (.mk_uN index) => globalSet state f rest index after
  | .LOAD ty packed argument =>
    match Memory.decodeLoad ty packed with
    | some descriptor => load state f rest after descriptor argument
    | none => .stuck
  | .STORE ty packed argument =>
    match Memory.decodeStore ty packed with
    | some descriptor => store state f rest after descriptor argument
    | none => .stuck
  | _ => astep state

/-- Mutable scalar abstract execution. Host calls remain an explicit boundary;
no host result is manufactured by the pure machine. -/
def step (s : AState) : AResult :=
  match s.frames with
  | [] => .done s.results
  | f :: rest =>
    match f.code with
    | [] => astep s
    | op :: after => instruction s.store s.ambient f rest op after

theorem instruction_load (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Load) (argument : memarg) :
    instruction s ambient f rest (op.source argument) after =
      load ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after op argument := by
  simp only [instruction,Memory.Load.source,Memory.decodeLoad_descriptor]

theorem instruction_store (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Store) (argument : memarg) :
    instruction s ambient f rest (op.source argument) after =
      store ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after op argument := by
  simp only [instruction,Memory.Store.source,Memory.decodeStore_descriptor]

end Itasca.Runtime.Abs.Core
