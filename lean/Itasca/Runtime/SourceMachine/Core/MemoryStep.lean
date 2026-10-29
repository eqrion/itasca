import Itasca.Runtime.SourceMachine.Memory.Semantics
import Itasca.Runtime.SourceMachine.Core.Globals
import Itasca.Runtime.SourceMachine.Core.Select

namespace Itasca.Runtime.Abs.Core
open SpecExt

/-- Scalar loads resolve memory zero in the current instance and use unwrapped
natural effective-address arithmetic before decoding the selected bytes. -/
def load (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Memory.Load) (argument : memarg) : AResult :=
  match pop f.vals,f.module.MEMS[0]? with
  | some (front,address),some memoryAddress =>
    match integer .I32 address,s.store.MEMS[memoryAddress]? with
    | some bits,some object =>
      let start := bits + proj_uN_0 argument.OFFSET
      if start + op.bytes ≤ object.BYTES.length then
        advance s {f with code := after, vals := front ++ [op.value ((object.BYTES.drop start).take op.bytes)]} rest
      else .trap
    | _,_ => .stuck
  | _,_ => .stuck

/-- Scalar stores retain the source memory's type and length, replacing only
an in-bounds byte interval. Operand decoding precedes the write. -/
def store (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Memory.Store) (argument : memarg) : AResult :=
  match pop f.vals,f.module.MEMS[0]? with
  | some (remaining,.CONST ty value),some memoryAddress =>
    if ty = op.type then
      match pop remaining,s.store.MEMS[memoryAddress]? with
      | some (front,address),some object =>
        match integer .I32 address with
        | none => .stuck
        | some bits =>
          let start := bits + proj_uN_0 argument.OFFSET
          if start + op.bytes ≤ object.BYTES.length then
            advance {s with store := Spec.memoryPayloadWrite s.store f.toFrame start (op.payload value)}
              {f with code := after, vals := front} rest
          else .trap
      | _,_ => .stuck
    else .stuck
  | _,_ => .stuck

end Itasca.Runtime.Abs.Core
