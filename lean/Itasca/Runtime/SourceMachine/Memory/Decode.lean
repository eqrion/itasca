import Itasca.Runtime.SourceMachine.Memory.Descriptor

namespace Itasca.Runtime.SourceMachine.Memory

def decodeLoad (ty : numtype) : Option loadop_ → Option Load
  | none => some (.full ty)
  | some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) sign)) =>
    if ty = .I32 then some (.packed .I32 .byte sign) else none
  | some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 16) sign)) =>
    if ty = .I32 then some (.packed .I32 .half sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 8) sign)) =>
    if ty = .I64 then some (.packed .I64 .byte sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 16) sign)) =>
    if ty = .I64 then some (.packed .I64 .half sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 32) sign)) =>
    if ty = .I64 then some (.packed .I64 .word sign) else none
  | _ => none

def decodeStore : numtype → Option sz → Option Store
  | ty,none => some (.full ty)
  | .I32,some (.mk_sz 8) => some (.packed .I32 .byte)
  | .I32,some (.mk_sz 16) => some (.packed .I32 .half)
  | .I64,some (.mk_sz 8) => some (.packed .I64 .byte)
  | .I64,some (.mk_sz 16) => some (.packed .I64 .half)
  | .I64,some (.mk_sz 32) => some (.packed .I64 .word)
  | _,_ => none

theorem decode_load_descriptor (op : Load) : decodeLoad op.type op.operation = some op := by
  cases op with
  | full ty => rfl
  | packed ty width sign => cases ty <;> cases width <;> rfl

theorem decode_store_descriptor (op : Store) : decodeStore op.type op.operation = some op := by
  cases op with
  | full ty => rfl
  | packed ty width => cases ty <;> cases width <;> rfl

end Itasca.Runtime.SourceMachine.Memory
