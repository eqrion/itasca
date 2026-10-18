import Exec.Abs.State

namespace Exec.Abs.Memory

/-- Packed scalar widths admitted by the binary format, indexed by result width. -/
inductive PackedWidth : Inn → Type where
  | byte {ty} : PackedWidth ty
  | half {ty} : PackedWidth ty
  | word : PackedWidth .I64

def PackedWidth.bits {ty} : PackedWidth ty → Nat
  | .byte => 8
  | .half => 16
  | .word => 32

def PackedWidth.size {ty} (width : PackedWidth ty) : sz := .mk_sz width.bits

/-- All fourteen scalar loads, including the signed/unsigned packed forms. -/
inductive Load where
  | full (ty : numtype)
  | packed (ty : Inn) (width : PackedWidth ty) (signed : sx)

def Load.type : Load → numtype
  | .full ty => ty
  | .packed ty _ _ => numtype_Inn ty

def Load.bytes : Load → Nat
  | .full ty => sizenn ty / 8
  | .packed _ width _ => width.bits / 8

def Load.operation : Load → Option loadop_
  | .full _ => none
  | .packed ty width signed => some (.mk_loadop__0 ty (.mk_loadop_Inn width.size signed))

def Load.source (op : Load) (argument : memarg) : instr :=
  .LOAD op.type op.operation argument

/-- All nine scalar stores; packed writes truncate the source integer. -/
inductive Store where
  | full (ty : numtype)
  | packed (ty : Inn) (width : PackedWidth ty)

def Store.type : Store → numtype
  | .full ty => ty
  | .packed ty _ => numtype_Inn ty

def Store.bytes : Store → Nat
  | .full ty => sizenn ty / 8
  | .packed _ width => width.bits / 8

def Store.operation : Store → Option sz
  | .full _ => none
  | .packed _ width => some width.size

def Store.source (op : Store) (argument : memarg) : instr :=
  .STORE op.type op.operation argument

theorem PackedWidth.well_formed {ty} (width : PackedWidth ty) : wf_sz width.size := by
  cases width <;> exact .sz_case_0 _ (by simp [PackedWidth.bits])

theorem PackedWidth.lt_width {ty} (width : PackedWidth ty) : width.bits < sizenn (numtype_Inn ty) := by
  cases ty <;> cases width <;> decide

theorem Load.operation_wf (op : Load) (packed : loadop_) (found : op.operation = some packed) :
    wf_loadop_ op.type packed := by
  cases op with
  | full ty => simp [Load.operation] at found
  | packed ty width signed =>
    simp only [Load.operation, Option.some.injEq] at found
    subst packed
    exact .loadop__case_0 _ ty _ (.loadop_Inn_case_0 ty width.size signed
      width.well_formed width.lt_width) rfl

theorem Load.bytes_positive (op : Load) : 0 < op.bytes := by
  cases op with
  | full ty => cases ty <;> decide
  | packed ty width signed => cases width <;> simp [Load.bytes, PackedWidth.bits]

theorem Store.bytes_positive (op : Store) : 0 < op.bytes := by
  cases op with
  | full ty => cases ty <;> decide
  | packed ty width => cases width <;> simp [Store.bytes, PackedWidth.bits]

end Exec.Abs.Memory
