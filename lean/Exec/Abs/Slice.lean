import Exec.Abs.Typing

namespace Exec.Abs

/-- The exact instruction family covered by the scalar integer execution proof. -/
inductive SliceInstr : instr → Prop where
  | numeric (op : Numeric.Instruction) : SliceInstr op.source
  | nop : SliceInstr .NOP
  | unreachable : SliceInstr .UNREACHABLE
  | drop : SliceInstr .DROP
  | const (ty : Inn) (value : iN) :
      SliceInstr (.CONST (numtype_Inn ty) (.mk_num__0 ty value))
  | add (ty : Inn) : SliceInstr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD))
  | sub (ty : Inn) : SliceInstr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty .SUB))
  | eqz (ty : Inn) : SliceInstr (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ))
  | eq (ty : Inn) : SliceInstr (.RELOP (numtype_Inn ty) (.mk_relop__0 ty .EQ))
  | lt_u (ty : Inn) : SliceInstr (.RELOP (numtype_Inn ty) (.mk_relop__0 ty (.LT .U)))
  | local_get (index : idx) : SliceInstr (.LOCAL_GET index)
  | local_set (index : idx) : SliceInstr (.LOCAL_SET index)
  | local_tee (index : idx) : SliceInstr (.LOCAL_TEE index)
  | block (ty : blocktype) (body : List instr) :
      Forall SliceInstr body → SliceInstr (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) :
      Forall SliceInstr body → SliceInstr (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) :
      Forall SliceInstr yes → Forall SliceInstr no → SliceInstr (.IFELSE ty yes no)
  | br (depth : labelidx) : SliceInstr (.BR depth)
  | br_if (depth : labelidx) : SliceInstr (.BR_IF depth)
  | call (index : funcidx) : SliceInstr (.CALL index)
  | ret : SliceInstr .RETURN

/-- All code reachable from the flat machine stays inside the slice. Memory,
tables, globals, floating-point operations, and host calls are excluded. -/
structure SliceState (s : AState) : Prop where
  active : Forall (fun f => Forall SliceInstr f.code ∧
    Forall (fun label => Forall SliceInstr label.cont ∧ Forall SliceInstr label.after) f.labels)
    s.frames
  functions : ∀ fn ∈ s.store.FUNCS, match fn.CODE with
    | .HOST _ => False
    | .FUNC _ _ body => Forall SliceInstr body

end Exec.Abs
