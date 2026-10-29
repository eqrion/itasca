import Itasca.Runtime.SourceMachine.Typing

namespace Itasca.Runtime.Abs

/-- Source heads executed by `astep`, which never changes the store. -/
inductive PureHead : instr → Prop where
  | numeric (op : Numeric.Instruction) : PureHead op.source
  | nop : PureHead .NOP
  | unreachable : PureHead .UNREACHABLE
  | drop : PureHead .DROP
  | const (ty : Inn) (value : iN) :
      PureHead (.CONST (numtype_Inn ty) (.mk_num__0 ty value))
  | local_get (index : idx) : PureHead (.LOCAL_GET index)
  | local_set (index : idx) : PureHead (.LOCAL_SET index)
  | local_tee (index : idx) : PureHead (.LOCAL_TEE index)
  | block (ty : blocktype) (body : List instr) : PureHead (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) : PureHead (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) : PureHead (.IFELSE ty yes no)
  | br (depth : labelidx) : PureHead (.BR depth)
  | br_if (depth : labelidx) : PureHead (.BR_IF depth)
  | call (index : funcidx) : PureHead (.CALL index)
  | ret : PureHead .RETURN

end Itasca.Runtime.Abs
