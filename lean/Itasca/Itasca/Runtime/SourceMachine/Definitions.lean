import Itasca.Results.Definitions.SourceMachine
import Itasca.Results.Definitions.Resources

open WebAssembly


section SourceMachineState

/-!
### Flat source frames and decoding

Labels, frames and complete abstract states decode into nested specification evaluation
contexts; innermost source frames and labels are retained explicitly.
-/

namespace Itasca.SourceMachine

/-- One source control label, stored innermost first in a frame. -/
structure Label where
  /-- Types of values transferred when branching to this label. -/
  branchTypes : List valtype
  /-- Types of values produced on ordinary completion of this label. -/
  resultTypes : List valtype
  /-- Instructions resumed by a branch to the label. -/
  cont : List instr
  /-- Absolute value-stack height below the label's parameters. -/
  height : Nat
  /-- Enclosing code that resumes after this label exits. -/
  after : List instr

/-- One flat source function activation, including its current control stack. -/
structure AFrame where
  /-- Address of the source function being executed. -/
  fa : funcaddr
  /-- Result arity from the function's declared type. -/
  resultTypes : List valtype
  /-- Parameter/local values in source local-index order. -/
  locals : List val
  /-- Module-instance bindings used to resolve source indices. -/
  module : moduleinst
  /-- Innermost active source control label first. -/
  labels : List Label
  /-- Remaining ordinary source instructions in the current label. -/
  code : List instr
  /-- Current source operand values. -/
  vals : List val
  deriving Inhabited

/-- The complete flat source state decoded to one specification configuration. -/
structure AState where
  /-- Current source object store, including committed mutations. -/
  store : WebAssembly.store
  /-- The external invocation's ambient frame. -/
  ambient : frame
  /-- Current function activation first, followed by suspended callers. -/
  frames : List AFrame
  /-- Values returned when the final frame exits; empty while frames remain. -/
  results : List val

def Label.arity (label : Label) : Nat := label.branchTypes.length

def AFrame.arity (f : AFrame) : Nat := f.resultTypes.length

def AFrame.toFrame (f : AFrame) : frame := ⟨f.locals, f.module⟩

end Itasca.SourceMachine

namespace Itasca.SourceMachine

open WebAssembly

def decodeLabels : List Label → List val → List admininstr → List admininstr
  | [], values, code => vals values ++ code
  | label :: rest, values, code =>
      decodeLabels rest (values.take label.height)
        ([.LABEL_ label.arity label.cont (vals (values.drop label.height) ++ code)] ++
          label.after.map admininstr_instr)

def decodeFrames : List AFrame → List admininstr → List admininstr
  | [], inner => inner
  | f :: rest, inner =>
      decodeFrames rest [.FRAME_ f.arity f.toFrame
        (decodeLabels f.labels f.vals (inner ++ f.code.map admininstr_instr))]

def decode (s : AState) : config :=
  .mk_config (.mk_state s.store s.ambient) (decodeFrames s.frames (vals s.results))

end Itasca.SourceMachine

end SourceMachineState

section SourceMachineIndirectCalls

/-!
### Indirect source-call resolution

`resolve` identifies an indirect call's source target from its store, table and
signature information.
-/

namespace Itasca.SourceMachine.Indirect

open WebAssembly

def resolve (s : store) (f : AFrame) (table type position : Nat) : Option Nat :=
  match (fun_table ⟨s,f.toFrame⟩ (.mk_uN table)).REFS[position]? with
  | some (.REF_FUNC_ADDR address) =>
    match s.FUNCS[address]? with
    | some function => if fun_type ⟨s,f.toFrame⟩ (.mk_uN type)=function.TYPE then some address else none
    | none => none
  | _ => none

end Itasca.SourceMachine.Indirect

end SourceMachineIndirectCalls

section SourceMachineTypingAndCalls

namespace Itasca.SourceMachine

open WebAssembly

def integerVal (ty : Inn) (bits : Nat) : val :=
  .CONST (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits))

/-- Runtime module bindings describe the source typing context through checked
addresses. This avoids the generated Moduleinst_ok's unrelated export-membership
side condition, and admits genuine host functions by their declared type. -/
structure ModuleBindings (s : store) (m : moduleinst) (C : context) : Prop where
  types : C.TYPES = m.TYPES
  funcs : List.Forall₂ (fun address ty =>
    ∃ fn, s.FUNCS[address]? = some fn ∧ fn.TYPE = ty) m.FUNCS C.FUNCS
  globals : List.Forall₂ (fun address ty =>
    Externaddr_ok s (.GLOBAL address) (.GLOBAL ty)) m.GLOBALS C.GLOBALS
  tables : List.Forall₂ (fun address ty =>
    Externaddr_ok s (.TABLE address) (.TABLE ty)) m.TABLES C.TABLES
  mems : List.Forall₂ (fun address ty =>
    Externaddr_ok s (.MEM address) (.MEM ty)) m.MEMS C.MEMS
  elems : List.Forall₂ (fun address ty =>
    ∃ entry, s.ELEMS[address]? = some entry ∧ Eleminst_ok s entry ty) m.ELEMS C.ELEMS
  datas : List.Forall₂ (fun address ty =>
    ∃ entry, s.DATAS[address]? = some entry ∧ Datainst_ok s entry ty) m.DATAS C.DATAS
  wf : wf_context C

end Itasca.SourceMachine

end SourceMachineTypingAndCalls

/-! Source-instruction classifiers used by the simulation construction.
The public resource contract needs source frames and reductions, not these
instruction-family decompositions or supported-syntax certificates. -/

/-! ## SourceMachine / Float -/

section SourceMachineFloat

/-!
### Source float instructions

The float instruction family records source operations, operand/result types and
arities, including the relational floating-point choices of the specification.
-/

namespace Itasca.SourceMachine.Float

open WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

/-- Scalar float syntax, independent of compiler bytecode and native operations. -/
inductive Instruction where
  | unary (ty : Fnn) (op : unop_Fnn)
  | binary (ty : Fnn) (op : binop_Fnn)
  | compare (ty : Fnn) (op : relop_Fnn)
  | convert (source : Inn) (target : Fnn) (sign : sx)
  | truncate (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
  | reinterpretFloat (source : Fnn)
  | reinterpretInt (source : Inn)
  | promote
  | demote

def integerType : Fnn → Inn
  | .F32 => .I32
  | .F64 => .I64

def floatType : Inn → Fnn
  | .I32 => .F32
  | .I64 => .F64

def Instruction.input : Instruction → numtype
  | .unary ty _ | .binary ty _ | .compare ty _ => numtype_Fnn ty
  | .convert source _ _ | .reinterpretInt source => numtype_Inn source
  | .truncate source _ _ _ | .reinterpretFloat source => numtype_Fnn source
  | .promote => .F32
  | .demote => .F64

def Instruction.output : Instruction → numtype
  | .unary ty _ | .binary ty _ => numtype_Fnn ty
  | .compare _ _ => .I32
  | .convert _ target _ => numtype_Fnn target
  | .truncate _ target _ _ => numtype_Inn target
  | .reinterpretFloat source => numtype_Inn (integerType source)
  | .reinterpretInt source => numtype_Fnn (floatType source)
  | .promote => .F64
  | .demote => .F32

def Instruction.arity : Instruction → Nat
  | .binary _ _ | .compare _ _ => 2
  | _ => 1

def Instruction.source : Instruction → instr
  | .unary ty op => .UNOP (numtype_Fnn ty) (.mk_unop__1 ty op)
  | .binary ty op => .BINOP (numtype_Fnn ty) (.mk_binop__1 ty op)
  | .compare ty op => .RELOP (numtype_Fnn ty) (.mk_relop__1 ty op)
  | .convert source target sign => .CVTOP (numtype_Fnn target) (numtype_Inn source)
      (.mk_cvtop___1 source target (.CONVERT sign))
  | .truncate source target sign saturating => .CVTOP (numtype_Inn target) (numtype_Fnn source)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))
  | .reinterpretFloat source => .CVTOP (numtype_Inn (integerType source)) (numtype_Fnn source)
      (.mk_cvtop___2 source (integerType source) .REINTERPRET)
  | .reinterpretInt source => .CVTOP (numtype_Fnn (floatType source)) (numtype_Inn source)
      (.mk_cvtop___1 source (floatType source) .REINTERPRET)
  | .promote => .CVTOP .F64 .F32 (.mk_cvtop___3 .F32 .F64 .PROMOTE)
  | .demote => .CVTOP .F32 .F64 (.mk_cvtop___3 .F64 .F32 .DEMOTE)

end Itasca.SourceMachine.Float

end SourceMachineFloat

/-! ## SourceMachine / Memory -/

section SourceMachineMemory

/-!
### Source memory instruction descriptors

Packed widths and load/store families give source instructions, value types and natural
memory-operation shapes.
-/

namespace Itasca.SourceMachine.Memory

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

def Store.operation : Store → Option sz
  | .full _ => none
  | .packed _ width => some width.size

def Store.source (op : Store) (argument : memarg) : instr :=
  .STORE op.type op.operation argument

end Itasca.SourceMachine.Memory

end SourceMachineMemory

/-! ## SourceMachine / Numeric -/

section SourceMachineNumeric

/-!
### Source numeric instructions

Conversion and unary/operator families retain their source instructions and input/output
types independently of compiled execution.
-/

namespace Itasca.SourceMachine.Numeric

open WebAssembly.Builtins

/-- The three scalar integer width conversions, excluding float conversions. -/
inductive Conversion where
  | wrap | extendUnsigned | extendSigned

def Conversion.input : Conversion → Inn
  | .wrap => .I64
  | .extendUnsigned | .extendSigned => .I32

def Conversion.output : Conversion → Inn
  | .wrap => .I32
  | .extendUnsigned | .extendSigned => .I64

def Conversion.operator : Conversion → cvtop__
  | .wrap => .mk_cvtop___0 .I64 .I32 .WRAP
  | .extendUnsigned => .mk_cvtop___0 .I32 .I64 (.EXTEND .U)
  | .extendSigned => .mk_cvtop___0 .I32 .I64 (.EXTEND .S)

def Conversion.source (op : Conversion) : instr :=
  .CVTOP (numtype_Inn op.output) (numtype_Inn op.input) op.operator

/-- Exactly the integer unary instructions with scalar binary encodings. -/
inductive UnaryOperator : Inn → Type where
  | clz {ty} : UnaryOperator ty
  | ctz {ty} : UnaryOperator ty
  | popcnt {ty} : UnaryOperator ty
  | extend8 {ty} : UnaryOperator ty
  | extend16 {ty} : UnaryOperator ty
  | extend32 : UnaryOperator .I64

def UnaryOperator.operation {ty : Inn} : UnaryOperator ty → unop_Inn
  | .clz => .CLZ
  | .ctz => .CTZ
  | .popcnt => .POPCNT
  | .extend8 => .EXTEND 8
  | .extend16 => .EXTEND 16
  | .extend32 => .EXTEND 32

/-- All scalar integer numeric instructions, indexed independently of the
interpreter and compiler bytecode representation. -/
inductive Instruction where
  | binary (ty : Inn) (op : binop_Inn)
  | unary (ty : Inn) (op : UnaryOperator ty)
  | compare (ty : Inn) (op : relop_Inn)
  | eqz (ty : Inn)
  | conversion (op : Conversion)

def Instruction.source : Instruction → instr
  | .binary ty op => .BINOP (numtype_Inn ty) (.mk_binop__0 ty op)
  | .unary ty op => .UNOP (numtype_Inn ty) (.mk_unop__0 ty op.operation)
  | .compare ty op => .RELOP (numtype_Inn ty) (.mk_relop__0 ty op)
  | .eqz ty => .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)
  | .conversion op => op.source

def Instruction.input : Instruction → Inn
  | .binary ty _ | .unary ty _ | .compare ty _ | .eqz ty => ty
  | .conversion op => op.input

def Instruction.output : Instruction → Inn
  | .binary ty _ | .unary ty _ => ty
  | .compare _ _ | .eqz _ => .I32
  | .conversion op => op.output

def Instruction.arity : Instruction → Nat
  | .binary _ _ | .compare _ _ => 2
  | .unary _ _ | .eqz _ | .conversion _ => 1

end Itasca.SourceMachine.Numeric

end SourceMachineNumeric

/-! ## SourceMachine / Simd -/

section SourceMachineSimd

/-!
### Source SIMD instructions

Pure and memory signatures identify SIMD source instructions and their operand/result
shapes independently of runtime dispatch.
-/

namespace Itasca.SourceMachine.Simd

open WebAssembly

/-- Principal stack signatures of pure SIMD source instructions. This relation
uses source constructors only and is independent of the byte decoder. -/
inductive PureSignature : instr → List valtype → valtype → Prop where
  | wholeUnary op : PureSignature (.VVUNOP .V128 op) [.V128] .V128
  | wholeBinary op : PureSignature (.VVBINOP .V128 op) [.V128,.V128] .V128
  | wholeTernary op : PureSignature (.VVTERNOP .V128 op) [.V128,.V128,.V128] .V128
  | wholeTest op : PureSignature (.VVTESTOP .V128 op) [.V128] .I32
  | unary sh op : PureSignature (.VUNOP sh op) [.V128] .V128
  | binary sh op : PureSignature (.VBINOP sh op) [.V128,.V128] .V128
  | test sh op : PureSignature (.VTESTOP sh op) [.V128] .I32
  | relation sh op : PureSignature (.VRELOP sh op) [.V128,.V128] .V128
  | shift sh op : PureSignature (.VSHIFTOP sh op) [.V128,.I32] .V128
  | bitmask sh : PureSignature (.VBITMASK sh) [.V128] .I32
  | swizzle sh : PureSignature (.VSWIZZLE sh) [.V128,.V128] .V128
  | shuffle sh lanes : PureSignature (.VSHUFFLE sh lanes) [.V128,.V128] .V128
  | splat sh : PureSignature (.VSPLAT sh) [valtype_numtype (shunpack sh)] .V128
  | extract sh sign lane : PureSignature (.VEXTRACT_LANE sh sign lane) [.V128] (valtype_numtype (shunpack sh))
  | replace sh lane : PureSignature (.VREPLACE_LANE sh lane) [.V128,valtype_numtype (shunpack sh)] .V128
  | extendUnary first second op : PureSignature (.VEXTUNOP first second op) [.V128] .V128
  | extendBinary first second op : PureSignature (.VEXTBINOP first second op) [.V128,.V128] .V128
  | narrow first second sign : PureSignature (.VNARROW first second sign) [.V128,.V128] .V128
  | convert first second op : PureSignature (.VCVTOP first second op) [.V128] .V128

/-- The source stack signatures of SIMD memory operations. Width, alignment and
lane validity remain obligations of the generated instruction typing rules. -/
inductive MemorySignature : instr → List valtype → List valtype → Prop where
  | load operation argument : MemorySignature (.VLOAD .V128 operation argument) [.I32] [.V128]
  | loadLane width argument lane : MemorySignature (.VLOAD_LANE .V128 width argument lane) [.I32,.V128] [.V128]
  | store argument : MemorySignature (.VSTORE .V128 argument) [.I32,.V128] []
  | storeLane width argument lane : MemorySignature (.VSTORE_LANE .V128 width argument lane) [.I32,.V128] []

end Itasca.SourceMachine.Simd

namespace Itasca.SourceMachine

/-- SIMD source syntax, independent of opcode decoding and extracted execution.
The generated typing separately constrains shapes, immediates and memory use. -/
inductive SimdInstr : instr → Prop where
  | pure {source inputs output} (signature : Simd.PureSignature source inputs output) : SimdInstr source
  | constant value : SimdInstr (.VCONST .V128 value)
  | memory {source inputs outputs} (signature : Simd.MemorySignature source inputs outputs) : SimdInstr source

end Itasca.SourceMachine

end SourceMachineSimd

/-! ## SourceMachine / Stateful -/

section SourceMachineStateful

/-!
### Stateful source instructions

The instruction family and its signatures describe source operations that inspect or
mutate retained state.
-/

namespace Itasca.SourceMachine.Stateful

/-- Source-indexed reference, table and bulk-memory instructions. -/
inductive Instruction where
  | refNull (type : reftype)
  | refFunc (function : Nat)
  | refIsNull
  | tableGet (table : Nat)
  | tableSet (table : Nat)
  | tableSize (table : Nat)
  | tableGrow (table : Nat)
  | tableFill (table : Nat)
  | tableCopy (destination source : Nat)
  | tableInit (table element : Nat)
  | elemDrop (element : Nat)
  | memorySize
  | memoryGrow
  | memoryFill
  | memoryCopy
  | memoryInit (data : Nat)
  | dataDrop (data : Nat)

def Instruction.source : Instruction → instr
  | .refNull type => .REF_NULL type
  | .refFunc function => .REF_FUNC (.mk_uN function)
  | .refIsNull => .REF_IS_NULL
  | .tableGet table => .TABLE_GET (.mk_uN table)
  | .tableSet table => .TABLE_SET (.mk_uN table)
  | .tableSize table => .TABLE_SIZE (.mk_uN table)
  | .tableGrow table => .TABLE_GROW (.mk_uN table)
  | .tableFill table => .TABLE_FILL (.mk_uN table)
  | .tableCopy destination source => .TABLE_COPY (.mk_uN destination) (.mk_uN source)
  | .tableInit table element => .TABLE_INIT (.mk_uN table) (.mk_uN element)
  | .elemDrop element => .ELEM_DROP (.mk_uN element)
  | .memorySize => .MEMORY_SIZE
  | .memoryGrow => .MEMORY_GROW
  | .memoryFill => .MEMORY_FILL
  | .memoryCopy => .MEMORY_COPY
  | .memoryInit data => .MEMORY_INIT (.mk_uN data)
  | .dataDrop data => .DATA_DROP (.mk_uN data)

/-- Operand counts do not depend on the table element type. -/
def Instruction.arity : Instruction → Nat
  | .refNull _ | .refFunc _ | .tableSize _ | .elemDrop _ | .memorySize | .dataDrop _ => 0
  | .refIsNull | .tableGet _ | .memoryGrow => 1
  | .tableSet _ | .tableGrow _ => 2
  | .tableFill _ | .tableCopy .. | .tableInit .. | .memoryFill | .memoryCopy | .memoryInit _ => 3

/-- Canonical source index spaces determine the operand/result types. -/
inductive Signature (C : context) : Instruction → List valtype → List valtype → Prop where
  | refNull (type) : Signature C (.refNull type) [] [valtype_reftype type]
  | refFunc (index) (type : functype) (found : C.FUNCS[index]? = some type) :
      Signature C (.refFunc index) [] [.FUNCREF]
  | refIsNull (type) : Signature C .refIsNull [valtype_reftype type] [.I32]
  | tableGet (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableGet index) [.I32] [valtype_reftype type]
  | tableSet (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableSet index) [.I32, valtype_reftype type] []
  | tableSize (index) (type : tabletype) (found : C.TABLES[index]? = some type) :
      Signature C (.tableSize index) [] [.I32]
  | tableGrow (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableGrow index) [valtype_reftype type, .I32] [.I32]
  | tableFill (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableFill index) [.I32, valtype_reftype type, .I32] []
  | tableCopy (destination source) (type) (destinationBounds sourceBounds)
      (destinationFound : C.TABLES[destination]? = some (.mk_tabletype destinationBounds type))
      (sourceFound : C.TABLES[source]? = some (.mk_tabletype sourceBounds type)) :
      Signature C (.tableCopy destination source) [.I32, .I32, .I32] []
  | tableInit (table element) (type) (bounds)
      (tableFound : C.TABLES[table]? = some (.mk_tabletype bounds type))
      (elementFound : C.ELEMS[element]? = some type) :
      Signature C (.tableInit table element) [.I32, .I32, .I32] []
  | elemDrop (index) (type : reftype) (found : C.ELEMS[index]? = some type) :
      Signature C (.elemDrop index) [] []
  | memorySize (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memorySize [] [.I32]
  | memoryGrow (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryGrow [.I32] [.I32]
  | memoryFill (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryFill [.I32, .I32, .I32] []
  | memoryCopy (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryCopy [.I32, .I32, .I32] []
  | memoryInit (index) (type : memtype) (found : C.MEMS[0]? = some type)
      (dataFound : C.DATAS[index]? = some .OK) :
      Signature C (.memoryInit index) [.I32, .I32, .I32] []
  | dataDrop (index) (found : C.DATAS[index]? = some .OK) :
      Signature C (.dataDrop index) [] []

end Itasca.SourceMachine.Stateful

end SourceMachineStateful

/-! ## SourceMachine / InstructionSyntax -/

section SourceMachineInstructionSyntax

/-!
### Binary instruction families

`BinaryInstr` describes the source syntax accepted by the execution model.
Administrative progress measures belong to the internal simulation proof.
-/

namespace Itasca.SourceMachine

inductive BinaryInstr : instr → Prop where
  | nop : BinaryInstr .NOP
  | unreachable : BinaryInstr .UNREACHABLE
  | drop : BinaryInstr .DROP
  | const (ty : numtype) (value : num_) : BinaryInstr (.CONST ty value)
  | numeric (op : Itasca.SourceMachine.Numeric.Instruction) : BinaryInstr op.source
  | float (op : Float.Instruction) : BinaryInstr op.source
  | select : BinaryInstr (.SELECT none)
  | typed_select (ty : valtype) : BinaryInstr (.SELECT (some [ty]))
  | local_get (index : idx) : BinaryInstr (.LOCAL_GET index)
  | local_set (index : idx) : BinaryInstr (.LOCAL_SET index)
  | local_tee (index : idx) : BinaryInstr (.LOCAL_TEE index)
  | global_get (index : idx) : BinaryInstr (.GLOBAL_GET index)
  | global_set (index : idx) : BinaryInstr (.GLOBAL_SET index)
  | load (op : Memory.Load) (argument : memarg) : BinaryInstr (op.source argument)
  | store (op : Memory.Store) (argument : memarg) : BinaryInstr (op.source argument)
  | stateful (op : Stateful.Instruction) : BinaryInstr op.source
  | simd {source} : SimdInstr source → BinaryInstr source
  | block (ty : blocktype) (body : List instr) : Forall BinaryInstr body → BinaryInstr (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) : Forall BinaryInstr body → BinaryInstr (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) :
      Forall BinaryInstr yes → Forall BinaryInstr no → BinaryInstr (.IFELSE ty yes no)
  | br (depth : labelidx) : BinaryInstr (.BR depth)
  | br_if (depth : labelidx) : BinaryInstr (.BR_IF depth)
  | br_table (labels : List labelidx) (fallback : labelidx) : BinaryInstr (.BR_TABLE labels fallback)
  | call (index : funcidx) : BinaryInstr (.CALL index)
  | call_indirect (table : tableidx) (type : typeidx) : BinaryInstr (.CALL_INDIRECT table type)
  | ret : BinaryInstr .RETURN


end Itasca.SourceMachine

end SourceMachineInstructionSyntax

/-! ## Source function syntax -/

section SourceMachineSupport

namespace Itasca.SourceMachine

/-- Every defined function contains source instructions covered by the execution
semantics. Host behavior is governed separately by the host contract. -/
def FunctionsSupported (s : store) : Prop :=
  ∀ function ∈ s.FUNCS, match function.CODE with
    | .HOST _ => True
    | .FUNC _ _ body => Forall BinaryInstr body

end Itasca.SourceMachine

end SourceMachineSupport



namespace Itasca.Spec.Segment

/-- The initialization program prescribed by the generated element rule. -/
def elementProgram : elem → idx → List instr
  | .ELEM _ expressions mode, index => match mode with
    | .PASSIVE => []
    | .DECLARE => [.ELEM_DROP index]
    | .ACTIVE table offset => offset ++
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)),
         .CONST .I32 (.mk_num__0 .I32 (.mk_uN expressions.length)),
         .TABLE_INIT table index, .ELEM_DROP index]

/-- The initialization program for a single-memory data segment. -/
def dataProgram : data → idx → List instr
  | .DATA bytes mode, index => match mode with
    | .PASSIVE => []
    | .ACTIVE _ offset => offset ++
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)),
         .CONST .I32 (.mk_num__0 .I32 (.mk_uN bytes.length)),
         .MEMORY_INIT index, .DATA_DROP index]

def elementPrograms (segments : List elem) : List (List instr) :=
  (List.range segments.length).map (fun index => elementProgram segments[index]! (.mk_uN index))

def dataPrograms (segments : List data) : List (List instr) :=
  (List.range segments.length).map (fun index => dataProgram segments[index]! (.mk_uN index))

end Itasca.Spec.Segment


