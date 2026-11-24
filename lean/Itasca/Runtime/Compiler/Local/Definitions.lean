import Itasca.Module.Definitions
import Itasca.Binary.Definitions
import Itasca.Runtime.SourceMachine.Definitions
import Itasca.Runtime.Representation.Definitions
import Itasca.Results.Definitions.Compiler.Source

/-! ## Compiler / Local / EnvironmentDemand -/

section CompilerLocalEnvironmentDemand

/-!
### Environment compiler demand

Signature slot widths determine the environment-phase capacity and reservation
bounds. These are numerical premises about source metadata,
used to prove compiler acceptance independently of a successful output.
-/

/-!
## Signature slot demand

`signatureSlots` computes the slot requirement of a retained function signature.
-/

namespace Itasca.Compiler
open Itasca.Representation

open Aeneas Aeneas.Std

def signatureSlots (types : List Itasca.wasm_types.ValueType) : Nat :=
  slots (types.map Itasca.Translation.valueType)

end Itasca.Compiler

/-!
## Environment demand

`SourceEnvironmentDemand` records the storage demand supplied by independently
decoded environment metadata.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std Itasca

/-- Environment storage needed before compiling any function. Reservations
refer to the source tables themselves, without mentioning scheduler buffers. -/
structure SourceEnvironmentDemand (limits : runtime.compiler.CompileLimits)
    (env : Itasca.metadata.Env) (bound : Nat) : Prop where
  functionLimit : env.func_type_indices.length ≤ limits.max_functions.val
  typeLimit : env.types.length ≤ limits.max_types.val
  signatureWidths : ∀ type ∈ env.types.val,
    signatureSlots type.params.val ≤ U32.max ∧ signatureSlots type.results.val ≤ U32.max
  functionWidths : ∀ type ∈ env.func_types.val, signatureSlots type.params.val ≤ U32.max
  signatureReserve : env.types.length ≤ bound
  slotReserve : env.func_types.length ≤ bound
  functionReserve : env.func_type_indices.length ≤ bound

end Itasca.Compiler

end CompilerLocalEnvironmentDemand

/-! ## Compiler / Local / InitializerCosts -/

section CompilerLocalInitializerCosts

/-!
### Initializer source costs

Element and mapping costs bound initializer compilation from the independent source
declarations.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

/-- Exact remaining append allowance for element initializer rows and offsets. -/
def initializerElementCost (elements : List Itasca.metadata.Element) : Nat :=
  (elements.map (fun e => e.init.val.length + 3)).sum

/-- A source-derived upper bound on all retained initializer-map appends. -/
def initializerMappingCost (source : Itasca.metadata.Module) : Nat :=
  2 * source.env.globals.val.length + initializerElementCost source.env.elements.val +
  2 * source.tail.data.val.length

end Itasca.Compiler

end CompilerLocalInitializerCosts

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The source function context is fixed by the independently decoded module
metadata and the function's parameter, local and result declarations. -/
def sourceFunctionContext (env : Itasca.metadata.Env) (locals results : List valtype) : context :=
  { TYPES := env.types.val.map Itasca.Translation.Environment.funcType
    FUNCS := env.func_types.val.map Itasca.Translation.Environment.funcType
    GLOBALS := env.global_types.val.map Itasca.Translation.globalType
    TABLES := env.table_types.val.map Itasca.Translation.Environment.tableType
    MEMS := env.mem_types.val.map Itasca.Translation.Environment.memType
    ELEMS := Itasca.Translation.Environment.elementTypes env
    DATAS := Itasca.Translation.Environment.dataTypes env
    LOCALS := locals
    LABELS := []
    RETURN := some (.mk_list results) }


end Itasca.Compiler

/-! Internal helper vocabulary used by construction proofs. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- At module publication the complete data namespace comes from the parsed
tail. Code validation may have run before that tail, without a data-count
section; the supported scalar emission has no data-segment instruction. -/
def moduleFunctionContext (module : runtime.compiler.ExecutableModule)
    (locals results : List valtype) : context :=
  {sourceFunctionContext module.module.env locals results with
    DATAS := List.replicate module.module.tail.data.length datatype.OK}

end Itasca.Compiler


/-! Internal emission and control-layout certificates. Public clients use the runtime protocol; only construction proofs inspect these relations. -/

/-! ## Compiler / Local / Initializer -/

section CompilerLocalInitializer

open Itasca.Representation

/-!
### Initializer instruction syntax

Constant/initial instructions, literal bits and `InitializerCode` relate source
initializer expressions to syntactic compiled code.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

def initializerBits (lo hi : U64) : U128 :=
  ⟨(UScalar.cast .U128 lo).bv ||| ((UScalar.cast .U128 hi).bv <<< 64)⟩

inductive ConstantInstruction (function : runtime.bytecode.CompiledFunction)
    (dst : U32) : Itasca.wasm_types.ConstExpr → Itasca.wasm_types.ValueType → runtime.bytecode.Instr → Prop where
  | i32 (value : I32) (ty) : ConstantInstruction function dst (.I32 value) ty
      (.Const32 dst (IScalar.hcast .U32 value))
  | i64 (value : I64) (ty) : ConstantInstruction function dst (.I64 value) ty
      (.Const64 dst (IScalar.hcast .U64 value))
  | f32 (bits : U32) (ty) : ConstantInstruction function dst (.F32 bits) ty (.Const32 dst bits)
  | f64 (bits : U64) (ty) : ConstantInstruction function dst (.F64 bits) ty (.Const64 dst bits)
  | v128 (lo hi : U64) (ty) (pool : U32)
      (embedded : function.v128_pool.val[pool.val]? = some (initializerBits lo hi)) :
      ConstantInstruction function dst (.V128 lo hi) ty (.ConstV128 dst pool)
  | refNull (ty) (elem) : ConstantInstruction function dst (.RefNull elem) ty (.RefNull dst)
  | refFunc (ty) (index) : ConstantInstruction function dst (.RefFunc index) ty (.RefFunc dst index)
  | global (ty) (index) (scalar : ty ≠ .V128) :
      ConstantInstruction function dst (.GlobalGet index) ty (.GlobalGet dst index)
  | globalVector (index) :
      ConstantInstruction function dst (.GlobalGet index) .V128 (.GlobalGet2 dst index)

abbrev InitialInstruction (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (instruction : runtime.bytecode.Instr) :=
  ConstantInstruction function 0#u32 expr ty instruction

structure InitializerCode (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) : Prop where
  code : ∃ instruction, InitialInstruction function expr ty instruction ∧
    function.code.val = [instruction, .Return 0#u32 (initializerWidth ty)]
  capacity : function.slot_count = initializerWidth ty
  localSlots : function.local_slots = 0#u32
  paramSlots : function.param_slots = 0#u32
  locals : function.locals.val = []

end Itasca.Compiler

end CompilerLocalInitializer

/-! ## Compiler / Local / SegmentPrograms -/

section CompilerLocalSegmentPrograms

/-!
### Segment initialization programs

Per-segment instruction syntax and the complete initialization function retain
source order, segment identities, exact instruction lists and scratch capacity.
These programs write segments, unlike the read-only expression initializers.
-/

section

open Itasca.Representation

/-!
## Segment program syntax

Element/data program relations describe the source-ordered initialization instructions
emitted for each segment.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

inductive ElementProgram (function : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.metadata.Element) : List runtime.bytecode.Instr → Prop where
  | passive (mode : segment.mode = .Passive) : ElementProgram function index segment []
  | declarative (mode : segment.mode = .Declarative) (word : U32) (encoded : word.val = index) :
      ElementProgram function index segment [.ElemDrop word]
  | active (table : U32) (offset : Itasca.wasm_types.ConstExpr)
      (mode : segment.mode = .Active table offset)
      (word length entry : U32) (encoded : word.val = index) (count : length.val = segment.init.length)
      (descriptor : function.indirect.val[entry.val]? = some (word, table))
      (instruction : runtime.bytecode.Instr)
      (constant : ConstantInstruction function 0#u32 offset .I32 instruction) :
      ElementProgram function index segment
        [instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
          .TableInit 0#u32 entry, .ElemDrop word]

inductive DataProgram (function : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.metadata.Data) : List runtime.bytecode.Instr → Prop where
  | passive (mode : segment.mode = .Passive) : DataProgram function index segment []
  | active (memory : U32) (offset : Itasca.wasm_types.ConstExpr)
      (mode : segment.mode = .Active memory offset)
      (word length : U32) (encoded : word.val = index) (count : length.val = segment.init.length)
      (instruction : runtime.bytecode.Instr)
      (constant : ConstantInstruction function 0#u32 offset .I32 instruction) :
      DataProgram function index segment
        [instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
          .MemoryInit 0#u32 word, .DataDrop word]

end Itasca.Compiler

end

section

/-!
## Compiled segment programs

Segment program bodies and complete programs retain source order and target instructions
for initialization.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

/-- The initialization function is the source-ordered concatenation of segment
programs followed by a zero-result return. -/
structure SegmentProgramBody (module : runtime.compiler.ExecutableModule)
    (function : runtime.bytecode.CompiledFunction)
    (elementPrograms dataPrograms : List (List runtime.bytecode.Instr)) : Prop where
  elementCount : elementPrograms.length = module.module.env.elements.length
  dataCount : dataPrograms.length = module.module.tail.data.length
  elements : ∀ index segment, module.module.env.elements.val[index]? = some segment →
    ∃ instructions, elementPrograms[index]? = some instructions ∧ ElementProgram function index segment instructions
  datas : ∀ index segment, module.module.tail.data.val[index]? = some segment →
    ∃ instructions, dataPrograms[index]? = some instructions ∧ DataProgram function index segment instructions
  instructions : function.code.val = elementPrograms.flatten ++ dataPrograms.flatten ++ [.Return 0#u32 0#u32]
  capacity : function.slot_count = 0#u32 ∨ function.slot_count = 3#u32
  activeCapacity : (∃ (index : Nat) (instructions : List runtime.bytecode.Instr), elementPrograms[index]? = some instructions ∧ instructions.length = 5) ∨
    (∃ (index : Nat) (instructions : List runtime.bytecode.Instr), dataPrograms[index]? = some instructions ∧ instructions.length = 5) →
    function.slot_count = 3#u32
  localSlots : function.local_slots = 0#u32
  paramSlots : function.param_slots = 0#u32
  locals : function.locals.val = []

def SegmentProgram (module : runtime.compiler.ExecutableModule) (function : runtime.bytecode.CompiledFunction) : Prop :=
  ∃ elements datas, SegmentProgramBody module function elements datas

end Itasca.Compiler

end

end CompilerLocalSegmentPrograms

/-! ## Compiler / Local / IntegerEmission -/

section CompilerLocalIntegerEmission

/-!
### Integer opcode correspondence

Integer source operations determine their literal compiler opcode and concrete target
instruction.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std SourceMachine.Numeric

/-- Binary encodings of all scalar integer numeric instructions. -/
def integerOpcode : Instruction → U16
  | .binary .I32 (.ADD) => 106#u16
  | .binary .I32 (.SUB) => 107#u16
  | .binary .I32 (.MUL) => 108#u16
  | .binary .I32 (.DIV .S) => 109#u16
  | .binary .I32 (.DIV .U) => 110#u16
  | .binary .I32 (.REM .S) => 111#u16
  | .binary .I32 (.REM .U) => 112#u16
  | .binary .I32 (.AND) => 113#u16
  | .binary .I32 (.OR) => 114#u16
  | .binary .I32 (.XOR) => 115#u16
  | .binary .I32 (.SHL) => 116#u16
  | .binary .I32 (.SHR .S) => 117#u16
  | .binary .I32 (.SHR .U) => 118#u16
  | .binary .I32 (.ROTL) => 119#u16
  | .binary .I32 (.ROTR) => 120#u16
  | .binary .I64 (.ADD) => 124#u16
  | .binary .I64 (.SUB) => 125#u16
  | .binary .I64 (.MUL) => 126#u16
  | .binary .I64 (.DIV .S) => 127#u16
  | .binary .I64 (.DIV .U) => 128#u16
  | .binary .I64 (.REM .S) => 129#u16
  | .binary .I64 (.REM .U) => 130#u16
  | .binary .I64 (.AND) => 131#u16
  | .binary .I64 (.OR) => 132#u16
  | .binary .I64 (.XOR) => 133#u16
  | .binary .I64 (.SHL) => 134#u16
  | .binary .I64 (.SHR .S) => 135#u16
  | .binary .I64 (.SHR .U) => 136#u16
  | .binary .I64 (.ROTL) => 137#u16
  | .binary .I64 (.ROTR) => 138#u16
  | .compare .I32 (.EQ) => 70#u16
  | .compare .I32 (.NE) => 71#u16
  | .compare .I32 (.LT .S) => 72#u16
  | .compare .I32 (.LT .U) => 73#u16
  | .compare .I32 (.GT .S) => 74#u16
  | .compare .I32 (.GT .U) => 75#u16
  | .compare .I32 (.LE .S) => 76#u16
  | .compare .I32 (.LE .U) => 77#u16
  | .compare .I32 (.GE .S) => 78#u16
  | .compare .I32 (.GE .U) => 79#u16
  | .compare .I64 (.EQ) => 81#u16
  | .compare .I64 (.NE) => 82#u16
  | .compare .I64 (.LT .S) => 83#u16
  | .compare .I64 (.LT .U) => 84#u16
  | .compare .I64 (.GT .S) => 85#u16
  | .compare .I64 (.GT .U) => 86#u16
  | .compare .I64 (.LE .S) => 87#u16
  | .compare .I64 (.LE .U) => 88#u16
  | .compare .I64 (.GE .S) => 89#u16
  | .compare .I64 (.GE .U) => 90#u16
  | .unary .I32 .clz => 103#u16
  | .unary .I32 .ctz => 104#u16
  | .unary .I32 .popcnt => 105#u16
  | .unary .I32 .extend8 => 192#u16
  | .unary .I32 .extend16 => 193#u16
  | .unary .I64 .clz => 121#u16
  | .unary .I64 .ctz => 122#u16
  | .unary .I64 .popcnt => 123#u16
  | .unary .I64 .extend8 => 194#u16
  | .unary .I64 .extend16 => 195#u16
  | .unary .I64 .extend32 => 196#u16
  | .eqz .I32 => 69#u16
  | .eqz .I64 => 80#u16
  | .conversion .wrap => 167#u16
  | .conversion .extendUnsigned => 173#u16
  | .conversion .extendSigned => 172#u16

/-- The exact scalar bytecode constructor used by compiler and interpreter. -/
def integerInstruction (op : Instruction) (dst a b : U32) : runtime.bytecode.Instr :=
  match op with
  | .binary .I32 (.ADD) => .I32Add dst a b
  | .binary .I32 (.SUB) => .I32Sub dst a b
  | .binary .I32 (.MUL) => .I32Mul dst a b
  | .binary .I32 (.DIV .S) => .I32DivS dst a b
  | .binary .I32 (.DIV .U) => .I32DivU dst a b
  | .binary .I32 (.REM .S) => .I32RemS dst a b
  | .binary .I32 (.REM .U) => .I32RemU dst a b
  | .binary .I32 (.AND) => .I32And dst a b
  | .binary .I32 (.OR) => .I32Or dst a b
  | .binary .I32 (.XOR) => .I32Xor dst a b
  | .binary .I32 (.SHL) => .I32Shl dst a b
  | .binary .I32 (.SHR .S) => .I32ShrS dst a b
  | .binary .I32 (.SHR .U) => .I32ShrU dst a b
  | .binary .I32 (.ROTL) => .I32Rotl dst a b
  | .binary .I32 (.ROTR) => .I32Rotr dst a b
  | .binary .I64 (.ADD) => .I64Add dst a b
  | .binary .I64 (.SUB) => .I64Sub dst a b
  | .binary .I64 (.MUL) => .I64Mul dst a b
  | .binary .I64 (.DIV .S) => .I64DivS dst a b
  | .binary .I64 (.DIV .U) => .I64DivU dst a b
  | .binary .I64 (.REM .S) => .I64RemS dst a b
  | .binary .I64 (.REM .U) => .I64RemU dst a b
  | .binary .I64 (.AND) => .I64And dst a b
  | .binary .I64 (.OR) => .I64Or dst a b
  | .binary .I64 (.XOR) => .I64Xor dst a b
  | .binary .I64 (.SHL) => .I64Shl dst a b
  | .binary .I64 (.SHR .S) => .I64ShrS dst a b
  | .binary .I64 (.SHR .U) => .I64ShrU dst a b
  | .binary .I64 (.ROTL) => .I64Rotl dst a b
  | .binary .I64 (.ROTR) => .I64Rotr dst a b
  | .compare .I32 (.EQ) => .I32Eq dst a b
  | .compare .I32 (.NE) => .I32Ne dst a b
  | .compare .I32 (.LT .S) => .I32LtS dst a b
  | .compare .I32 (.LT .U) => .I32LtU dst a b
  | .compare .I32 (.GT .S) => .I32GtS dst a b
  | .compare .I32 (.GT .U) => .I32GtU dst a b
  | .compare .I32 (.LE .S) => .I32LeS dst a b
  | .compare .I32 (.LE .U) => .I32LeU dst a b
  | .compare .I32 (.GE .S) => .I32GeS dst a b
  | .compare .I32 (.GE .U) => .I32GeU dst a b
  | .compare .I64 (.EQ) => .I64Eq dst a b
  | .compare .I64 (.NE) => .I64Ne dst a b
  | .compare .I64 (.LT .S) => .I64LtS dst a b
  | .compare .I64 (.LT .U) => .I64LtU dst a b
  | .compare .I64 (.GT .S) => .I64GtS dst a b
  | .compare .I64 (.GT .U) => .I64GtU dst a b
  | .compare .I64 (.LE .S) => .I64LeS dst a b
  | .compare .I64 (.LE .U) => .I64LeU dst a b
  | .compare .I64 (.GE .S) => .I64GeS dst a b
  | .compare .I64 (.GE .U) => .I64GeU dst a b
  | .unary .I32 .clz => .I32Clz dst a b
  | .unary .I32 .ctz => .I32Ctz dst a b
  | .unary .I32 .popcnt => .I32Popcnt dst a b
  | .unary .I32 .extend8 => .I32Extend8S dst a b
  | .unary .I32 .extend16 => .I32Extend16S dst a b
  | .unary .I64 .clz => .I64Clz dst a b
  | .unary .I64 .ctz => .I64Ctz dst a b
  | .unary .I64 .popcnt => .I64Popcnt dst a b
  | .unary .I64 .extend8 => .I64Extend8S dst a b
  | .unary .I64 .extend16 => .I64Extend16S dst a b
  | .unary .I64 .extend32 => .I64Extend32S dst a b
  | .eqz .I32 => .I32Eqz dst a b
  | .eqz .I64 => .I64Eqz dst a b
  | .conversion .wrap => .I32WrapI64 dst a b
  | .conversion .extendUnsigned => .I64ExtendI32U dst a b
  | .conversion .extendSigned => .I64ExtendI32S dst a b

end Itasca.Compiler

end CompilerLocalIntegerEmission

/-! ## Compiler / Local / Emission -/

section CompilerLocalEmission

open Itasca.Representation

/-!
### Linear emission vocabulary

Target bytecode, integer operations, moves and `LinearEmission` relate a source
instruction to concrete code and its operand-type transition.
-/

namespace Itasca.Compiler

open Aeneas.Std

abbrev Bytecode := runtime.bytecode.Instr

/-- Binary operations currently related to the integer abstract machine. -/
inductive IntegerBinary where
  | add | sub | mul | eq | ne | ltU | gtU | leU | geU

def IntegerBinary.source (ty : Inn) : IntegerBinary → instr
  | .add => .BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD)
  | .sub => .BINOP (numtype_Inn ty) (.mk_binop__0 ty .SUB)
  | .mul => .BINOP (numtype_Inn ty) (.mk_binop__0 ty .MUL)
  | .eq => .RELOP (numtype_Inn ty) (.mk_relop__0 ty .EQ)
  | .ne => .RELOP (numtype_Inn ty) (.mk_relop__0 ty .NE)
  | .ltU => .RELOP (numtype_Inn ty) (.mk_relop__0 ty (.LT .U))
  | .gtU => .RELOP (numtype_Inn ty) (.mk_relop__0 ty (.GT .U))
  | .leU => .RELOP (numtype_Inn ty) (.mk_relop__0 ty (.LE .U))
  | .geU => .RELOP (numtype_Inn ty) (.mk_relop__0 ty (.GE .U))

def integerType : Inn → valtype
  | .I32 => .I32
  | .I64 => .I64

def IntegerBinary.output (ty : Inn) : IntegerBinary → valtype
  | .add | .sub | .mul => integerType ty
  | _ => .I32

def IntegerBinary.target (ty : Inn) (op : IntegerBinary) (a b : U32) : Bytecode :=
  match ty, op with
  | .I32, .add => .I32Add a a b
  | .I64, .add => .I64Add a a b
  | .I32, .sub => .I32Sub a a b
  | .I64, .sub => .I64Sub a a b
  | .I32, .mul => .I32Mul a a b
  | .I64, .mul => .I64Mul a a b
  | .I32, .eq => .I32Eq a a b
  | .I64, .eq => .I64Eq a a b
  | .I32, .ne => .I32Ne a a b
  | .I64, .ne => .I64Ne a a b
  | .I32, .ltU => .I32LtU a a b
  | .I64, .ltU => .I64LtU a a b
  | .I32, .gtU => .I32GtU a a b
  | .I64, .gtU => .I64GtU a a b
  | .I32, .leU => .I32LeU a a b
  | .I64, .leU => .I64LeU a a b
  | .I32, .geU => .I32GeU a a b
  | .I64, .geU => .I64GeU a a b

/-- A local transfer copies both words exactly for a vector value. -/
def move (ty : valtype) (dst src : U32) : Bytecode :=
  if width ty = 2 then .Copy2 dst src else .Copy dst src

/-- Each constructor fixes the emitted bytecode and its static operand slots.
The value-type stack is ordered from bottom to top. -/
inductive LinearEmission (locals : List valtype) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | nop (stack) : LinearEmission locals stack .NOP [] stack
  | drop (stack ty) : LinearEmission locals (stack ++ [ty]) .DROP [] stack
  | const32 (stack) (dst word : U32)
      (slot : dst.val = slots locals + slots stack) :
      LinearEmission locals stack (.CONST .I32 (.mk_num__0 .I32 (.mk_uN word.val)))
        [.Const32 dst word] (stack ++ [.I32])
  | const64 (stack) (dst : U32) (word : U64)
      (slot : dst.val = slots locals + slots stack) :
      LinearEmission locals stack (.CONST .I64 (.mk_num__0 .I64 (.mk_uN word.val)))
        [.Const64 dst word] (stack ++ [.I64])
  | binary (stack) (ty) (op : IntegerBinary) (a b : U32)
      (left : a.val = slots locals + slots stack) (right : b.val = a.val + 1) :
      LinearEmission locals (stack ++ [integerType ty, integerType ty])
        (op.source ty) [op.target ty a b] (stack ++ [op.output ty])
  | numeric (stack) (op : SourceMachine.Numeric.Instruction) (a b : U32)
      (left : a.val = slots locals + slots stack)
      (right : b.val = a.val + (op.arity - 1)) :
      LinearEmission locals (stack ++ List.replicate op.arity (integerType op.input))
        op.source [integerInstruction op a a b] (stack ++ [integerType op.output])
  | eqz32 (stack) (a : U32) (slot : a.val = slots locals + slots stack) :
      LinearEmission locals (stack ++ [.I32]) (.TESTOP .I32 (.mk_testop__0 .I32 .EQZ))
        [.I32Eqz a a a] (stack ++ [.I32])
  | eqz64 (stack) (a : U32) (slot : a.val = slots locals + slots stack) :
      LinearEmission locals (stack ++ [.I64]) (.TESTOP .I64 (.mk_testop__0 .I64 .EQZ))
        [.I64Eqz a a a] (stack ++ [.I32])
  | localGet (stack) (ty) (index localSlot stackSlot : U32)
      (localType : locals[index.val]? = some ty)
      (localPos : localSlot.val = offset locals index.val)
      (stackPos : stackSlot.val = slots locals + slots stack) :
      LinearEmission locals stack (.LOCAL_GET (.mk_uN index.val))
        [move ty stackSlot localSlot] (stack ++ [ty])
  | localSet (stack) (ty) (index localSlot stackSlot : U32)
      (localType : locals[index.val]? = some ty)
      (localPos : localSlot.val = offset locals index.val)
      (stackPos : stackSlot.val = slots locals + slots stack) :
      LinearEmission locals (stack ++ [ty]) (.LOCAL_SET (.mk_uN index.val))
        [move ty localSlot stackSlot] stack
  | localTee (stack) (ty) (index localSlot stackSlot : U32)
      (localType : locals[index.val]? = some ty)
      (localPos : localSlot.val = offset locals index.val)
      (stackPos : stackSlot.val = slots locals + slots stack) :
      LinearEmission locals (stack ++ [ty]) (.LOCAL_TEE (.mk_uN index.val))
        [move ty localSlot stackSlot] (stack ++ [ty])

end Itasca.Compiler

end CompilerLocalEmission

/-! ## Compiler / Local / Labels -/

section CompilerLocalLabels

/-!
### Structured control layout

Code segments, label targets, the implicit function exit and branch-table entries retain exact source continuations and concrete transfer coordinates.
-/

section

open Itasca.Representation

/-!
## Control labels and segments

Segments, label targets, block signatures and branch layouts retain source control
structure and concrete transfer coordinates.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- Concrete copy specialization shared by compiler and execution certificates. -/
def transferInstruction (dst src count : U32) : Bytecode :=
  if count.val = 1 then .Copy dst src else if count.val = 2 then .Copy2 dst src else .CopyN dst src count

/-- An exact bytecode fragment with absolute entry and continuation coordinates. -/
def Segment (code : List Bytecode) (pc : Nat) (instructions : List Bytecode) (next : Nat) : Prop :=
  ∃ front suffix, code = front ++ instructions ++ suffix ∧ front.length = pc ∧
    next = pc + instructions.length

/-- Static label information retained from structured source control. Branch
operands replace everything above `front`; a loop continuation re-enters its
source LOOP instruction and its bytecode LoopHead. -/
structure LabelTarget where
  front : List valtype
  branchTypes : List valtype
  resultTypes : List valtype
  target : U32
  /-- Fallthrough leaves the label here; an IF then arm may execute a skip. -/
  normalExit : Nat
  cont : List instr
  after : List instr
  normalLive : Bool
  branchLive : Bool

/-- Only a live normal exit can be reached by an empty source continuation. -/
def NormalLive (labels : List LabelTarget) : Prop :=
  ∀ label, labels.head? = some label → label.normalLive = true

/-- Source block signatures, including module-local type-index resolution. -/
inductive BlockSignature (types : List functype) : blocktype → List valtype → List valtype → Prop where
  | empty : BlockSignature types (._RESULT none) [] []
  | value (ty) : BlockSignature types (._RESULT (some ty)) [] [ty]
  | index (i : Nat) (params results)
      (lookup : types[i]? = some ⟨.mk_list params, .mk_list results⟩) :
      BlockSignature types (._IDX (.mk_uN i)) params results

/-- Transfer layout is independent of operand values and runtime state. -/
def BranchLayout (locals stack : List valtype) (label : LabelTarget)
    (dst src count : U32) : Prop :=
  ∃ discarded, stack = label.front ++ discarded ++ label.branchTypes ∧
    dst.val = slots locals + slots label.front ∧
    src.val = slots locals + slots (label.front ++ discarded) ∧
    count.val = slots label.branchTypes

/-- Exactly the branch instruction sequence emitted after fixups resolve. -/
def branchInstructions (dst src count target : U32) : List Bytecode :=
  if count = 0#u32 ∨ src = dst then [.Jump target]
  else [transferInstruction dst src count, .Jump target]

/-- Conditional branches either test directly, or guard a transfer/jump pair. -/
def branchIfInstructions (dst src count target cond resume : U32) : List Bytecode :=
  if count = 0#u32 ∨ src = dst then [.JumpIfNonZero cond target]
  else [.JumpIfZero cond resume, transferInstruction dst src count, .Jump target]

/-- A then arm either skips an explicit else arm or meets the shared exit
without emitting a jump (the binary IF-without-ELSE form). -/
inductive IfSkip (code : List Bytecode) (yesExit : Nat) (noEntry exit : U32) (yesNormal : Bool) : Prop where
  | emitted (fragment : Segment code yesExit (if yesNormal then [.Jump exit] else []) noEntry.val) :
      IfSkip code yesExit noEntry exit yesNormal
  | direct (normal : yesExit = exit.val) (otherwise : noEntry = exit) :
      IfSkip code yesExit noEntry exit yesNormal


end Itasca.Compiler

end

section

open Itasca.Representation

/-!
## Implicit function root exit

`functionRootLabel` interprets the actual epilogue and declared results, including the
zero-width exit of an unreachable nonvoid body.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- The actual epilogue determines whether the implicit root exit carries
its declared results. Dead nonvoid bodies may retain a zero-width epilogue. -/
def functionRootLabel (results : List valtype) (compiled : runtime.bytecode.CompiledFunction)
    (epilogue : U32) : LabelTarget :=
  let live := match compiled.code.val[epilogue.val]? with
    | some (.Return _ count) => decide (count.val = slots results)
    | _ => false
  ⟨[], results, results, epilogue, epilogue.val, [], [], live, live⟩

end Itasca.Compiler

end

section

open Itasca.Representation

/-!
## Branch-table layout

Branch-table entries and layouts relate source label depths to the concrete table
retained by emitted control code.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- An emitted table destination has the ordinary branch layout and exact
transfer/jump fragment for its source depth. -/
def BranchTableEntry (locals : List valtype) (labels : List LabelTarget)
    (stack : List valtype) (code : List Bytecode) (depth : labelidx) (entry : U32) (next : Nat) : Prop :=
  ∃ label dst src count fragmentEnd,
    labels[proj_uN_0 depth]? = some label ∧ label.branchLive = true ∧
    BranchLayout locals stack label dst src count ∧
    Segment code entry.val (branchInstructions dst src count label.target) fragmentEnd ∧
    fragmentEnd ≤ next ∧ next ≤ code.length

/-- Pure compiler evidence for a branch table, including its default entry.
Every retained side-table PC is tied to an emitted branch fragment. -/
structure BranchTableLayout (jumpTables : List U32) (locals : List valtype)
    (labels : List LabelTarget) (stack : List valtype) (code : List Bytecode)
    (depths : List labelidx) (fallback : labelidx) (pc next : Nat)
    (selector start len : U32) : Prop where
  selectorSlot : selector.val = slots locals + slots stack
  length : len.val = depths.length+1
  instruction : code[pc]? = some (.JumpTable selector start len)
  arithmetic : start.val + depths.length ≤ U32.max
  entries : ∀ index depth, (depths ++ [fallback])[index]? = some depth →
    ∃ entry, jumpTables[start.val+index]? = some entry ∧
      BranchTableEntry locals labels stack code depth entry next

end Itasca.Compiler

end

end CompilerLocalLabels

/-! ## Compiler / Local / StructuredCode -/

section CompilerLocalStructuredCode

open Itasca.Representation

/-!
### Structured code certificates

`StructuredCode` and its target/normal/point relations retain the branch and
continuation geometry of structured emitted code.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- Structured compiler evidence parameterized only by its syntactic emitted-head relation. -/
inductive StructuredCode (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List U32 → List LabelTarget → List valtype → List instr → Nat → Nat → List valtype → Prop where
  | nil (labels stack pc) (bound : pc ≤ code.length) (live : NormalLive labels) :
      StructuredCode emission types functions returns locals code jumpTables labels stack [] pc pc stack
  | linear {labels before middle after instruction source emitted pc tail next}
      (head : emission before instruction emitted middle)
      (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback)
      (fragment : Segment code pc emitted tail)
      (rest : StructuredCode emission types functions returns locals code jumpTables labels middle source tail next after) :
      StructuredCode emission types functions returns locals code jumpTables labels before (instruction :: source) pc next after
  | skip {labels stack source pc target next final}
      (forward : pc < target.val)
      (instruction : code[pc]? = some (.Jump target))
      (rest : StructuredCode emission types functions returns locals code jumpTables labels stack source target.val next final) :
      StructuredCode emission types functions returns locals code jumpTables labels stack source pc next final
  | block {labels front params results after body bt pc normalExit branchExit next final normalLive branchLive}
      (signature : BlockSignature types bt params results)
      (bodyCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
        (front ++ params) body pc normalExit (front ++ results))
      (rest : normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after normalExit next final)
      (targetRest : branchLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after branchExit.val next final)
      (bounds : pc ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.BLOCK bt body :: after) pc next final
  | loop {labels front params results after body bt entry exit next final normalLive}
      (signature : BlockSignature types bt params results)
      (head : code[entry.val]? = some .LoopHead)
      (bodyCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
        (front ++ params) body (entry.val + 1) exit (front ++ results))
      (rest : normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit next final)
      (bounds : entry.val ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.LOOP bt body :: after) entry.val next final
  | ifElse {labels front params results after yes no bt pc yesExit noEntry exit next final cond yesNormal yesBranch noNormal noBranch}
      (signature : BlockSignature types bt params results)
      (condition : cond.val = slots locals + slots (front ++ params))
      (guard : code[pc]? = some (.JumpIfZero cond noEntry))
      (yesCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
        (front ++ params) yes (pc + 1) yesExit (front ++ results))
      (skip : IfSkip code yesExit noEntry exit yesNormal)
      (noCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, exit, exit.val, [], after, noNormal, noBranch⟩ :: labels)
        (front ++ params) no noEntry.val exit.val (front ++ results))
      (rest : yesNormal = true ∨ yesBranch = true ∨ noNormal = true ∨ noBranch = true →
        StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit.val next final)
      (bounds : pc + 1 ≤ next ∧ noEntry.val ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params ++ [.I32])
        (.IFELSE bt yes no :: after) pc next final
  | branch {labels stack after depth label dst src count pc fragmentEnd next final}
      (lookup : labels[depth]? = some label)
      (live : label.branchLive = true)
      (layout : BranchLayout locals stack label dst src count)
      (fragment : Segment code pc (branchInstructions dst src count label.target) fragmentEnd)
      (remaining : fragmentEnd ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels stack (.BR (.mk_uN depth) :: after) pc next final
  | branchIf {labels stack after depth label dst src count cond resume pc next final}
      (lookup : labels[depth]? = some label)
      (live : label.branchLive = true)
      (layout : BranchLayout locals stack label dst src count)
      (condition : cond.val = slots locals + slots stack)
      (fragment : Segment code pc (branchIfInstructions dst src count label.target cond resume) resume.val)
      (rest : StructuredCode emission types functions returns locals code jumpTables labels stack after resume.val next final) :
      StructuredCode emission types functions returns locals code jumpTables labels (stack ++ [.I32])
        (.BR_IF (.mk_uN depth) :: after) pc next final
  | call {labels front params results after index base pc next final}
      (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
      (arguments : base.val = slots locals + slots front)
      (instruction : code[pc]? = some (.Call index base))
      (rest : StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after (pc + 1) next final) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.CALL (.mk_uN index.val) :: after) pc next final
  | unreachable {labels stack after pc next final}
      (instruction : code[pc]? = some .Unreachable)
      (remaining : pc + 1 ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels stack (.UNREACHABLE :: after) pc next final
  | return_ {labels front after src count pc next final}
      (source : src.val = slots locals + slots front)
      (size : count.val = slots returns)
      (instruction : code[pc]? = some (.Return src count))
      (remaining : pc + 1 ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ returns) (.RETURN :: after) pc next final

  | branchTable {first rest labels stack after depths fallback pc next final selector start len}
      (gate : emission (stack ++ [.I32]) (.BR_TABLE depths fallback) [.JumpTable selector start len] stack)
      (table : BranchTableLayout (first :: rest) locals labels stack code depths fallback pc next selector start len)
      (bounds : pc + 1 ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code (first :: rest) labels
        (stack ++ [.I32]) (.BR_TABLE depths fallback :: after) pc next final


end Itasca.Compiler

end CompilerLocalStructuredCode

/-! ## Compiler / Local / StructuredFunction -/

section CompilerLocalStructuredFunction

open Itasca.Representation

/-!
### Structured function syntax

`StructuredFunctionCode` connects one source function and its frame layout to structured
target code and its epilogue.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- Complete retained syntax/layout evidence for one defined function. The
well-formedness field is the actual bytecode check, not execution correctness. -/
structure StructuredFunctionCode (emit : List valtype → instr → List Bytecode → List valtype → Prop) (typeTable functions : List functype)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop where
  signature : typeTable[compiled.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩
  locals : compiled.locals.val.map Itasca.Translation.valueType = params ++ declared
  parameterSlots : compiled.param_slots.val = slots params
  localSlots : compiled.local_slots.val = slots (params ++ declared)
  capacity : compiled.local_slots.val ≤ compiled.slot_count.val
  fetchBound : compiled.code.val.length ≤ U32.max
  checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true
  bodyCode : StructuredCode emit typeTable functions results (params ++ declared) compiled.code.val compiled.jump_tables.val
    [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results
  returnCode : ∃ count, compiled.code.val[epilogue.val]? = some (.Return compiled.local_slots count)
  endPosition : compiled.code.val.length = epilogue.val + 1

end Itasca.Compiler

end CompilerLocalStructuredFunction

/-! ## Compiler / Local / Tables -/

section CompilerLocalTables

/-!
### Function-local compiler tables

`CompilerTables` retains the auxiliary tables and constant pool used to interpret a
compiled function's instruction operands.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

/-- Function-local syntactic tables used by emitted instructions. -/
structure CompilerTables where
  /-- Function-local indirect-call signature index pairs. -/
  indirect : List (U32 × U32)
  /-- SIMD immediates referenced by emitted instructions. -/
  simd : List runtime.bytecode.SimdImmediate
  /-- Raw 128-bit literals in the function's constant pool. -/
  constants : List U128
  /-- Published target entries selected by branch-table instructions. -/
  jumpTables : List U32

end Itasca.Compiler

namespace Itasca.Compiler.CompilerTables

open Aeneas Aeneas.Std

def ofFunction (function : runtime.bytecode.CompiledFunction) : CompilerTables :=
  ⟨function.indirect.val,function.simd.val,function.v128_pool.val,function.jump_tables.val⟩

end Itasca.Compiler.CompilerTables

end CompilerLocalTables

/-! ## Compiler / Local / FunctionCode -/

section CompilerLocalFunctionCode

/-!
### Indexed function certificates

Contextual function syntax retains the actual jump table and source/layout evidence,
without an execution premise.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- Contextual function syntax with the actual retained jump table. The
certificate contains source/layout evidence, never an execution premise. -/
def IndexedFunctionCode
    (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop)
    (C : context) (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS=params++declared ∧
  StructuredFunctionCode (emission (CompilerTables.ofFunction compiled) C)
    C.TYPES C.FUNCS params declared results body compiled epilogue

def DefinedIndexedFunctionCode
    (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop)
    (env : Itasca.metadata.Env) (typeIndex : U32) (source : funccode)
    (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  compiled.type_index=typeIndex ∧ ∃ signature declared body epilogue,
    env.types.val[typeIndex.val]?=some signature ∧
    source=.FUNC (.mk_uN typeIndex.val) (declared.map local.LOCAL) body ∧
    IndexedFunctionCode emission (sourceFunctionContext env
      (signature.params.val.map Itasca.Translation.valueType++declared)
      (signature.results.val.map Itasca.Translation.valueType))
      (signature.params.val.map Itasca.Translation.valueType) declared
      (signature.results.val.map Itasca.Translation.valueType) body compiled epilogue

end Itasca.Compiler

end CompilerLocalFunctionCode

/-! ## Compiler / Local / IndirectCallEmission -/

section CompilerLocalIndirectCallEmission

open Itasca.Representation

/-!
### Indirect-call emission

`IndirectCallEmission` retains the function-local indirect signature metadata and
concrete code for a source indirect call.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- An indirect call retains both source indices and the actual function-local
pair entry. The table selector follows the full parameter word region. -/
inductive IndirectCallEmission (pairs : List (U32 × U32)) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | call (front params results : List valtype) (typeIndex tableIndex entry index base : U32)
      (bounds : limits)
      (signature : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
      (table : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
      (pair : pairs[entry.val]? = some (tableIndex,typeIndex))
      (basePosition : base.val = slots C.LOCALS + slots front)
      (indexPosition : index.val = base.val + slots params) :
      IndirectCallEmission pairs C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val))
        [.CallIndirect entry index base] (front ++ results)

end Itasca.Compiler

end CompilerLocalIndirectCallEmission

/-! ## Compiler / Local / InitializerMappings -/

section CompilerLocalInitializerMappings

/-!
### Source initializer mappings

Source globals, element expressions and active-segment offsets select retained
read-only initializer functions in source order. These mappings exclude the
separate segment-writing program, whose certificate lives in SegmentPrograms.
-/

section

/-!
## Source element offsets

`sourceElementOffset` interprets active and inactive element modes for initializer
compilation.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

def sourceElementOffset (segment : Itasca.metadata.Element) : Option Itasca.wasm_types.ConstExpr :=
  match segment.mode with
  | .Active _ expr => some expr
  | .Passive | .Declarative => none

end Itasca.Compiler

end

section

/-!
## Initializer entry positions

`InitializerAt`, entry collections and offset initializers retain source ordering and
the exact initializer positions in compiled code.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

def InitializerAt (functions : List runtime.bytecode.CompiledFunction)
    (index : Usize) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) : Prop :=
  ∃ code, functions[index.val]? = some code ∧ InitializerCode code expr ty

/-- Indexed source expressions and their retained synthetic functions. -/
def InitializerEntries (functions : List runtime.bytecode.CompiledFunction)
    (expressions : List Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (indices : List Usize) : Prop :=
  List.Forall₂ (fun expr index => InitializerAt functions index expr ty) expressions indices

def GlobalInitializerEntries (functions : List runtime.bytecode.CompiledFunction)
    (globals : List Itasca.metadata.Global) (indices : List Usize) : Prop :=
  List.Forall₂ (fun global index => InitializerAt functions index global.init global.gtype.valtype)
    globals indices

def OffsetInitializer (functions : List runtime.bytecode.CompiledFunction)
    (expr : Option Itasca.wasm_types.ConstExpr) (index : Option Usize) : Prop :=
  match expr, index with
  | none, none => True
  | some expr, some index => InitializerAt functions index expr .I32
  | _, _ => False

end Itasca.Compiler

end

section

open Itasca.Representation

/-!
## Published initializer mappings

Element values/offsets, data offsets and complete initializer mappings connect source
declarations to their compiled initializer entries.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

def ElementValueMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.metadata.Element) (rows : List (alloc.vec.Vec Usize)) : Prop :=
  List.Forall₂ (fun segment indices => InitializerEntries functions segment.init.val
    (Itasca.Module.Constants.referenceValueType segment.elem) indices.val) segments rows

def ElementOffsetMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.metadata.Element) (offsets : List (Option Usize)) : Prop :=
  List.Forall₂ (fun segment offset => OffsetInitializer functions (sourceElementOffset segment) offset)
    segments offsets

def sourceDataOffset (segment : Itasca.metadata.Data) : Option Itasca.wasm_types.ConstExpr :=
  match segment.mode with
  | .Active _ expr => some expr
  | .Passive => none

def DataOffsetMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.metadata.Data) (offsets : List (Option Usize)) : Prop :=
  List.Forall₂ (fun segment offset => OffsetInitializer functions (sourceDataOffset segment) offset)
    segments offsets

/-- Source-indexed certificates for every retained read-only initializer. The
separate segment-writing initialization function is not covered by this record. -/
structure InitializerMappings (module : runtime.compiler.ExecutableModule) : Prop where
  globals : GlobalInitializerEntries module.functions.val module.module.env.globals.val module.global_initializers.val
  elementValues : ElementValueMappings module.functions.val module.module.env.elements.val module.element_initializers.val
  elementOffsets : ElementOffsetMappings module.functions.val module.module.env.elements.val module.element_offsets.val
  dataOffsets : DataOffsetMappings module.functions.val module.module.tail.data.val module.data_offsets.val

end Itasca.Compiler

end

end CompilerLocalInitializerMappings

/-! ## Compiler / Local / ScalarOperations -/

section CompilerLocalScalarOperations

/-!
### Scalar instruction emission

Float, global, memory and select instruction relations record the exact target
instructions and physical operand slots. ScalarEmission combines these relations
with integer operations; runtime simulation proves their execution behavior.
-/

section

/-!
## Float instruction constructors

`floatInstruction` maps source float operations and operand positions to concrete target
instructions.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

def floatInstruction (op : SourceMachine.Float.Instruction) (dst a b : U32) : runtime.bytecode.Instr :=
  match op with
  | .unary .F32 .ABS => .F32Abs dst a b
  | .unary .F32 .NEG => .F32Neg dst a b
  | .unary .F32 .CEIL => .F32Ceil dst a b
  | .unary .F32 .FLOOR => .F32Floor dst a b
  | .unary .F32 .TRUNC => .F32Trunc dst a b
  | .unary .F32 .NEAREST => .F32Nearest dst a b
  | .unary .F32 .SQRT => .F32Sqrt dst a b
  | .unary .F64 .ABS => .F64Abs dst a b
  | .unary .F64 .NEG => .F64Neg dst a b
  | .unary .F64 .CEIL => .F64Ceil dst a b
  | .unary .F64 .FLOOR => .F64Floor dst a b
  | .unary .F64 .TRUNC => .F64Trunc dst a b
  | .unary .F64 .NEAREST => .F64Nearest dst a b
  | .unary .F64 .SQRT => .F64Sqrt dst a b
  | .binary .F32 .ADD => .F32Add dst a b
  | .binary .F32 .SUB => .F32Sub dst a b
  | .binary .F32 .MUL => .F32Mul dst a b
  | .binary .F32 .DIV => .F32Div dst a b
  | .binary .F32 .MIN => .F32Min dst a b
  | .binary .F32 .MAX => .F32Max dst a b
  | .binary .F32 .COPYSIGN => .F32Copysign dst a b
  | .binary .F64 .ADD => .F64Add dst a b
  | .binary .F64 .SUB => .F64Sub dst a b
  | .binary .F64 .MUL => .F64Mul dst a b
  | .binary .F64 .DIV => .F64Div dst a b
  | .binary .F64 .MIN => .F64Min dst a b
  | .binary .F64 .MAX => .F64Max dst a b
  | .binary .F64 .COPYSIGN => .F64Copysign dst a b
  | .compare .F32 .EQ => .F32Eq dst a b
  | .compare .F32 .NE => .F32Ne dst a b
  | .compare .F32 .LT => .F32Lt dst a b
  | .compare .F32 .GT => .F32Gt dst a b
  | .compare .F32 .LE => .F32Le dst a b
  | .compare .F32 .GE => .F32Ge dst a b
  | .compare .F64 .EQ => .F64Eq dst a b
  | .compare .F64 .NE => .F64Ne dst a b
  | .compare .F64 .LT => .F64Lt dst a b
  | .compare .F64 .GT => .F64Gt dst a b
  | .compare .F64 .LE => .F64Le dst a b
  | .compare .F64 .GE => .F64Ge dst a b
  | .convert .I32 .F32 .S => .F32ConvertI32S dst a b
  | .convert .I32 .F32 .U => .F32ConvertI32U dst a b
  | .convert .I32 .F64 .S => .F64ConvertI32S dst a b
  | .convert .I32 .F64 .U => .F64ConvertI32U dst a b
  | .convert .I64 .F32 .S => .F32ConvertI64S dst a b
  | .convert .I64 .F32 .U => .F32ConvertI64U dst a b
  | .convert .I64 .F64 .S => .F64ConvertI64S dst a b
  | .convert .I64 .F64 .U => .F64ConvertI64U dst a b
  | .truncate .F32 .I32 .S false => .I32TruncF32S dst a b
  | .truncate .F32 .I32 .S true => .I32TruncSatF32S dst a b
  | .truncate .F32 .I32 .U false => .I32TruncF32U dst a b
  | .truncate .F32 .I32 .U true => .I32TruncSatF32U dst a b
  | .truncate .F32 .I64 .S false => .I64TruncF32S dst a b
  | .truncate .F32 .I64 .S true => .I64TruncSatF32S dst a b
  | .truncate .F32 .I64 .U false => .I64TruncF32U dst a b
  | .truncate .F32 .I64 .U true => .I64TruncSatF32U dst a b
  | .truncate .F64 .I32 .S false => .I32TruncF64S dst a b
  | .truncate .F64 .I32 .S true => .I32TruncSatF64S dst a b
  | .truncate .F64 .I32 .U false => .I32TruncF64U dst a b
  | .truncate .F64 .I32 .U true => .I32TruncSatF64U dst a b
  | .truncate .F64 .I64 .S false => .I64TruncF64S dst a b
  | .truncate .F64 .I64 .S true => .I64TruncSatF64S dst a b
  | .truncate .F64 .I64 .U false => .I64TruncF64U dst a b
  | .truncate .F64 .I64 .U true => .I64TruncSatF64U dst a b
  | .reinterpretFloat .F32 => .I32ReinterpretF32 dst a b
  | .reinterpretFloat .F64 => .I64ReinterpretF64 dst a b
  | .reinterpretInt .I32 => .F32ReinterpretI32 dst a b
  | .reinterpretInt .I64 => .F64ReinterpretI64 dst a b
  | .promote => .F64PromoteF32 dst a b
  | .demote => .F32DemoteF64 dst a b

end Itasca.Compiler

end

section

/-!
## Global instruction constructors

Width-specific global get/set constructors identify the emitted instructions used by
scalar emission relations.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std
open Aeneas.Std.Result

def globalGetInstruction (wide : Bool) (dst index : U32) : runtime.bytecode.Instr :=
  if wide then .GlobalGet2 dst index else .GlobalGet dst index

def globalSetInstruction (wide : Bool) (src index : U32) : runtime.bytecode.Instr :=
  if wide then .GlobalSet2 src index else .GlobalSet src index

end Itasca.Compiler

end

section

/-!
## Memory opcode correspondence

Load/store source descriptors determine their literal compiler opcodes and emitted
instruction constructors.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

def memoryLoadOpcode : SourceMachine.Memory.Load → U16
  | .full .I32 => 40#u16
  | .full .I64 => 41#u16
  | .full .F32 => 42#u16
  | .full .F64 => 43#u16
  | .packed .I32 .byte .S => 44#u16
  | .packed .I32 .byte .U => 45#u16
  | .packed .I32 .half .S => 46#u16
  | .packed .I32 .half .U => 47#u16
  | .packed .I64 .byte .S => 48#u16
  | .packed .I64 .byte .U => 49#u16
  | .packed .I64 .half .S => 50#u16
  | .packed .I64 .half .U => 51#u16
  | .packed .I64 .word .S => 52#u16
  | .packed .I64 .word .U => 53#u16

def memoryStoreOpcode : SourceMachine.Memory.Store → U16
  | .full .I32 => 54#u16
  | .full .I64 => 55#u16
  | .full .F32 => 56#u16
  | .full .F64 => 57#u16
  | .packed .I32 .byte => 58#u16
  | .packed .I32 .half => 59#u16
  | .packed .I64 .byte => 60#u16
  | .packed .I64 .half => 61#u16
  | .packed .I64 .word => 62#u16

def memoryLoadInstruction (op : SourceMachine.Memory.Load) (dst address offset : U32) : runtime.bytecode.Instr :=
  match op with
  | .full .I32 => .I32Load dst address offset
  | .full .I64 => .I64Load dst address offset
  | .full .F32 => .F32Load dst address offset
  | .full .F64 => .F64Load dst address offset
  | .packed .I32 .byte .S => .I32Load8S dst address offset
  | .packed .I32 .byte .U => .I32Load8U dst address offset
  | .packed .I32 .half .S => .I32Load16S dst address offset
  | .packed .I32 .half .U => .I32Load16U dst address offset
  | .packed .I64 .byte .S => .I64Load8S dst address offset
  | .packed .I64 .byte .U => .I64Load8U dst address offset
  | .packed .I64 .half .S => .I64Load16S dst address offset
  | .packed .I64 .half .U => .I64Load16U dst address offset
  | .packed .I64 .word .S => .I64Load32S dst address offset
  | .packed .I64 .word .U => .I64Load32U dst address offset

def memoryStoreInstruction (op : SourceMachine.Memory.Store) (address value offset : U32) : runtime.bytecode.Instr :=
  match op with
  | .full .I32 => .I32Store address value offset
  | .full .I64 => .I64Store address value offset
  | .full .F32 => .F32Store address value offset
  | .full .F64 => .F64Store address value offset
  | .packed .I32 .byte => .I32Store8 address value offset
  | .packed .I32 .half => .I32Store16 address value offset
  | .packed .I64 .byte => .I64Store8 address value offset
  | .packed .I64 .half => .I64Store16 address value offset
  | .packed .I64 .word => .I64Store32 address value offset

end Itasca.Compiler

end

section

/-!
## Select instruction constructor

`selectInstruction` chooses the width-specific target instruction for the supplied
physical operand slots.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std
open Aeneas.Std.Result

def selectInstruction (wide : Bool) (left right condition : U32) : runtime.bytecode.Instr :=
  if wide then .Select2 left right condition else .Select left right condition

end Itasca.Compiler

end

end CompilerLocalScalarOperations

/-! ## Compiler / Local / ScalarEmission -/

section CompilerLocalScalarEmission

/-!
### Scalar instruction emission

Ordinary scalar lowering and explicitly typed select retain exact source instructions, operand layouts and emitted bytecode. Execution behavior is proved separately.
-/

section

open Itasca.Representation

/-!
## Scalar emission cases

`ScalarEmission` collects the source/target instruction cases for ordinary scalar
lowering.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- Scalar instructions, including those resolved against the module's globals and
memory, with their source typing context. The relation fixes syntax, operand layout
and emitted bytecode only. -/
inductive ScalarEmission (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | linear {before instruction emitted after}
      (emission : LinearEmission C.LOCALS before instruction emitted after) :
      ScalarEmission C before instruction emitted after
  | float32 (stack) (dst bits : U32)
      (slot : dst.val = slots C.LOCALS + slots stack) :
      ScalarEmission C stack (.CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 bits.val)))
        [.Const32 dst bits] (stack ++ [.F32])
  | float64 (stack) (dst : U32) (bits : U64)
      (slot : dst.val = slots C.LOCALS + slots stack) :
      ScalarEmission C stack (.CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 bits.val)))
        [.Const64 dst bits] (stack ++ [.F64])
  | select (stack) (ty : valtype) (left right condition : U32)
      (leftSlot : left.val = slots C.LOCALS + slots stack)
      (rightSlot : right.val = left.val + width ty)
      (conditionSlot : condition.val = right.val + width ty) :
      ScalarEmission C (stack ++ [ty, ty, .I32]) (.SELECT none)
        [selectInstruction (decide (width ty = 2)) left right condition] (stack ++ [ty])
  | globalGet (stack) (mutability : «mut») (ty : valtype) (index dst : U32)
      (globalType : C.GLOBALS[index.val]? = some (.mk_globaltype mutability ty))
      (slot : dst.val = slots C.LOCALS + slots stack) :
      ScalarEmission C stack (.GLOBAL_GET (.mk_uN index.val))
        [globalGetInstruction (decide (width ty = 2)) dst index] (stack ++ [ty])
  | globalSet (stack) (ty : valtype) (index src : U32)
      (globalType : C.GLOBALS[index.val]? = some (.mk_globaltype (some .MUT) ty))
      (slot : src.val = slots C.LOCALS + slots stack) :
      ScalarEmission C (stack ++ [ty]) (.GLOBAL_SET (.mk_uN index.val))
        [globalSetInstruction (decide (width ty = 2)) src index] stack
  | load (stack) (op : SourceMachine.Memory.Load) (argument : memarg) (address offset : U32)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (sourceOffset : argument.OFFSET = .mk_uN offset.val)
      (slot : address.val = slots C.LOCALS + slots stack) :
      ScalarEmission C (stack ++ [.I32]) (op.source argument)
        [memoryLoadInstruction op address address offset] (stack ++ [valtype_numtype op.type])
  | store (stack) (op : SourceMachine.Memory.Store) (argument : memarg) (address value offset : U32)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (sourceOffset : argument.OFFSET = .mk_uN offset.val)
      (addressSlot : address.val = slots C.LOCALS + slots stack)
      (valueSlot : value.val = address.val + 1) :
      ScalarEmission C (stack ++ [.I32, valtype_numtype op.type]) (op.source argument)
        [memoryStoreInstruction op address value offset] stack
  | float (stack : List valtype) (op : SourceMachine.Float.Instruction) (left right : U32)
      (leftSlot : left.val = slots C.LOCALS + slots stack)
      (rightSlot : right.val = left.val + (op.arity - 1)) :
      ScalarEmission C (stack ++ List.replicate op.arity (valtype_numtype op.input))
        op.source [floatInstruction op left left right] (stack ++ [valtype_numtype op.output])

end Itasca.Compiler

end

section

open Itasca.Representation

/-!
## Typed-select emission

`TypedSelectEmission` relates an explicit source select type and physical operand
positions to the emitted width-specific select instruction.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std

/-- Explicit select emits the same width-specific instruction as implicit
select, while retaining its declared source result type. -/
inductive TypedSelectEmission (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | select (front : List valtype) (ty : valtype) (left right condition : U32)
      (leftPos : left.val = slots C.LOCALS + slots front)
      (rightPos : right.val = left.val + width ty)
      (conditionPos : condition.val = right.val + width ty) :
      TypedSelectEmission C (front ++ [ty,ty,.I32]) (.SELECT (some [ty]))
        [selectInstruction (decide (width ty = 2)) left right condition] (front ++ [ty])

end Itasca.Compiler

end

end CompilerLocalScalarEmission

/-! ## Compiler / Local / SimdEmission -/

section CompilerLocalSimdEmission

open Itasca.Representation

/-!
### SIMD emission vocabulary

Lane signatures, immediates, constants and emitted bytecode relate independently decoded
SIMD instructions to local compiler output. These relations identify source syntax,
stack effects and retained metadata; they do not assume execution correctness.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std
open Itasca.Body.Simd

/-- Source syntax and immediate fields retained by a SIMD metadata entry.
The opcode meanings are the independent binary-decoding tables. -/
inductive SimdImmediateMeaning (C : context) : U32 → runtime.bytecode.SimdImmediate →
    List valtype → instr → List valtype → Prop where
  /-- Pure SIMD carries its decoded SpecTec syntax and intrinsic typing signature.
  Existence of a typing context avoids imposing well-formedness of the caller's
  context here. Pure instructions do not inspect that context; implementation
  proofs establish that this signature is unique and usable in every valid one. -/
  | pure (opcode : U32) (immediate : runtime.bytecode.SimdImmediate)
      (source : instr) (input output : List valtype)
      (meaning : pureInstruction opcode.val = some source)
      (typed : ∃ D, Instr_ok D source (.mk_functype (.mk_list input) (.mk_list output))) :
      SimdImmediateMeaning C opcode immediate input source output
  | lane (opcode : U32) (immediate : runtime.bytecode.SimdImmediate) (op : LaneOperation)
      (meaning : laneMeaning opcode.val = some op) (lane : U8)
      (position : immediate.lane.val = lane.val) :
      SimdImmediateMeaning C opcode immediate op.inputs (op.instruction (.mk_uN lane.val)) op.outputs
  | memory (opcode : U32) (immediate : runtime.bytecode.SimdImmediate) (op : MemoryOperation)
      (meaning : memoryMeaning opcode.val = some op) (argument : memarg) (lane : U8)
      (memory : memtype) (available : C.MEMS[0]? = some memory)
      (offset : argument.OFFSET = .mk_uN immediate.offset.val)
      (position : op.laneCount ≠ 0 → immediate.lane.val = lane.val) :
      SimdImmediateMeaning C opcode immediate op.inputs (op.instruction argument (.mk_uN lane.val)) op.outputs
  | shuffle (immediate : runtime.bytecode.SimdImmediate) (low high : U64)
      (bits : immediate.bits.val = low.val + high.val * 2^64) :
      SimdImmediateMeaning C 13#u32 immediate [.V128,.V128] (shuffle low high) [.V128]

/-- Exact SIMD instruction, slot, and function-local metadata correspondence.
Execution correctness is established separately. Pure instruction signatures use
the generated typing judgment, rather than an implementation classification. -/
inductive SimdEmission (immediates : List runtime.bytecode.SimdImmediate) (constants : List U128)
    (C : context) : List valtype → instr → List Bytecode → List valtype → Prop where
  | instruction (front input output : List valtype) (source : instr)
      (opcode operand entry : U32) (immediate : runtime.bytecode.SimdImmediate) (instruction : Bytecode)
      (meaning : SimdImmediateMeaning C opcode immediate input source output)
      (metadata : immediates[entry.val]? = some immediate)
      (constructed : runtime.bytecode.Instr.make_simd opcode operand operand entry = .ok (some instruction))
      (position : operand.val = slots C.LOCALS + slots front) :
      SimdEmission immediates constants C (front ++ input) source [instruction] (front ++ output)
  | constant (front : List valtype) (bits : U128) (dst entry : U32)
      (metadata : constants[entry.val]? = some bits)
      (position : dst.val = slots C.LOCALS + slots front) :
      SimdEmission immediates constants C front (.VCONST .V128 (.mk_uN bits.val))
        [.ConstV128 dst entry] (front ++ [.V128])

end Itasca.Compiler

end CompilerLocalSimdEmission

/-! ## Compiler / Local / StatefulEmission -/

section CompilerLocalStatefulEmission

/-!
### Stateful instruction emission

Operand tuples and emission relations describe bulk memory/table operations
using the same source stack and retained indirect table. The certificate records
syntactic correspondence; interpreter proofs establish execution behavior.
-/

section

/-!
## Stateful opcode and argument meaning

Opcode classification, argument lists and instruction pairs describe the source operands
interpreted by stateful lowering.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- Expanded opcodes use 0x100 plus the misc-prefix subopcode. -/
def statefulOpcode : SourceMachine.Stateful.Instruction → U16
  | .refNull _ => 208#u16
  | .refFunc _ => 210#u16
  | .refIsNull => 209#u16
  | .tableGet _ => 37#u16
  | .tableSet _ => 38#u16
  | .tableSize _ => 272#u16
  | .tableGrow _ => 271#u16
  | .tableFill _ => 273#u16
  | .tableCopy .. => 270#u16
  | .tableInit .. => 268#u16
  | .elemDrop _ => 269#u16
  | .memorySize => 63#u16
  | .memoryGrow => 64#u16
  | .memoryFill => 267#u16
  | .memoryCopy => 266#u16
  | .memoryInit _ => 264#u16
  | .dataDrop _ => 265#u16

/-- Callback arguments, including the reversed table.init pair order. -/
def statefulArguments : SourceMachine.Stateful.Instruction → Nat × Nat
  | .refNull .FUNCREF => (0, 0)
  | .refNull .EXTERNREF => (1, 0)
  | .refFunc index | .tableGet index | .tableSet index | .tableSize index
    | .tableGrow index | .tableFill index | .elemDrop index | .memoryInit index
    | .dataDrop index => (index, 0)
  | .tableCopy destination source => (destination, source)
  | .tableInit table element => (element, table)
  | _ => (0, 0)

def StatefulArguments (op : SourceMachine.Stateful.Instruction) (a b : U32) : Prop :=
  a.val = (statefulArguments op).1 ∧ b.val = (statefulArguments op).2

/-- Exact bytecode constructor. `first` starts the complete operand suffix;
`second` is the next scalar slot. `entry` indexes the retained pair table. -/
def statefulInstruction (op : SourceMachine.Stateful.Instruction) (first second a entry : U32) :
    runtime.bytecode.Instr :=
  match op with
  | .refNull _ => .RefNull first
  | .refFunc _ => .RefFunc first a
  | .refIsNull => .RefIsNull first first
  | .tableGet _ => .TableGet first first a
  | .tableSet _ => .TableSet first second a
  | .tableSize _ => .TableSize first a
  | .tableGrow _ => .TableGrow first a
  | .tableFill _ => .TableFill first a
  | .tableCopy .. => .TableCopy first entry
  | .tableInit .. => .TableInit first entry
  | .elemDrop _ => .ElemDrop a
  | .memorySize => .MemorySize first
  | .memoryGrow => .MemoryGrow first
  | .memoryFill => .MemoryFill first
  | .memoryCopy => .MemoryCopy first
  | .memoryInit _ => .MemoryInit first a
  | .dataDrop _ => .DataDrop a

/-- Pair-table entries are function-local immutable compiler metadata. -/
def StatefulPair (pairs : List (U32 × U32)) (op : SourceMachine.Stateful.Instruction)
    (a b entry : U32) : Prop :=
  match op with
  | .tableCopy .. | .tableInit .. => pairs[entry.val]? = some (a, b)
  | _ => True

end Itasca.Compiler

end

section

open Itasca.Representation

/-!
## Stateful emission cases

`StatefulEmission` relates source stateful operations to emitted instructions and their
stack-type transition.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- Reference and bulk instructions retain their exact function-local pair table.
This is syntactic compiler evidence, independent of execution correctness. -/
inductive StatefulEmission (pairs : List (U32 × U32)) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | instruction (stack input output) (op : SourceMachine.Stateful.Instruction)
      (signature : SourceMachine.Stateful.Signature C op input output)
      (first second a b entry : U32)
      (firstSlot : first.val = slots C.LOCALS + slots stack)
      (secondSlot : op.arity ≥ 2 → second.val = first.val + 1)
      (arguments : StatefulArguments op a b)
      (pair : StatefulPair pairs op a b entry) :
      StatefulEmission pairs C (stack ++ input) op.source
        [statefulInstruction op first second a entry] (stack ++ output)

end Itasca.Compiler

end

end CompilerLocalStatefulEmission
