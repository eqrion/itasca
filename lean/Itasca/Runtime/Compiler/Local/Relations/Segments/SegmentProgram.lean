import Itasca.Runtime.Compiler.Local.Initializer.InitializerMappings

/-! Syntactic programs emitted for active and declarative segments. The
certificate records source segment indices and actual embedded descriptor
lookups; runtime bounds and source typing remain separate obligations. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

inductive ElementProgram (function : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.module.Element) : List runtime.bytecode.Instr → Prop where
  | passive (mode : segment.mode = .Passive) : ElementProgram function index segment []
  | declarative (mode : segment.mode = .Declarative) (word : U32) (encoded : word.val = index) :
      ElementProgram function index segment [.ElemDrop word]
  | active (table : U32) (offset : Itasca.types.ConstExpr)
      (mode : segment.mode = .Active table offset)
      (word length entry : U32) (encoded : word.val = index) (count : length.val = segment.init.length)
      (descriptor : function.indirect.val[entry.val]? = some (word, table))
      (instruction : runtime.bytecode.Instr)
      (constant : ConstantInstruction function 0#u32 offset .I32 instruction) :
      ElementProgram function index segment
        [instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
          .TableInit 0#u32 entry, .ElemDrop word]

inductive DataProgram (function : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.module.Data) : List runtime.bytecode.Instr → Prop where
  | passive (mode : segment.mode = .Passive) : DataProgram function index segment []
  | active (memory : U32) (offset : Itasca.types.ConstExpr)
      (mode : segment.mode = .Active memory offset)
      (word length : U32) (encoded : word.val = index) (count : length.val = segment.init.length)
      (instruction : runtime.bytecode.Instr)
      (constant : ConstantInstruction function 0#u32 offset .I32 instruction) :
      DataProgram function index segment
        [instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
          .MemoryInit 0#u32 word, .DataDrop word]

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

end Itasca.Runtime.Compiler
