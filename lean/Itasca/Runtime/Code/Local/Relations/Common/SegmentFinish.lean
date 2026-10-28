import Itasca.Runtime.Code.Local.Relations.Control.SegmentLoops

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

theorem segment_program_finish (module : runtime.compiler.ExecutableModule)
    (seed first second : runtime.bytecode.CompiledFunction)
    (instructions : alloc.vec.Vec runtime.bytecode.Instr)
    (elements datas : List (List runtime.bytecode.Instr))
    (elementPrefix : ElementProgramPrefix module seed first module.module.env.elements.length elements)
    (dataPrefix : DataProgramPrefix module first second module.module.tail.data.length datas)
    (appended : instructions.val = second.code.val ++ [.Return 0#u32 0#u32])
    (emptyCode : seed.code.val = []) (emptyLocals : seed.locals.val = [])
    (localSlots : seed.local_slots = 0#u32) (paramSlots : seed.param_slots = 0#u32)
    (capacity : seed.slot_count = 0#u32) :
    SegmentProgram module {second with code := instructions} := by
  have secondPool : second.v128_pool = first.v128_pool := by
    have same := congrArg runtime.bytecode.CompiledFunction.v128_pool dataPrefix.fields
    exact same
  have secondIndirect : second.indirect = first.indirect := by
    have same := congrArg runtime.bytecode.CompiledFunction.indirect dataPrefix.fields
    exact same
  have secondCapacity : second.slot_count = 0#u32 ∨ second.slot_count = 3#u32 := by
    rcases dataPrefix.capacity with same | three
    · rcases elementPrefix.capacity with original | three
      · exact .inl (same.trans (original.trans capacity))
      · exact .inr (same.trans three)
    · exact .inr three
  refine ⟨elements, datas, ?_⟩
  constructor
  · exact elementPrefix.length
  · exact dataPrefix.length
  · intro index segment found
    obtain ⟨actual, body, actualFound, bodyFound, program⟩ := elementPrefix.entries index
      (List.getElem?_eq_some_iff.mp found).1
    have same : actual = segment := Option.some.inj (actualFound.symm.trans found)
    subst actual
    exact ⟨body, bodyFound, program.extend secondPool (by simp only [secondIndirect, List.take_length])⟩
  · intro index segment found
    obtain ⟨actual, body, actualFound, bodyFound, program⟩ := dataPrefix.entries index
      (List.getElem?_eq_some_iff.mp found).1
    have same : actual = segment := Option.some.inj (actualFound.symm.trans found)
    subst actual
    exact ⟨body, bodyFound, program.extend rfl⟩
  · simp [appended, dataPrefix.code, elementPrefix.code, emptyCode, List.append_assoc]
  · exact secondCapacity
  · rintro (⟨index, body, found, five⟩ | ⟨index, body, found, five⟩)
    · have firstThree := elementPrefix.active body (List.mem_of_getElem? found) five
      rcases dataPrefix.capacity with same | three
      · exact same.trans firstThree
      · exact three
    · exact dataPrefix.active body (List.mem_of_getElem? found) five
  · have secondFields := congrArg runtime.bytecode.CompiledFunction.local_slots dataPrefix.fields
    have firstFields := congrArg runtime.bytecode.CompiledFunction.local_slots elementPrefix.fields
    exact secondFields.trans (firstFields.trans localSlots)
  · have secondFields := congrArg runtime.bytecode.CompiledFunction.param_slots dataPrefix.fields
    have firstFields := congrArg runtime.bytecode.CompiledFunction.param_slots elementPrefix.fields
    exact secondFields.trans (firstFields.trans paramSlots)
  · have secondFields := congrArg (fun f => f.locals.val) dataPrefix.fields
    have firstFields := congrArg (fun f => f.locals.val) elementPrefix.fields
    exact secondFields.trans (firstFields.trans emptyLocals)

theorem SegmentProgram.change_module {before after : runtime.compiler.ExecutableModule}
    {function} (program : SegmentProgram before function) (source : after.module = before.module) :
    SegmentProgram after function := by
  obtain ⟨elements, datas, certificate⟩ := program
  refine ⟨elements, datas, ?_⟩
  cases certificate
  constructor <;> (try simp only [source]) <;> assumption

end Itasca.Runtime.Code
