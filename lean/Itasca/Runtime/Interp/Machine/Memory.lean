import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.Memory.MemoryCoreEmission
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Memory.MemoryCoreOperandBounds
import Itasca.Runtime.Interp.Memory.MemoryCoreTransition
import Itasca.Runtime.Interp.Memory.MemoryCoreStep
import Itasca.Runtime.Interp.Memory.MemoryCoreResult
import Itasca.Runtime.Interp.Memory.MemoryLoadStepFootprint
import Itasca.Runtime.Interp.Machine.Control.ForwardJump
import Itasca.Runtime.Spec.Extend
import Itasca.Runtime.SourceMachine.Core.MemoryPositive
import Itasca.Runtime.Interp.Machine.Control.UniformSource
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution

/-!
Scalar memory machine instruction preparation, execution and ownership. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Memory Point -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Memory
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem corePoint_load_head {C returns code labels stack pc next output}
    (op : Abs.Memory.Load) (argument : memarg) (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (op.source argument :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (op.source argument :: after) target.val next output) ∨
    (∃ front address offset, stack = front ++ [.I32] ∧
      address.val = Code.slots C.LOCALS + Code.slots front ∧ argument.OFFSET = .mk_uN offset.val ∧
      code[pc]? = some (Code.memoryLoadInstruction op address address offset) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [valtype_numtype op.type]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source argument :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,address,offset,input,emitted,result,offsetEq,position⟩ := scalarEmission_load_inv op argument (FloatHeads.project (.core (.load op argument)) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,address,offset,rfl,position,offsetEq,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp [Abs.Memory.Load.source] at sourceEq

 theorem corePoint_store_head {C returns code labels stack pc next output}
    (op : Abs.Memory.Store) (argument : memarg) (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (op.source argument :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (op.source argument :: after) target.val next output) ∨
    (∃ front address value offset, stack = front ++ [.I32,valtype_numtype op.type] ∧
      address.val = Code.slots C.LOCALS + Code.slots front ∧ value.val = address.val+1 ∧ argument.OFFSET = .mk_uN offset.val ∧
      code[pc]? = some (Code.memoryStoreInstruction op address value offset) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        front after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source argument :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,address,value,offset,input,emitted,result,offsetEq,position,valuePosition⟩ := scalarEmission_store_inv op argument (FloatHeads.project (.core (.store op argument)) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,address,value,offset,rfl,position,valuePosition,offsetEq,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp [Abs.Memory.Store.source] at sourceEq
end Itasca.Runtime.Interp.StructuredMachine.Memory

end

/-! ## Memory Continue -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Memory
open Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem corePoint_load_continue {sourceStore raw f compiled C targets next output}
    (point : FramePoint sourceStore raw f compiled C targets next output)
    (front : List val) (bits : Nat) (value : val) (ty : numtype) (after : List instr)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits])
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (valueType : Code.valueType value = valtype_numtype ty)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType ++ [valtype_numtype ty]) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint sourceStore {raw with pc := pc} {f with code := after,vals := front ++ [value]}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,List.map_cons,List.map_nil,valueType,pcNext] using tail

theorem corePoint_store_continue {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front operands : List val) (after : List instr)
    (values : f.vals = front ++ operands)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint afterStore {raw with pc := pc} {f with code := after,vals := front}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  · simpa only [pcNext] using tail
end Itasca.Runtime.Interp.StructuredMachine.Memory

end

/-! ## Memory Prepare -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Memory
open Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem coreFramePoint_load_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (op : Abs.Memory.Load) (argument : memarg)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} [])
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (∃ front bits memoryAddress object address offset,
      f.vals = front ++ [Abs.integerVal .I32 bits] ∧ bits < 2^32 ∧
      inst.memories.val[0]? = some memoryAddress ∧ store.memories.val[memoryAddress.index.val]? = some object ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType) ∧
      proj_uN_0 argument.OFFSET = offset.val ∧
      compiled.code.val[raw.pc.val]? = some (Code.memoryLoadInstruction op address address offset) ∧
      Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Code.valueType ++ [valtype_numtype op.type]) after (raw.pc.val+1) next output) := by
  rcases corePoint_load_head op argument after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,address,offset,input,position,offsetEq,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,bits,memoryAddress,object,values,bound,mapped,issued,wf,heights⟩ :=
      load_typed_operands_full view code store inst f after op argument moduleEq typed
    have typesEq : front.map Code.valueType = types := by
      have eq := input
      simp only [values,List.map_append,List.map_cons,List.map_nil,Code.valueType,Abs.integerVal,numtype_Inn] at eq
      exact List.append_cancel_right eq
    refine Or.inr ⟨front,bits,memoryAddress,object,address,offset,values,bound,mapped,issued,heights,?_,?_,fetch,?_⟩
    · simpa only [← point.locals,typesEq] using position
    · simp only [offsetEq,proj_uN_0]
    · simpa only [typesEq] using tail

theorem coreFramePoint_store_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (op : Abs.Memory.Store) (argument : memarg)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} [])
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (∃ front bits number memoryAddress object address value offset,
      f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number] ∧ bits < 2^32 ∧ wf_num_ op.type number ∧
      inst.memories.val[0]? = some memoryAddress ∧ store.memories.val[memoryAddress.index.val]? = some object ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType) ∧
      value.val = address.val+1 ∧ proj_uN_0 argument.OFFSET = offset.val ∧
      compiled.code.val[raw.pc.val]? = some (Code.memoryStoreInstruction op address value offset) ∧
      Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Code.valueType) after (raw.pc.val+1) next output) := by
  rcases corePoint_store_head op argument after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,address,value,offset,input,position,valuePosition,offsetEq,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,bits,number,memoryAddress,object,values,bound,numberWf,mapped,issued,wf,heights⟩ :=
      store_typed_operands_full view code store inst f after op argument moduleEq typed
    have typesEq : front.map Code.valueType = types := by
      have eq := input
      simp only [values,List.map_append,List.map_cons,List.map_nil,Code.valueType,Abs.integerVal,numtype_Inn] at eq
      exact List.append_cancel_right eq
    refine Or.inr ⟨front,bits,number,memoryAddress,object,address,value,offset,values,bound,numberWf,mapped,issued,heights,?_,valuePosition,?_,fetch,?_⟩
    · simpa only [← point.locals,typesEq] using position
    · simp only [offsetEq,proj_uN_0]
    · simpa only [typesEq] using tail
end Itasca.Runtime.Interp.StructuredMachine.Memory

end

/-! ## Memory Certified Step -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Memory
open Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem coreFramePoint_load_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Load) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((∃ nextFrame pc, out.1 = .Ok () ∧
        Abs.Core.step initial = .next {initial with frames := nextFrame :: rest} ∧ pc.val = raw.pc.val+1 ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        Abs.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Store.decodeStore view code store) {raw with pc := pc} nextFrame compiled C targets next output ∧
        (∃ values, nextFrame = {f with code := after,vals := values}) ∧
        ∃ position word, raw.base.val ≤ position ∧ position < exec.slots.length ∧
          out.2.1.slots.val = exec.slots.val.set position word) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}}) ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄) := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_load_prepare view code store inst raw f compiled C targets next output after op argument moduleEq frameTyped point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨front,bits,memoryAddress,object,address,offset,values,bound,mapped,issued,heights,position,offsetEq,fetch,tail⟩ := operation
    obtain ⟨out,result,footprint⟩ := WP.spec_imp_exists (step_load_footprint memory hooks floats allocator platform index view laws code exec store raw op address offset inst memoryAddress object ambient f rest after front bits argument found mapped issued moduleEq values slots position bound offsetEq compiled last frameFound codeFound fetch pcBound)
    have normal := (step_load_core_simulation memory hooks floats allocator platform index view laws code exec store raw op address offset inst memoryAddress object ambient f rest after front bits argument found mapped issued moduleEq values slots position bound offsetEq compiled last frameFound codeFound fetch pcBound typed)
    rw [result] at normal ⊢
    apply WP.spec.ret
    have effect := normal
    rw [WP.spec_ok] at effect
    refine ⟨effect.1,effect.2.1,?_⟩
    rcases effect.2.2 with ⟨nextFrame,success,actual,fresh,source,represented,pc,pcNext,unchanged⟩ | trapped
    · obtain ⟨value,frameEq,valueType⟩ := core_load_next_shape view code store inst memoryAddress object _ f nextFrame rest after front bits op argument offset rfl moduleEq mapped issued values bound offsetEq actual
      refine Or.inl ⟨nextFrame,pc,success,(core_step_load_eq _ _ _ _ _ _ _).trans actual,pcNext,unchanged,fresh,source,represented,?_,⟨_,frameEq⟩,?_⟩
      · rw [frameEq]
        exact corePoint_load_continue point front bits value op.type after values heights valueType tail pc pcNext
      · obtain ⟨word,capacity,exactWords⟩ := footprint success
        exact ⟨raw.base.val+address.val,word,Nat.le_add_right _ _,capacity,exactWords⟩
    · exact Or.inr trapped

theorem coreFramePoint_store_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Store) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
      ∃ memoryAddress object, inst.memories.val[0]? = some memoryAddress ∧
        store.memories.val[memoryAddress.index.val]? = some object ∧
        MemoryMutation view store out.2.2.1 memoryAddress object ∧
      ((∃ nextFrame, out.1 = .Ok () ∧
        Abs.Core.step initial = .next {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Store.decodeStore view code out.2.2.1) {raw with pc := pc} nextFrame compiled C targets next output ∧
        (∃ values, nextFrame = {f with code := after,vals := values})) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩))) ⦄) := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_store_prepare view code store inst raw f compiled C targets next output after op argument moduleEq frameTyped point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨front,bits,number,memoryAddress,object,address,value,offset,values,bound,numberWf,mapped,issued,heights,position,valuePosition,offsetEq,fetch,tail⟩ := operation
    apply WP.spec_mono (step_store_core_simulation memory hooks floats allocator platform index view laws code exec store raw op address value offset inst memoryAddress object ambient f rest after front bits number argument found mapped issued moduleEq values slots position valuePosition bound numberWf offsetEq compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨pc,pcNext,unchanged⟩ := effect.2.1
    refine ⟨effect.1,pc,pcNext,unchanged,memoryAddress,object,mapped,issued,effect.2.2.1,?_⟩
    rcases effect.2.2.2 with ⟨success,actual,fresh,extension,source,represented⟩ | trapped
    · refine Or.inl ⟨_,success,(core_step_store_eq _ _ _ _ _ _ _).trans actual,fresh,extension,source,?_,?_,⟨_,rfl⟩⟩
      · simpa only [unchanged,FrameSlots] using represented
      · exact corePoint_store_continue point extension front _ after values heights tail pc pcNext
    · exact Or.inr trapped

end Itasca.Runtime.Interp.StructuredMachine.Memory

end

/-! ## Memory Run -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Memory
open Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
theorem step_memory_load_core {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Load) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint (Store.decodeStore view code store) {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped {initial with frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with frames := g::rest} ∨ Abs.Core.step initial = .next {initial with frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word)) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ ∃ n, 0 < n ∧
        StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  rcases coreFramePoint_load_step memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point typed with jump | operation
  · obtain ⟨target,forward,fetched,tail⟩ := jump
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      (Store.decodeStore view code store) ambient {f with code := op.source argument::after} rest C targets next output target
      last frameFound found codeFound pcBound forward fetched slots tail typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨sameStore,samePlatform,Or.inl ⟨success,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · apply WP.spec_mono operation
    intro out effect
    refine ⟨effect.1,effect.2.1,?_⟩
    rcases effect.2.2 with ⟨g,pc,success,actual,pcNext,unchanged,fresh,source,represented,retained,shape,footprint⟩ | ⟨failed,unchanged,trace⟩
    · have metadata : FrameMetadata f g := by obtain ⟨values,rfl⟩ := shape; exact ⟨rfl,rfl,rfl,rfl⟩
      refine Or.inl ⟨success,pc,g,unchanged,represented,retained,fresh,metadata,Or.inr actual,?_,Or.inr footprint⟩
      exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (stepH_wf source).2)⟩
    · exact Or.inr ⟨failed,trace⟩

theorem step_memory_store_core {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Store) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      ∃ pc : U32, out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
      ((out.1 = .Ok () ∧ ∃ g : Abs.AFrame,
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint (Store.decodeStore view code out.2.2.1) {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∨
          Abs.Core.step initial = .next {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  rcases coreFramePoint_store_step memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point typed with jump | operation
  · obtain ⟨target,forward,fetched,tail⟩ := jump
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      (Store.decodeStore view code store) ambient {f with code := op.source argument::after} rest C targets next output target
      last frameFound found codeFound pcBound forward fetched slots tail typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    rw [sameStore]
    exact ⟨samePlatform,.refl store,extend_store_refl _ typed.typed.store,Or.inl rfl,target,exactState,
      Or.inl ⟨success,_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation⟩⟩
  · apply WP.spec_mono operation
    intro out effect
    obtain ⟨samePlatform,pc,pcNext,exactState,memoryAddress,object,mapped,issued,mutation,operation⟩ := effect
    rcases operation with ⟨g,success,actual,fresh,extension,source,represented,retained,shape⟩ | ⟨failed,unchanged,trace⟩
    · have metadata : FrameMetadata f g := by obtain ⟨values,rfl⟩ := shape; exact ⟨rfl,rfl,rfl,rfl⟩
      refine ⟨samePlatform,mutation.frame_metadata,extension,Or.inr ⟨_,_,issued,mutation⟩,pc,exactState,
        Or.inl ⟨success,g,represented,retained,fresh,metadata,Or.inr actual,?_⟩⟩
      exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (stepH_wf source).2)⟩
    · have extension : Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) := by
        rw [unchanged]
        exact extend_store_refl _ typed.typed.store
      exact ⟨samePlatform,mutation.frame_metadata,extension,Or.inr ⟨_,_,issued,mutation⟩,pc,exactState,Or.inr ⟨failed,unchanged,trace⟩⟩

end Itasca.Runtime.Interp.StructuredMachine.Memory

end

/-! ## Memory Execution Owned -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Memory
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
theorem step_memory_load_execution_owned_uniform {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Load) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code out.2.2.1 out.2.1
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∧
        UniformConcreteSim raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} [] ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) []
          ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_load_head op argument after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,address,offset,input,position,offsetEq,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_memory_load_core memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point machine.typed)
  intro out effect
  obtain ⟨sameStore,samePlatform,operation⟩ := effect
  rw [sameStore]
  refine ⟨samePlatform,Or.inl rfl,.refl store,extend_store_refl _ machine.typed.typed.store,?_⟩
  rcases operation with ⟨success,pc,g,fields,represented,retained,fresh,metadata,transition,simulation,footprint⟩ | ⟨failed,trace⟩
  · have uniform : UniformConcreteSim raw.pc.val pc.val false false
        ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
        ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases transition with same | step
      · rw [← same] at simulation ⊢
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (Abs.Core.load_step_positive _ _ _ _ _ _ _ _ machine.typed step)
    have covered : Abs.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases transition with same | step
      · rw [← same]; exact machine.core
      · exact StructuredMachine.core_step_supported machine.typed machine.core step
    have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
      rcases footprint with same | ⟨position,word,above,bound,changed⟩
      · rw [same]; exact .refl _ _
      · rw [changed]; exact .set _ _ _ _ above
    exact Or.inl ⟨success,pc,g,Execution.ordinary view code ambient {f with code := op.source argument::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound
      program (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,uniform,StructuredMachine.owned_transition machine.typed machine.core transition,StructuredMachine.bound_transition machine.typed machine.core transition⟩
  · exact Or.inr ⟨failed,rfl,trace⟩

theorem step_memory_load_execution_owned {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Load) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code out.2.2.1 out.2.1
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) []
          ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_memory_load_execution_owned_uniform memory hooks floats allocator platform index view laws code exec store raw inst compiled ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound point expected machine program)
  rintro out ⟨platform,mutation,metadata,extension,success | trapped⟩
  · rcases success with ⟨success,pc,g,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨platform,mutation,metadata,extension,Or.inl ⟨success,pc,g,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨platform,mutation,metadata,extension,Or.inr trapped⟩

theorem step_memory_store_execution_owned_uniform {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Store) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code out.2.2.1 out.2.1
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∧
        UniformConcreteSim raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} [] ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) []
          ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_store_head op argument after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,address,value,offset,input,position,valuePosition,offsetEq,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_memory_store_core memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point machine.typed)
  intro out effect
  obtain ⟨samePlatform,stores,extension,mutation,pc,fields,operation⟩ := effect
  refine ⟨samePlatform,mutation,stores,extension,?_⟩
  rcases operation with ⟨success,g,represented,retained,fresh,metadata,transition,simulation⟩ | ⟨failed,sameStore,trace⟩
  · have uniform : UniformConcreteSim raw.pc.val pc.val false false
        ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
        ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ [] := by
      rcases transition with same | step
      · rw [← same] at simulation ⊢
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (Abs.Core.store_step_positive _ _ _ _ _ _ _ _ machine.typed step)
    have covered : Abs.SupportedState ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ := by
      rcases transition with same | step
      · rw [← same]; exact machine.core
      · exact StructuredMachine.core_step_supported machine.typed machine.core step
    have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
      rw [fields]; exact .refl _ _
    have untouched : {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} := by rw [fields]
    exact Or.inl ⟨success,pc,g,Execution.ordinary view code ambient {f with code := op.source argument::after} g rest expected raw.pc.val false machine
      stores extension raw index pc last frameFound program (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ untouched preserved fresh covered,simulation,uniform,StructuredMachine.owned_transition machine.typed machine.core transition,StructuredMachine.bound_transition machine.typed machine.core transition⟩
  · exact Or.inr ⟨failed,sameStore,trace⟩

theorem step_memory_store_execution_owned {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Store) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code out.2.2.1 out.2.1
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) []
          ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_memory_store_execution_owned_uniform memory hooks floats allocator platform index view laws code exec store raw inst compiled ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound point expected machine program)
  rintro out ⟨platform,mutation,metadata,extension,success | trapped⟩
  · rcases success with ⟨success,pc,g,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨platform,mutation,metadata,extension,Or.inl ⟨success,pc,g,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨platform,mutation,metadata,extension,Or.inr trapped⟩

end Itasca.Runtime.Interp.StructuredMachine.Memory

end
