import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.SafetyAndEncoding
import Itasca.Runtime.Interp.State.GlobalOperations
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.SourceMachine.Float.Descriptors
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.SourceMachine.Core.ProgressAndBounds
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Machine.Normalization.IndexedEmpty
import Itasca.Runtime.Interp.Relations.NormalizationAndValueTypes
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Interp.Numeric.Integer.ConversionsAndBinaryContracts
import Itasca.Runtime.Interp.Numeric.Integer.SignedOperationsAndCounts
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.SourceMachine.Numeric.Positive
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Interp.Machine.Coverage.RecordingHeads
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Relations.EntryEffects
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.State.ObjectBindingsAndMutation
import Itasca.Runtime.Interp.Machine.StateAndOwnership
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Interp.Memory.MemoryEffects
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Interp.Memory.EncodingAndDispatch

open WebAssembly

/-!
Proofs for Runtime / Interp / Machine.

This module collects ScalarExecution, GlobalMutation, LocalOwnership, MemoryAndNormalization.
Each section documents its contracts and consumers.
-/

/-! ## ScalarExecution -/

section

open Itasca.Representation

/-!
# Scalar Execution

Scalar execution, including globals and select, agrees with source instruction behavior.
-/

/-! ## Global -/

section

/-!
Global reads and writes from structured fetch inversion through preparation and certified step. Whole-execution ownership remains separate: mutation proofs need the certified step without its 150 additional execution dependencies.
-/

/-! ## Global Point -/

section

namespace Itasca.Interp.Machine.Global
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std

theorem core_point_global_get_head {C returns code labels stack pc next output}
    (index : Nat) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.GLOBAL_GET (.mk_uN index) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.GLOBAL_GET (.mk_uN index) :: after) target.val next output) ∨
    (∃ mutability ty idx dst, index = idx.val ∧
      C.GLOBALS[index]? = some (.mk_globaltype mutability ty) ∧
      dst.val = Representation.slots C.LOCALS + Representation.slots stack ∧
      code[pc]? = some (Compiler.globalGetInstruction (decide (Representation.width ty = 2)) dst idx) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.GLOBAL_GET (.mk_uN index) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨mutability,ty,idx,dst,indexEq,lookup,emitted,result,position⟩ := scalar_emission_global_get_inv index (FloatHeads.project (.core (.global_get (.mk_uN index))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨mutability,ty,idx,dst,rfl,lookup,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq

theorem core_point_global_set_head {C returns code labels stack pc next output}
    (index : Nat) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.GLOBAL_SET (.mk_uN index) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.GLOBAL_SET (.mk_uN index) :: after) target.val next output) ∨
    (∃ front ty idx src, index = idx.val ∧ stack = front ++ [ty] ∧
      C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) ∧
      src.val = Representation.slots C.LOCALS + Representation.slots front ∧
      code[pc]? = some (Compiler.globalSetInstruction (decide (Representation.width ty = 2)) src idx) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        front after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.GLOBAL_SET (.mk_uN index) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,idx,src,indexEq,input,lookup,emitted,result,position⟩ := scalar_emission_global_set_inv index (FloatHeads.project (.core (.global_set (.mk_uN index))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,idx,src,rfl,rfl,lookup,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq
end Itasca.Interp.Machine.Global

end

/-! ## Global Prepare -/

section

namespace Itasca.Interp.Machine.Global
open Aeneas Aeneas.Std WebAssembly

theorem core_frame_point_global_get_prepare {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (index : Nat)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Representation.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) ∨
    (∃ idx dst address object, index = idx.val ∧
      inst.globals.val[index]? = some address ∧ store.globals.val[address.index.val]? = some object ∧
      dst.val = Representation.slots ((f.locals ++ f.vals).map Representation.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Compiler.globalGetInstruction (decide (Representation.width (Itasca.Translation.valueType object.ty.valtype) = 2)) dst idx) ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (f.vals.map Representation.valueType ++ [Itasca.Translation.valueType object.ty.valtype]) after (raw.pc.val+1) next output) := by
  rcases core_point_global_get_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨mutability,ty,idx,dst,indexEq,lookup,position,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨address,object,mapped,issued,mutEq,typeEq⟩ := core_global_lookup view code store inst f C index mutability ty moduleEq point.bindings lookup
    refine Or.inr ⟨idx,dst,address,object,indexEq,mapped,issued,?_,?_,?_⟩
    · simpa only [point.locals,List.map_append,Representation.slots_append] using position
    · simpa only [typeEq] using fetch
    · simpa only [typeEq] using tail

theorem core_frame_point_global_set_prepare {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (index : Nat)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (typed : SourceMachine.FrameTyped (Representation.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [])
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Representation.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) ∨
    (∃ front value idx src address object, index = idx.val ∧ f.vals = front ++ [value] ∧ wf_val value ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      inst.globals.val[index]? = some address ∧ store.globals.val[address.index.val]? = some object ∧
      object.ty.mutability = .Var ∧ Itasca.Translation.valueType object.ty.valtype = Representation.valueType value ∧
      src.val = Representation.slots ((f.locals ++ front).map Representation.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Compiler.globalSetInstruction (decide (Representation.width (Itasca.Translation.valueType object.ty.valtype) = 2)) src idx) ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Representation.valueType) after (raw.pc.val+1) next output) := by
  rcases core_point_global_set_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,ty,idx,src,indexEq,input,lookup,position,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨address,object,mapped,issued,mutEq,typeEq⟩ := core_global_lookup view code store inst f C index (some .MUT) ty moduleEq point.bindings lookup
    obtain ⟨front,value,values,valueWf,heights⟩ := global_set_typed_operand f after index typed
    have shape := input
    simp only [values,List.map_append,List.map_cons,List.map_nil] at shape
    have lengthEq : (front.map Representation.valueType).length = types.length := by
      have lengths := congrArg List.length shape
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨typesEq,valueEq⟩ := List.append_inj shape lengthEq
    have valueType : Representation.valueType value = ty := by simpa using valueEq
    have mutable : object.ty.mutability = .Var := by
      cases eq : object.ty.mutability <;> simp_all [Itasca.Translation.mutability]
    refine Or.inr ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,typeEq.trans valueType.symm,?_,?_,?_⟩
    · simpa only [point.locals,List.map_append,Representation.slots_append,typesEq] using position
    · simpa only [typeEq] using fetch
    · simpa only [typesEq] using tail
end Itasca.Interp.Machine.Global

end

/-! ## Global Continue -/

section

namespace Itasca.Interp.Machine.Global
open Aeneas Aeneas.Std WebAssembly

theorem decode_words_value_type (ty : Itasca.wasm_types.ValueType) (lo hi : U64) :
    Representation.valueType (Representation.decodeWords ty lo hi) = Itasca.Translation.valueType ty := by
  cases ty <;> simp only [Representation.decodeWords,Representation.decodeRef,Itasca.Translation.referenceType,Itasca.Translation.valueType]
  all_goals first | rfl | (split <;> rfl)

theorem core_point_global_get_continue {sourceStore raw f compiled C targets next output}
    (point : FramePoint sourceStore raw f compiled C targets next output)
    (value : val) (ty : valtype) (after : List instr)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length)
    (valueType : Representation.valueType value = ty)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (f.vals.map Representation.valueType ++ [ty]) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint sourceStore {raw with pc := pc} {f with code := after,vals := f.vals ++ [value]}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals,?_,?_⟩
  · have labels : LabelsMatch (f.vals ++ []) f.labels targets := by simpa only [List.append_nil] using point.labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,List.map_cons,List.map_nil,valueType,pcNext] using tail

theorem core_point_global_set_continue {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front : List val) (value : val) (after : List instr)
    (values : f.vals = front ++ [value])
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Representation.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint afterStore {raw with pc := pc} {f with code := after,vals := front}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  · simpa only [pcNext] using tail
end Itasca.Interp.Machine.Global

end

/-! ## Global Certified Step Owned -/

section

namespace Itasca.Interp.Machine.Global
open Aeneas Aeneas.Std WebAssembly Itasca.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem core_frame_point_global_get_step_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (binding : FrameBinding store exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (pcBound : raw.pc.val < U32.max)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Representation.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ nextFrame pc, pc.val = raw.pc.val+1 ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧
        SourceMachine.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Representation.decodeStore view code store) {raw with pc := pc} nextFrame compiled C targets next output ∧ (∃ values, nextFrame = {f with code := after,vals := values}) ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        SourceMachine.Core.step initial = .next {initial with frames := nextFrame :: rest} ⦄) := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (Representation.decodeStore view code store) {f with code := .GLOBAL_GET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases core_frame_point_global_get_prepare view code store inst raw f compiled C targets next output after index moduleEq point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨idx,dst,address,object,indexEq,mapped,issued,position,fetch,tail⟩ := operation
    subst index
    have valid := Compiler.well_formed_fetched compiled checked raw.pc.val _ fetch
    have bound := Compiler.global_get_valid_bounds compiled (Itasca.Translation.valueType object.ty.valtype) dst idx valid
    have allocated := binding.capacity inst compiled found codeFound
    have capacity : raw.base.val + dst.val + Representation.width (Itasca.Translation.valueType object.ty.valtype) ≤ exec.slots.length := by omega
    apply WP.spec_mono (step_global_get_simulation memory hooks floats allocator view code exec store raw dst idx inst address object ambient f rest after platform frameIndex found mapped issued moduleEq slots position capacity
      (small object (List.mem_of_getElem? issued)) compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨success,platformSame,storeSame,nextFrame,actual,fresh,source,represented,pc,pcNext,unchanged,prefixEffect⟩ := effect
    have coreStep : SourceMachine.Core.step ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN idx.val) :: after} :: rest,[]⟩ =
        .next ⟨Representation.decodeStore view code store,ambient,nextFrame::rest,[]⟩ := by
      simpa only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Core.globalGet] using actual
    have exactStep := core_global_get_value view code store inst address object ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN idx.val) :: after} :: rest,[]⟩ f rest after idx rfl moduleEq mapped issued
    rw [exactStep] at actual
    have frameEq := (List.cons.inj (congrArg SourceMachine.AState.frames (SourceMachine.AResult.next.inj actual))).1
    refine ⟨success,storeSame,platformSame,nextFrame,pc,pcNext,unchanged,fresh,source,represented,?_,?_,prefixEffect,coreStep⟩
    · rw [←frameEq]
      exact core_point_global_get_continue point _ _ after (SourceMachine.frame_typed_heights frameTyped)
        (decode_words_value_type _ _ _) tail pc pcNext
    · exact ⟨_,frameEq.symm⟩

theorem core_frame_point_global_set_step_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Representation.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ Store.MetadataPreserved store out.2.2.1 ∧
      ∃ nextFrame pc, pc.val = raw.pc.val+1 ∧
        out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧
        SourceMachine.CoreTyped {initial with store := Representation.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store initial.store (Representation.decodeStore view code out.2.2.1) ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with store := Representation.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Representation.decodeStore view code out.2.2.1) {raw with pc := pc} nextFrame compiled C targets next output ∧ (∃ values, nextFrame = {f with code := after,vals := values}) ∧
        SourceMachine.Core.step initial = .next {initial with store := Representation.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ⦄) := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (Representation.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases core_frame_point_global_set_prepare view code store inst raw f compiled C targets next output after index moduleEq frameTyped point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,valueType,position,fetch,tail⟩ := operation
    subst index
    apply WP.spec_mono (step_global_set_simulation memory hooks floats allocator view code exec store raw src idx inst address object ambient f rest after front value platform frameIndex found mapped issued moduleEq slots values position mutable valueWf valueType compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨platformSame,success,⟨pc,pcNext,unchanged⟩,metadata,nextFrame,actual,fresh,extension,source,represented⟩ := effect
    have coreStep : SourceMachine.Core.step ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN idx.val) :: after} :: rest,[]⟩ =
        .next ⟨Representation.decodeStore view code out.2.2.1,ambient,nextFrame::rest,[]⟩ := by
      simpa only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Core.globalSet,SourceMachine.AFrame.toFrame] using actual
    have typeEq : SourceMachine.valueType value = Itasca.Translation.valueType object.ty.valtype := by rw [←value_type_eq_abs]; exact valueType.symm
    have exactStep := core_global_set_value view code store inst address object ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN idx.val) :: after} :: rest,[]⟩ f rest after idx front value rfl moduleEq mapped issued values mutable typeEq
    rw [exactStep] at actual
    have frameEq := (List.cons.inj (congrArg SourceMachine.AState.frames (SourceMachine.AResult.next.inj actual))).1
    refine ⟨success,platformSame,metadata,nextFrame,pc,pcNext,unchanged,fresh,extension,source,represented,?_,?_,coreStep⟩
    · rw [←frameEq]
      exact core_point_global_set_continue point extension front value after values heights tail pc pcNext
    · exact ⟨_,frameEq.symm⟩

end Itasca.Interp.Machine.Global

end

end

/-! ## Numeric -/

section

/-!
Integer numeric machine fetch, execution and trap classification. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Numeric Inversion -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std
theorem emission_numeric_pure {compiled C before after emitted} (op : SourceMachine.Numeric.Instruction)
    (head : Interp.emission compiled C before op.source emitted after) :
    Compiler.LinearEmission C.LOCALS before op.source emitted after :=
  scalar_emission_numeric_pure op (FloatHeads.project (.core (.pure (.numeric op))) head)
end Itasca.Interp.Machine

end

/-! ## Numeric -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Numeric
theorem step_numeric {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (op : Instruction) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := op.source :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FramePoint s { raw with pc := pc } g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := op.source :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        (g = {f with code := op.source :: after} ∨
          SourceMachine.Core.step ⟨s,ambient,{f with code := op.source :: after} :: rest,[]⟩ = .next ⟨s,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (SourceMachine.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> (try casesm* Conversion) <;> rfl
  rcases structured_code_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := op.source :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨sameStore, samePlatform, .inl ⟨success, target, { f with code := op.source :: after },
      ?_, ?_, targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,?_,Or.inl rfl⟩⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
    · rw [exactState]
      exact SlotPrefix.refl _ _
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linear_emission_numeric_inv op (emission_numeric_pure op head)
    have frameTyped : SourceMachine.FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨front, a, b, split, wfFront, heights⟩ := op.typed_operands_bounds frameTyped
    have frontTypes : front.map Representation.valueType = stack := by
      rw [split, List.map_append, numeric_operand_types] at shape
      exact List.append_cancel_right shape
    have leftPosition : left.val = Representation.slots ((f.locals ++ front).map Representation.valueType) := by
      simpa only [point.locals,List.map_append, Representation.slots_append, frontTypes] using leftPos
    have fetched : compiled.code.val[raw.pc.val]? = some (Compiler.integerInstruction op left left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ op.operands a b) := by
      simpa only [FrameSlots, split, List.append_assoc] using slots
    obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_integer_values memory hooks floats allocator exec store platform index raw inst compiled
      op left right (f.locals ++ front) a b last hf hi hc fetched pcBound represented leftPosition rightPos)
    rw [returned]
    simp only [WP.spec_ok]
    have prefixEffect := step_prefix memory hooks floats allocator exec store platform index raw inst compiled
      (Compiler.integerInstruction op left left right) last hf hi hc fetched (.numeric op left left right) out returned
    obtain ⟨sameStore, samePlatform, pc, pcEq, effect⟩ := effect
    refine ⟨sameStore, samePlatform, ?_⟩
    cases operation : op.apply a b with
    | none =>
      simp only [NumericValuesEffect, operation] at effect
      obtain ⟨trap, kind, exactEffect⟩ := effect
      have sourceTrap : SourceMachine.astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .trap := by
        have h := astep_operands ⟨s, ambient, [], []⟩ f rest after front op a b
        simp only [finish, operation] at h
        simpa only [← split] using h
      refine .inr ⟨trap, congrArg Prod.fst exactEffect, kind, ?_⟩
      exact astep_trap_simulation s ambient f rest after op typed.typed sourceTrap
    | some value =>
      simp only [NumericValuesEffect, operation] at effect
      obtain ⟨success, represented, unchanged⟩ := effect
      have sourceStep : SourceMachine.astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .next
          ⟨s, ambient, { f with code := after, vals := front ++ [SourceMachine.integerVal op.output value.toNat] } :: rest, []⟩ := by
        have h := astep_operands ⟨s, ambient, [], []⟩ f rest after front op a b
        simp only [finish, operation, SourceMachine.advance] at h
        simpa only [← split] using h
      have nextTyped := SourceMachine.instruction_preservation s ambient f rest _ after _ (.numeric op) typed.typed sourceStep
      have nextPoint : FramePoint s { raw with pc := pc }
          { f with code := after, vals := front ++ [SourceMachine.integerVal op.output value.toNat] }
          compiled C targets next output := by
        apply linear_continuation point pc f.locals
          (front ++ [SourceMachine.integerVal op.output value.toNat]) after middle
        · simpa only [endpoint, pcEq] using continuation
        · rfl
        · simp only [middleEq, List.map_append, List.map_cons, List.map_nil, integer_value_type, frontTypes]
        · have labels : LabelsMatch (front ++ op.operands a b) f.labels targets := by
            simpa only [← split] using point.labels
          exact labels.replace_suffix heights
      refine .inl ⟨success, pc, { f with code := after, vals := front ++ [SourceMachine.integerVal op.output value.toNat] },
        unchanged, ?_, nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl,rfl,rfl,rfl⟩,
        .tail _ _ _ _ _ (frame_references_numeric f front _ _ _ split), ?_,prefixEffect,Or.inr ?_⟩
      · simpa only [FrameSlots, List.append_assoc] using represented
      · apply ConcreteSim.of_source
        exact astep_simulation s ambient f rest after op _ typed.typed sourceStep
      · change SourceMachine.Core.instruction s ambient {f with code := op.source :: after} rest op.source after = _
        rw [SourceMachine.Core.instruction_slice s ambient {f with code := op.source :: after} rest op.source after (.numeric op) frameTyped]
        exact sourceStep

end Itasca.Interp.Machine

end

/-! ## Numeric Fetch -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Numeric
theorem numeric_fetched {raw compiled C targets next output s} {f : SourceMachine.AFrame}
    (op : Instruction) (after : List instr)
    (point : FramePoint s raw {f with code := op.source :: after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction := by
  have linear : linearSource op.source = true := by cases op <;> (try casesm* Conversion) <;> rfl
  rcases structured_code_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,rest⟩
  · exact ⟨_,fetch⟩
  · obtain ⟨stack,left,right,shape,emittedEq,middleEq,leftPos,rightPos⟩ := linear_emission_numeric_inv op (emission_numeric_pure op head)
    refine ⟨Compiler.integerInstruction op left left right,?_⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

end Itasca.Interp.Machine

end

/-! ## Numeric Execution Owned -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Numeric

theorem step_numeric_execution_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : SourceMachine.AFrame,
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (SourceMachine.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched⟩ := numeric_fetched op after point
  have pcBound := program.fetched_bound instruction fetched
  apply WP.spec_mono (step_numeric memory hooks floats allocator exec store platform index raw inst compiled C targets
    next output (Representation.decodeStore view code store) ambient f rest op after last hf hi hc pcBound machine.typed slots point)
  intro out effect
  refine ⟨effect.1,effect.2.1,?_⟩
  rcases effect.2.2 with success | trapped
  · obtain ⟨status,pc,g,unchanged,represented,continuation,fresh,metadata,closure,simulation,prefixEffect,sourceStep⟩ := success
    have uniform : UniformConcreteSim raw.pc.val pc.val false false
        ⟨Representation.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
        ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases sourceStep with same | step
      · subst g
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (SourceMachine.Numeric.core_step_positive _ _ _ _ _ _ _ machine.typed.typed step)
    have covered : SourceMachine.SupportedState ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases sourceStep with same | step
      · simpa only [same] using machine.core
      · exact Machine.core_step_supported machine.typed machine.core step
    have ownership : ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨Representation.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ →
        SourceMachine.Ownership.StatefulOwned bounds ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ := by
      intro bounds bounded
      rcases sourceStep with same | step
      · simpa only [same] using bounded
      · exact Machine.core_step_owned machine.typed machine.core step bounds bounded
    refine Or.inl ⟨status,pc,g,?_,simulation,uniform,ownership,Machine.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))⟩
    exact machine.ordinary view code ambient {f with code := op.source :: after} g rest expected raw.pc.val false
      (.refl store) (Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last hf program (.ready continuation)
      represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged prefixEffect fresh covered
  · exact Or.inr trapped
theorem step_numeric_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : SourceMachine.AFrame,
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (SourceMachine.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_numeric_execution_owned_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest op after last hf hi hc program slots point expected machine)
  rintro out ⟨same,platform,success | trapped⟩
  · rcases success with ⟨success,pc,g,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨same,platform,Or.inl ⟨success,pc,g,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨same,platform,Or.inr trapped⟩

end Itasca.Interp.Machine

end

/-! ## Numeric No Trap -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Numeric

theorem step_numeric_no_trap {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (op : Instruction) (after : List instr)
    (total : ∀ a b, op.apply a b ≠ none)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := op.source :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => out.1 = .Ok () ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> (try casesm* Conversion) <;> rfl
  rcases structured_code_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    exact success
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linear_emission_numeric_inv op (emission_numeric_pure op head)
    have frameTyped : SourceMachine.FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨front, a, b, split, wfFront, heights⟩ := op.typed_operands_bounds frameTyped
    have frontTypes : front.map Representation.valueType = stack := by
      rw [split, List.map_append, numeric_operand_types] at shape
      exact List.append_cancel_right shape
    have leftPosition : left.val = Representation.slots ((f.locals ++ front).map Representation.valueType) := by
      simpa only [point.locals,List.map_append, Representation.slots_append, frontTypes] using leftPos
    have fetched : compiled.code.val[raw.pc.val]? = some (Compiler.integerInstruction op left left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ op.operands a b) := by
      simpa only [FrameSlots, split, List.append_assoc] using slots
    obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_integer_values memory hooks floats allocator exec store platform index raw inst compiled
      op left right (f.locals ++ front) a b last hf hi hc fetched pcBound represented leftPosition rightPos)
    rw [returned]
    simp only [WP.spec_ok]
    obtain ⟨sameStore,samePlatform,pc,pcEq,effect⟩ := effect
    cases operation : op.apply a b with
    | none => exact False.elim (total a b operation)
    | some value =>
      simp only [NumericValuesEffect,operation] at effect
      exact effect.1
end Itasca.Interp.Machine

end

end

/-! ## Select -/

section

/-!
Untyped select machine fetch, step and ownership. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Select Point -/

section

namespace Itasca.Interp.Machine.Select
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std WebAssembly Itasca.Interp
theorem core_point_select_head {C returns code labels stack pc next output} (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.SELECT none :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.SELECT none :: after) target.val next output) ∨
    (∃ front ty left right condition, stack = front ++ [ty,ty,.I32] ∧
      left.val = Representation.slots C.LOCALS+Representation.slots front ∧ right.val = left.val+Representation.width ty ∧
      condition.val = right.val+Representation.width ty ∧
      code[pc]? = some (Compiler.selectInstruction (decide (Representation.width ty = 2)) left right condition) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.SELECT none :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,left,right,condition,input,emitted,result,leftPos,rightPos,conditionPos⟩ := scalar_emission_select_inv (FloatHeads.project (.core .select) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,left,right,condition,rfl,leftPos,rightPos,conditionPos,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq

end Itasca.Interp.Machine.Select

end

/-! ## Select Step -/

section

namespace Itasca.Interp.Machine.Select
open Aeneas Aeneas.Std WebAssembly

theorem step_select_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (sourceStore : WebAssembly.store) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max) (slots : FrameSlots exec raw f)
    (point : FramePoint sourceStore raw {f with code := .SELECT none::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped {initial with frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with frames := g::rest} ∨ SourceMachine.Core.step initial = .next {initial with frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  dsimp only
  rcases core_point_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
  · have retained : FramePoint sourceStore {raw with pc := target} {f with code := .SELECT none::after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .SELECT none::after} rest C targets next output target
      last frameFound instanceFound codeFound pcBound forward fetched slots retained typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · rw [exactState]; exact .refl _ _
  · have frameTyped : SourceMachine.FrameTyped sourceStore {f with code := .SELECT none::after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨front,left,right,bits,valueTy,split,bitsBound,leftType,rightType,heights⟩ := select_typed_operands frameTyped
    have conditionType : Representation.valueType (SourceMachine.integerVal .I32 bits) = .I32 := rfl
    have stackEq : front.map Representation.valueType ++ [valueTy,valueTy,.I32] = types ++ [ty,ty,.I32] := by
      simpa only [split,List.map_append,List.map_cons,List.map_nil,leftType,rightType,conditionType] using input
    have lengthEq : (front.map Representation.valueType).length = types.length := by
      have lengths := congrArg List.length stackEq
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨frontEq,typeEq⟩ := List.append_inj stackEq lengthEq
    have sameTy : valueTy = ty := (List.cons.inj typeEq).1
    have leftType' : Representation.valueType left = ty := leftType.trans sameTy
    have rightType' : Representation.valueType right = ty := rightType.trans sameTy
    have position : a.val = Representation.slots ((f.locals++front).map Representation.valueType) := by
      simpa only [List.map_append,Representation.slots_append,point.locals,← frontEq] using leftPos
    have actual := select_source_next (s := sourceStore) (ambient := ambient) (rest := rest) (after := after) split (leftType.trans rightType.symm) bitsBound
    obtain ⟨nextState,nextEq,fresh,source⟩ := SourceMachine.Core.select_progress sourceStore ambient f rest after typed
    have nextEq' : SourceMachine.Core.step ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩ = .next nextState := nextEq
    have sameState := SourceMachine.AResult.next.inj (actual.symm.trans nextEq')
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Compiler.selectInstruction (decide (Representation.width ty = 2)) a b condition) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have continuation : FramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := front++[if bits = 0 then right else left]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (front++[left,right,SourceMachine.integerVal .I32 bits]) f.labels targets := by simpa only [split] using point.labels
        exact labels.replace_suffix heights
      · have selectedType : Representation.valueType (if bits = 0 then right else left) = ty := by split <;> first | exact rightType' | exact leftType'
        simpa only [List.map_append,List.map_cons,List.map_nil,selectedType,frontEq,pcNext] using tail
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++[left,right,SourceMachine.integerVal .I32 bits]) := by
      simpa only [FrameSlots,split,List.append_assoc] using slots
    apply WP.spec_mono (select_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw (f.locals++front) left right bits a b condition ty
      represented leftType' rightType' position rightPos conditionPos bitsBound)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,fields,preserved⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,fields,?_,continuation,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr actual,?_,preserved⟩
    · simpa only [FrameSlots,List.append_assoc] using represented
    · exact Or.inr ⟨1,by omega,by simpa using Itasca.Spec.StepsHN.cons source (Itasca.Spec.StepsHN.refl (Itasca.Spec.step_h_wf source).2)⟩
end Itasca.Interp.Machine.Select

end

/-! ## Select Execution Owned -/

section

namespace Itasca.Interp.Machine.Select
open Aeneas Aeneas.Std
theorem step_select_core_execution_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Representation.CodeInterpretation) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .SELECT none::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        UniformConcreteSim raw.pc.val pc.val false false initial {initial with frames := g::rest} [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_select_core memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Representation.decodeStore view code store) ambient f rest after last frameFound instanceFound codeFound pcBound slots point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,fields,represented,retained,fresh,metadata,transition,simulation,preserved⟩ := effect
  have uniform : UniformConcreteSim raw.pc.val pc.val false false
      ⟨Representation.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
      ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
    rcases transition with same | step
    · rw [← same] at simulation ⊢
      exact simulation.uniform_same (by scalar_tac)
    · exact UniformConcreteSim.single (SourceMachine.Core.select_step_positive _ _ _ _ _ _ machine.typed step)
  have covered : SourceMachine.SupportedState ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases transition with same | step
    · rw [← same]; exact machine.core
    · exact Machine.core_step_supported machine.typed machine.core step
  exact ⟨success,sameStore,samePlatform,pc,g,
    Execution.ordinary view code ambient {f with code := .SELECT none::after} g rest expected raw.pc.val false machine
      (.refl store) (Itasca.Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,uniform,Machine.owned_transition machine.typed machine.core transition,Machine.bound_transition machine.typed machine.core transition⟩
theorem step_select_core_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Representation.CodeInterpretation) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .SELECT none::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  apply WP.spec_mono (step_select_core_execution_owned_uniform memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,same,platform,pc,g,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,same,platform,pc,g,machine,simulation,ownership,bounded⟩

end Itasca.Interp.Machine.Select

end

end

end

/-! ## GlobalMutation -/

section

open Itasca.Representation

/-! ## ExecutionOwned -/

section

/-!
Global get/set execution with retained ownership.

Main declarations: `step_global_get_core_execution_owned_uniform` and `step_global_set_core_execution_owned`.
-/

namespace Itasca.Interp.Machine.Global
open Aeneas Aeneas.Std WebAssembly Itasca.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_global_get_core_execution_owned_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, ∃ g : SourceMachine.AFrame,
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]
    exact frameFound
  have binding := (machine.stack.top raw top).binding
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_global_get_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨mutability,ty,idx,dst,indexEq,lookup,position,fetch,tail⟩
    · exact program.fetched_bound _ fetch
    · exact program.fetched_bound _ fetch
  rcases core_frame_point_global_get_step_owned memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest after index C targets next output found moduleEq slots binding last frameFound codeFound program.checked pcBound small point machine.typed with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform frameIndex raw inst compiled
      (Representation.decodeStore view code store) ambient {f with code := .GLOBAL_GET (.mk_uN index) :: after} rest C targets next output target last frameFound found codeFound pcBound forward fetch slots tail machine.typed)
    intro out effect
    obtain ⟨success,storeSame,platformSame,exactState,represented,retained,typed,simulation⟩ := effect
    refine ⟨success,storeSame,platformSame,target,_,?_,simulation,UniformConcreteSim.forward rfl forward (by scalar_tac),fun _ h => h,fun _ h => h⟩
    exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw frameIndex target last frameFound program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ (by rw [exactState]) (by rw [exactState]; exact .refl _ _) typed machine.core
  · apply WP.spec_mono operation
    intro out effect
    obtain ⟨success,storeSame,platformSame,g,pc,pcNext,unchanged,typed,source,represented,retained,⟨values,shape⟩,prefixEffect,sourceStep⟩ := effect
    have metadata : FrameMetadata {f with code := .GLOBAL_GET (.mk_uN index) :: after} g := by rw [shape]; exact ⟨rfl,rfl,rfl,rfl⟩
    have covered : SourceMachine.SupportedState ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ := by
      exact Machine.core_step_supported machine.typed machine.core sourceStep
    refine ⟨success,storeSame,platformSame,pc,g,?_,?_,UniformConcreteSim.single source,Machine.owned_transition machine.typed machine.core (Or.inr sourceStep),Machine.bound_transition machine.typed machine.core (Or.inr sourceStep)⟩
    · exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
        (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program (.ready retained)
        represented metadata unchanged prefixEffect typed covered
    · exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (step_h_wf source).2)⟩

theorem step_global_get_core_execution_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, ∃ g : SourceMachine.AFrame,
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  apply WP.spec_mono (step_global_get_core_execution_owned_uniform memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest after index C targets next output found moduleEq slots last frameFound codeFound program small point expected machine)
  rintro out ⟨success,same,platform,pc,g,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,same,platform,pc,g,machine,simulation,ownership,bounded⟩

theorem step_global_set_core_execution_owned_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ Store.MetadataPreserved store out.2.2.1 ∧
      Extend_store initial.store (Representation.decodeStore view code out.2.2.1) ∧
      ∃ pc : U32, ∃ g : SourceMachine.AFrame,
        Execution view code out.2.2.1 out.2.1 ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false false initial ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_global_set_head index after point.code with ⟨target,forward,fetch,tail⟩ | operation
    · exact program.fetched_bound _ fetch
    · obtain ⟨ty,idx,src,front,indexEq,lookup,values,position,fetch,tail⟩ := operation
      exact program.fetched_bound _ fetch
  rcases core_frame_point_global_set_step_owned memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest after index C targets next output found moduleEq slots last frameFound codeFound pcBound point machine.typed with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform frameIndex raw inst compiled
      (Representation.decodeStore view code store) ambient {f with code := .GLOBAL_SET (.mk_uN index) :: after} rest C targets next output target last frameFound found codeFound pcBound forward fetch slots tail machine.typed)
    intro out effect
    obtain ⟨success,storeSame,platformSame,exactState,represented,retained,typed,simulation⟩ := effect
    simp only [storeSame]
    refine ⟨success,platformSame,.refl store,extend_store_refl _ machine.typed.typed.store,target,_,?_,simulation,UniformConcreteSim.forward rfl forward (by scalar_tac),fun _ h => h,fun _ h => h⟩
    exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw frameIndex target last frameFound program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ (by rw [exactState]) (by rw [exactState]; exact .refl _ _) typed machine.core
  · apply WP.spec_mono operation
    intro out effect
    obtain ⟨success,platformSame,stores,g,pc,pcNext,unchanged,typed,extension,source,represented,retained,⟨values,shape⟩,sourceStep⟩ := effect
    have metadata : FrameMetadata {f with code := .GLOBAL_SET (.mk_uN index) :: after} g := by rw [shape]; exact ⟨rfl,rfl,rfl,rfl⟩
    have covered : SourceMachine.SupportedState ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ := by
      exact Machine.core_step_supported machine.typed machine.core sourceStep
    refine ⟨success,platformSame,stores,extension,pc,g,?_,?_,UniformConcreteSim.single source,Machine.owned_transition machine.typed machine.core (Or.inr sourceStep),Machine.bound_transition machine.typed machine.core (Or.inr sourceStep)⟩
    · exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false stores extension
        raw frameIndex pc last frameFound program (.ready retained)
        represented metadata (by rw [unchanged]) (by rw [unchanged]; exact .refl _ _) typed covered
    · exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (step_h_wf source).2)⟩
theorem step_global_set_core_execution_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ Store.MetadataPreserved store out.2.2.1 ∧
      Extend_store initial.store (Representation.decodeStore view code out.2.2.1) ∧
      ∃ pc : U32, ∃ g : SourceMachine.AFrame,
        Execution view code out.2.2.1 out.2.1 ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩) ⦄ := by
  apply WP.spec_mono (step_global_set_core_execution_owned_uniform memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest after index C targets next output found moduleEq slots last frameFound codeFound program point expected machine)
  rintro out ⟨success,platform,metadata,extension,pc,g,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,platform,metadata,extension,pc,g,machine,simulation,ownership,bounded⟩

end Itasca.Interp.Machine.Global

end

/-! ## Mutation -/

section

/-!
Structured global-write mutation. The point-step effect establishes the retained source/store mutation certificate used by full machine execution.
-/

/-! ## Global Mutation Step -/

section

namespace Itasca.Interp.Machine.Global
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem core_frame_point_global_set_mutation (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target)) ∨
    (∃ front value, f.vals = front ++ [value] ∧ wf_val value ∧
      runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => GlobalMutation store out.2.2.1 value ⦄) := by
  have frameTyped : SourceMachine.FrameTyped (Representation.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases core_frame_point_global_set_prepare view code store inst raw f compiled C targets next output after index moduleEq frameTyped point with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch⟩
  · obtain ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,valueType,position,fetch,tail⟩ := operation
    subst index
    refine Or.inr ⟨front,value,values,valueWf,?_⟩
    exact step_global_set_mutation memory hooks floats allocator exec store raw src idx inst address object f front value
      platform frameIndex found mapped issued slots values position mutable valueType compiled last frameFound codeFound fetch pcBound
end Itasca.Interp.Machine.Global

end

/-! ## Global Mutation -/

section

namespace Itasca.Interp.Machine.Global
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem core_frame_point_global_set_store_mutation (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CoreStoreMutation view ⟨Representation.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩ store out.2.2.1 ⦄ := by
  rcases core_frame_point_global_set_mutation memory hooks floats allocator platform frameIndex view code exec store raw inst compiled
    ambient f rest after index C targets next output found moduleEq slots last frameFound codeFound pcBound point typed with jump | mutation
  · obtain ⟨target,forward,fetch⟩ := jump
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform frameIndex raw inst compiled target
      last frameFound found codeFound pcBound fetch)
    intro out effect
    rw [effect.2.2.1]
    exact .unchanged
  · obtain ⟨front,value,values,wellFormed,mutation⟩ := mutation
    apply WP.spec_mono mutation
    intro out effect
    apply CoreStoreMutation.global ?_ wellFormed effect
    exact Or.inr ⟨{f with code := .GLOBAL_SET (.mk_uN index) :: after},by simp,Or.inr (by simpa only [values] using List.mem_append_right front (List.mem_singleton_self value))⟩
end Itasca.Interp.Machine.Global

end

end

end

/-! ## LocalOwnership -/

section

open Itasca.Representation

/-!
# Execution Owned

Local reads and writes preserve operand ownership and frame prefixes. Move inversion and capacity facts establish the concrete local-instruction execution contracts.
-/

/-! ## MovePrefix -/

section

/-!
Slot-prefix preservation for local moves.

Main declarations: `move_prefix`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem move_prefix (ty : valtype) (dst src : U32) : PrefixInstruction (Compiler.move ty dst src) := by
  unfold Compiler.move
  split
  · exact .copy2 ..
  · exact .copy ..

end Itasca.Interp

end

/-! ## Inversion -/

section

/-!
Inversion of local get/write emission.

Main declarations: `emission_local_get_pure` and `emission_local_write_pure`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std
theorem emission_local_get_pure {compiled C before after emitted} (index : Nat)
    (head : Interp.emission compiled C before (.LOCAL_GET (.mk_uN index)) emitted after) :
    Compiler.LinearEmission C.LOCALS before (.LOCAL_GET (.mk_uN index)) emitted after :=
  scalar_emission_local_get_pure index (FloatHeads.project (.core (.pure (.local_get _))) head)
theorem emission_local_write_pure {compiled C before after emitted} (index : Nat) (keep : Bool)
    (head : Interp.emission compiled C before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after) :
    Compiler.LinearEmission C.LOCALS before (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) emitted after :=
  scalar_emission_local_write_pure index keep (FloatHeads.project (by cases keep;exact .core (.pure (.local_set _));exact .core (.pure (.local_tee _))) head)
end Itasca.Interp.Machine

end

/-! ## ExecutionOwned -/

section

/-!
Local-variable structured execution and ownership. Fetch, capacity and get/write frame effects assemble the complete execution relation without changing surrounding frame slots.
-/

/-! ## Local Capacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Itasca.Interp.Machine
/-- Even behind forward skips, a local read's destination lies within the
allocation checked for the complete function bytecode. -/
theorem structured_local_get_capacity
    (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype)
    (labels : List LabelTarget) (index : Nat) (after : List instr)
    (next : Nat) (output : List valtype) (ty : valtype)
    (localType : C.LOCALS[index]? = some ty) :
    ∀ pc, StructuredCode (Interp.emission compiled C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.LOCAL_GET (.mk_uN index) :: after) pc next output →
      slots C.LOCALS + slots stack + width ty ≤ compiled.slot_count.val := by
  intro pc relation
  generalize measureEq : compiled.code.val.length - pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases Interp.Machine.structured_code_linear_inv (by rfl) relation with skip | branch
    · obtain ⟨target, forward, fetched, continuation⟩ := skip
      have targetBound := continuation.entry_bound
      exact ih (compiled.code.val.length - target.val) (by omega) target.val continuation rfl
    · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
      obtain ⟨actual, src, dst, actualType, emittedEq, middleEq, source, position⟩ :=
        Interp.linear_emission_local_get_inv index (Interp.Machine.emission_local_get_pure index head)
      have same : actual = ty := Option.some.inj (actualType.symm.trans localType)
      subst actual
      have fetched : compiled.code.val[pc]? = some (move ty dst src) := by
        simpa only [Nat.add_zero] using fragment.fetch (index := 0)
          (by simp only [emittedEq, List.getElem?_cons_zero])
      have valid := well_formed_fetched compiled checked pc _ fetched
      have bound := (move_valid_bounds compiled ty dst src valid).1
      simpa only [position] using bound

end Itasca.Compiler

namespace Itasca.Interp
open Aeneas Aeneas.Std
open Itasca.Interp.Machine
/-- LOCAL_GET needs no independent spare-capacity premise: retained code and
frame certificates establish it for the actual represented local value. -/
theorem structured_local_get_storage_capacity {M : Type}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    {s C targets next output} (index : Nat) (after : List instr)
    (point : FramePoint s raw { source with code := .LOCAL_GET (.mk_uN index) :: after }
      compiled C targets next output)
    (value : val) (lookup : source.locals[index]? = some value) :
    raw.base.val + Representation.slots ((source.locals ++ source.vals).map Representation.valueType) +
      Representation.width (Representation.valueType value) ≤ exec.slots.length := by
  have localType : (source.locals.map Representation.valueType)[index]? = some (Representation.valueType value) := by
    simp only [List.getElem?_map, lookup, Option.map_some]
  have bound := Compiler.structured_local_get_capacity compiled checked C source.resultTypes
    (source.vals.map Representation.valueType) targets index after next output
    (Representation.valueType value) (by simpa only [point.locals] using localType) raw.pc.val point.code.current
  rw [point.locals] at bound
  change Representation.slots (source.locals.map Representation.valueType) + Representation.slots (source.vals.map Representation.valueType) + Representation.width (Representation.valueType value) ≤ compiled.slot_count.val at bound
  have capacity := binding.capacity inst compiled hi hc
  simp only [List.map_append, Representation.slots_append]
  omega

end Itasca.Interp

end

/-! ## Local Get Owned -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std
theorem step_local_get_owned_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (localIndex : U32) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : ∀ value, f.locals[localIndex.val]? = some value →
      raw.base.val + Representation.slots ((f.locals ++ f.vals).map Representation.valueType) + Representation.width (Representation.valueType value) ≤ exec.slots.length)
    (point : FramePoint s raw { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (targets' : List Compiler.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool), raw.pc.val < pc.val ∧ pending = false ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        (g = {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} ∨ ∃locals values, g = {f with code := after,locals := locals,vals := values}) ∧
        FrameOwnershipClosure {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} g ⦄ := by
  rcases structured_code_linear_inv (by rfl) point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after },
      targets, next, output, false, forward, rfl, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨ty, src, dst, localType, emittedEq, middleEq, source, position⟩ := linear_emission_local_get_inv localIndex.val (emission_local_get_pure localIndex.val head)
    obtain ⟨value, lookup, tyEq⟩ := values_type_lookup f.locals localIndex.val ty (by simpa only [point.locals] using localType)
    subst ty
    have destination : dst.val = Representation.slots ((f.locals ++ f.vals).map Representation.valueType) := by
      simpa only [point.locals,List.map_append, Representation.slots_append] using position
    have fetched : compiled.code.val[raw.pc.val]? = some (Compiler.move (Representation.valueType value) dst src) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have frameTyped : SourceMachine.FrameTyped s { f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    have localBound : localIndex.val < f.locals.length := List.getElem?_eq_some_iff.mp lookup |>.1
    have valueEq : f.locals[localIndex.val]! = value := by
      simpa only [List.getElem?_eq_getElem localBound, Option.some.injEq, getElem!_pos f.locals localIndex.val localBound] using lookup
    have nextFrame := SourceMachine.local_get_frame_preservation frameTyped
    rw [valueEq] at nextFrame
    have nextTyped := SourceMachine.active_frame_preservation typed.typed nextFrame rfl
    have labelsAfter : LabelsMatch (f.vals ++ [value]) f.labels targets := by
      have old : LabelsMatch (f.vals ++ []) f.labels targets := by simpa only [List.append_nil] using point.labels
      have heights := SourceMachine.frame_typed_heights frameTyped
      exact old.replace_suffix heights
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Compiler.move (Representation.valueType value) dst src) last hf hi hc fetched pcBound
    intro pc hpc
    have nextPoint : FramePoint s { raw with pc := pc }
        { f with code := after, vals := f.vals ++ [value] }
        compiled C targets next output := by
      apply linear_continuation point pc f.locals (f.vals ++ [value]) after middle
      · simpa only [endpoint, hpc] using continuation
      · rfl
      · simp only [middleEq, List.map_append, List.map_cons, List.map_nil]
      · exact labelsAfter
    apply WP.spec_mono (dispatch_local_get_refines memory hooks floats allocator
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index raw localIndex src dst
      s ambient f rest after f.vals value lookup typed.typed slots (by simpa only [point.locals] using source) destination
      (by simpa only [destination] using capacity value lookup))
    intro out effect
    obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
    refine ⟨success, sameStore, samePlatform, pc,
      { f with code := after, vals := f.vals ++ [value] }, targets, next, output, false, (by omega), rfl,
      unchanged, represented, .ready nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, rfl⟩, .tail _ _ _ _ _ (frame_references_local_get f localIndex.val value lookup), ?_,Or.inr ⟨_,_,rfl⟩,?_⟩
    · apply ConcreteSim.of_source
      exact simulation
    · exact FrameOwnershipClosure.local_get {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} after localIndex.val value lookup

end Itasca.Interp.Machine

end

/-! ## Local Prefix -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std
theorem local_get_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame}
    (index : Nat) (after : List instr)
    (point : FramePoint s raw {f with code := .LOCAL_GET (.mk_uN index)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases structured_code_linear_inv (by rfl) point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,continuation⟩
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨ty,src,dst,localType,emittedEq,middleEq,source,position⟩ := linear_emission_local_get_inv index (emission_local_get_pure index head)
    refine ⟨Compiler.move ty dst src,?_,move_prefix ty dst src⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

theorem local_write_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame}
    (index : Nat) (keep : Bool) (after : List instr)
    (point : FramePoint s raw {f with code := (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index))::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  have linear : linearSource (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = true := by cases keep <;> rfl
  rcases structured_code_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,continuation⟩
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨stack,ty,dst,src,shape,localType,emittedEq,middleEq,destination,source⟩ := linear_emission_local_write_inv index keep (emission_local_write_pure index keep head)
    refine ⟨Compiler.move ty dst src,?_,move_prefix ty dst src⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])
end Itasca.Interp.Machine

end

/-! ## Local Write Owned -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std
theorem step_local_write_owned_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : WebAssembly.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (localIndex : U32) (keep : Bool) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (targets' : List Compiler.LabelTarget) (next' : Nat)
        (output' : List valtype) (pending : Bool), raw.pc.val < pc.val ∧ pending = false ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        ControlPoint s { raw with pc := pc } g compiled C targets' next' output' pending ∧
        SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        (g = {f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after} ∨ ∃locals values, g = {f with code := after,locals := locals,vals := values}) ∧
        FrameOwnershipClosure {f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after} g ⦄ := by
  have linear : linearSource (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) = true := by cases keep <;> rfl
  rcases structured_code_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨success, sameStore, samePlatform, target, { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after },
      targets, next, output, false, forward, rfl, ?_, ?_, .ready targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,Or.inl rfl,.refl _⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, ty, dst, src, shape, localType, emittedEq, middleEq, destination, source⟩ :=
      linear_emission_local_write_inv localIndex.val keep (emission_local_write_pure localIndex.val keep head)
    obtain ⟨front, value, valuesSplit, frontTypes, valueType⟩ := values_type_suffix f.vals stack ty shape
    obtain ⟨old, lookup, oldType⟩ := values_type_lookup f.locals localIndex.val ty (by simpa only [point.locals] using localType)
    have compatible : Representation.valueType value = Representation.valueType old := valueType.trans oldType.symm
    have frameTyped : SourceMachine.FrameTyped s
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    have frameTyped' : SourceMachine.FrameTyped s
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after, vals := front ++ [value] } [] := by
      simpa only [← valuesSplit] using frameTyped
    have typed' : SourceMachine.ATyped ⟨s, ambient,
        { f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after, vals := front ++ [value] } :: rest, []⟩ := by
      simpa only [← valuesSplit] using typed.typed
    have slots' : FrameSlots exec raw { f with vals := front ++ [value] } := by
      simpa only [← valuesSplit] using slots
    have nextFrame : SourceMachine.FrameTyped s
        { f with code := after, locals := f.locals.set localIndex.val value, vals := if keep then front ++ [value] else front } [] := by
      cases keep with
      | false => exact SourceMachine.local_set_frame_preservation frameTyped'
      | true => exact SourceMachine.local_tee_frame_preservation frameTyped'
    have nextTyped := SourceMachine.active_frame_preservation typed.typed nextFrame rfl
    have heights := frame_linear_heights frameTyped linear front (by
      rw [valuesSplit]
      cases keep <;> simp [linearInputs])
    have labelsAfter : LabelsMatch (if keep then front ++ [value] else front) f.labels targets := by
      have labels : LabelsMatch (front ++ [value]) f.labels targets := by simpa only [← valuesSplit] using point.labels
      cases keep with
      | true => exact labels
      | false => simpa only [List.append_nil, Bool.false_eq_true, ite_false] using labels.replace_suffix (after := []) heights
    have fetched : compiled.code.val[raw.pc.val]? = some (Compiler.move (Representation.valueType value) dst src) := by
      simpa only [Nat.add_zero, valueType] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have sourcePosition : src.val = Representation.slots ((f.locals ++ front).map Representation.valueType) := by
      simpa only [point.locals,List.map_append, Representation.slots_append, frontTypes] using source
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Compiler.move (Representation.valueType value) dst src) last hf hi hc fetched pcBound
    intro pc hpc
    have nextPoint : FramePoint s { raw with pc := pc }
        { f with code := after, locals := f.locals.set localIndex.val value, vals := if keep then front ++ [value] else front }
        compiled C targets next output := by
      apply linear_continuation point pc (f.locals.set localIndex.val value)
        (if keep then front ++ [value] else front) after middle
      · simpa only [endpoint, hpc] using continuation
      · exact Compiler.value_types_set lookup compatible
      · cases keep <;> simp only [middleEq, Bool.false_eq_true, ite_false, ite_true, List.map_append,
          List.map_cons, List.map_nil, frontTypes, valueType]
      · exact labelsAfter
    apply WP.spec_mono (dispatch_local_write_refines memory hooks floats allocator
      { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index raw
      localIndex src dst keep s ambient f rest after front value old lookup compatible typed' slots' sourcePosition (by simpa only [point.locals] using destination))
    intro out effect
    obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
    refine ⟨success, sameStore, samePlatform, pc,
      { f with code := after, locals := f.locals.set localIndex.val value, vals := if keep then front ++ [value] else front },
      targets, next, output, false, (by omega), rfl, unchanged, represented, .ready nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl, rfl, rfl, Compiler.value_types_set lookup compatible⟩, .tail _ _ _ _ _ (frame_references_local_write f localIndex.val front value keep valuesSplit), ?_,Or.inr ⟨_,_,rfl⟩,?_⟩
    · apply ConcreteSim.of_source
      simpa only [← valuesSplit] using simulation
    · cases keep
      · simpa only [Bool.false_eq_true,ite_false,←valuesSplit] using FrameOwnershipClosure.local_set f (.LOCAL_SET (.mk_uN localIndex.val)::after) after front value localIndex.val
      · simpa only [ite_true,←valuesSplit] using FrameOwnershipClosure.local_tee f (.LOCAL_TEE (.mk_uN localIndex.val)::after) after front value localIndex.val

end Itasca.Interp.Machine

end

/-! ## Local Execution Owned -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std WebAssembly Itasca.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_local_get_execution_owned_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (localIndex : U32)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,allowed⟩ := local_get_fetch localIndex.val after point
  have pcBound := program.fetched_bound instruction fetched
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]
    exact frameFound
  have binding := (machine.stack.top raw top).binding
  have capacity := structured_local_get_storage_capacity binding inst compiled found codeFound program.checked localIndex.val after point
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_local_get_owned_forward memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Representation.decodeStore view code store) ambient f rest localIndex after last frameFound found codeFound pcBound machine.typed slots capacity point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched allowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,forward,pendingEq,unchanged,represented,retained,typed,metadata,closure,simulation,shape,ownership⟩ := effect
  subst pending
  have uniform := simulation.uniform_forward forward (by scalar_tac)
  have covered : SourceMachine.SupportedState ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | ⟨locals,values,same⟩
    · rw [same]; exact machine.core
    · rw [same]; exact Machine.SyntaxClosure.supported (SyntaxClosure.tail _ _ _ _ _) machine.core
  refine ⟨success,storeSame,platformSame,pc,g,false,?_,simulation,uniform,fun _ h => FrameOwnershipClosure.stateful ownership h,fun _ bounded => closure.code_bound bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

theorem step_local_write_execution_owned_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (localIndex : U32) (keep : Bool)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Representation.decodeStore view code store,ambient,{f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,allowed⟩ := local_write_fetch localIndex.val keep after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_local_write_owned_forward memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Representation.decodeStore view code store) ambient f rest localIndex keep after last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched allowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,forward,pendingEq,unchanged,represented,retained,typed,metadata,closure,simulation,shape,ownership⟩ := effect
  subst pending
  have uniform := simulation.uniform_forward forward (by scalar_tac)
  have covered : SourceMachine.SupportedState ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | ⟨locals,values,same⟩
    · rw [same]; exact machine.core
    · rw [same]; exact Machine.SyntaxClosure.supported (SyntaxClosure.tail _ _ _ _ _) machine.core
  refine ⟨success,storeSame,platformSame,pc,g,false,?_,simulation,uniform,fun _ h => FrameOwnershipClosure.stateful ownership h,fun _ bounded => closure.code_bound bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

end Itasca.Interp.Machine

end

end

end

/-! ## MemoryAndNormalization -/

section

open Itasca.Representation

/-!
# Memory And Normalization

Memory instruction effects and machine normalization preserve the concrete interpreter relation.
-/

/-! ## Memory -/

section

/-!
Scalar memory machine instruction preparation, execution and ownership. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Memory Point -/

section

namespace Itasca.Interp.Machine.Memory
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Itasca.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem core_point_load_head {C returns code labels stack pc next output}
    (op : SourceMachine.Memory.Load) (argument : memarg) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (op.source argument :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (op.source argument :: after) target.val next output) ∨
    (∃ front address offset, stack = front ++ [.I32] ∧
      address.val = Representation.slots C.LOCALS + Representation.slots front ∧ argument.OFFSET = .mk_uN offset.val ∧
      code[pc]? = some (Compiler.memoryLoadInstruction op address address offset) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [valtype_numtype op.type]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source argument :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,address,offset,input,emitted,result,offsetEq,position⟩ := scalar_emission_load_inv op argument (FloatHeads.project (.core (.load op argument)) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,address,offset,rfl,position,offsetEq,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp [SourceMachine.Memory.Load.source] at sourceEq

 theorem core_point_store_head {C returns code labels stack pc next output}
    (op : SourceMachine.Memory.Store) (argument : memarg) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (op.source argument :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (op.source argument :: after) target.val next output) ∨
    (∃ front address value offset, stack = front ++ [.I32,valtype_numtype op.type] ∧
      address.val = Representation.slots C.LOCALS + Representation.slots front ∧ value.val = address.val+1 ∧ argument.OFFSET = .mk_uN offset.val ∧
      code[pc]? = some (Compiler.memoryStoreInstruction op address value offset) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        front after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source argument :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,address,value,offset,input,emitted,result,offsetEq,position,valuePosition⟩ := scalar_emission_store_inv op argument (FloatHeads.project (.core (.store op argument)) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,address,value,offset,rfl,position,valuePosition,offsetEq,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp [SourceMachine.Memory.Store.source] at sourceEq
end Itasca.Interp.Machine.Memory

end

/-! ## Memory Continue -/

section

namespace Itasca.Interp.Machine.Memory
open Itasca.Interp.MemoryDescriptor
open Aeneas Aeneas.Std WebAssembly

theorem core_point_load_continue {sourceStore raw f compiled C targets next output}
    (point : FramePoint sourceStore raw f compiled C targets next output)
    (front : List val) (bits : Nat) (value : val) (ty : numtype) (after : List instr)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits])
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (valueType : Representation.valueType value = valtype_numtype ty)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Representation.valueType ++ [valtype_numtype ty]) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint sourceStore {raw with pc := pc} {f with code := after,vals := front ++ [value]}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,List.map_cons,List.map_nil,valueType,pcNext] using tail

theorem core_point_store_continue {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front operands : List val) (after : List instr)
    (values : f.vals = front ++ operands)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Representation.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint afterStore {raw with pc := pc} {f with code := after,vals := front}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  · simpa only [pcNext] using tail
end Itasca.Interp.Machine.Memory

end

/-! ## Memory Prepare -/

section

namespace Itasca.Interp.Machine.Memory
open Itasca.Interp.MemoryDescriptor
open Aeneas Aeneas.Std WebAssembly

theorem core_frame_point_load_prepare {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (op : SourceMachine.Memory.Load) (argument : memarg)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (typed : SourceMachine.FrameTyped (Representation.decodeStore view code store) {f with code := op.source argument :: after} [])
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Representation.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (∃ front bits memoryAddress object address offset,
      f.vals = front ++ [SourceMachine.integerVal .I32 bits] ∧ bits < 2^32 ∧
      inst.memories.val[0]? = some memoryAddress ∧ store.memories.val[memoryAddress.index.val]? = some object ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      address.val = Representation.slots (f.locals.map Representation.valueType) + Representation.slots (front.map Representation.valueType) ∧
      proj_uN_0 argument.OFFSET = offset.val ∧
      compiled.code.val[raw.pc.val]? = some (Compiler.memoryLoadInstruction op address address offset) ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Representation.valueType ++ [valtype_numtype op.type]) after (raw.pc.val+1) next output) := by
  rcases core_point_load_head op argument after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,address,offset,input,position,offsetEq,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,bits,memoryAddress,object,values,bound,mapped,issued,wf,heights⟩ :=
      load_typed_operands_full view code store inst f after op argument moduleEq typed
    have typesEq : front.map Representation.valueType = types := by
      have eq := input
      simp only [values,List.map_append,List.map_cons,List.map_nil,Representation.valueType,SourceMachine.integerVal,numtype_Inn] at eq
      exact List.append_cancel_right eq
    refine Or.inr ⟨front,bits,memoryAddress,object,address,offset,values,bound,mapped,issued,heights,?_,?_,fetch,?_⟩
    · simpa only [← point.locals,typesEq] using position
    · simp only [offsetEq,proj_uN_0]
    · simpa only [typesEq] using tail

theorem core_frame_point_store_prepare {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (op : SourceMachine.Memory.Store) (argument : memarg)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (typed : SourceMachine.FrameTyped (Representation.decodeStore view code store) {f with code := op.source argument :: after} [])
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Representation.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (∃ front bits number memoryAddress object address value offset,
      f.vals = front ++ [SourceMachine.integerVal .I32 bits,.CONST op.type number] ∧ bits < 2^32 ∧ wf_num_ op.type number ∧
      inst.memories.val[0]? = some memoryAddress ∧ store.memories.val[memoryAddress.index.val]? = some object ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      address.val = Representation.slots (f.locals.map Representation.valueType) + Representation.slots (front.map Representation.valueType) ∧
      value.val = address.val+1 ∧ proj_uN_0 argument.OFFSET = offset.val ∧
      compiled.code.val[raw.pc.val]? = some (Compiler.memoryStoreInstruction op address value offset) ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Representation.valueType) after (raw.pc.val+1) next output) := by
  rcases core_point_store_head op argument after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,address,value,offset,input,position,valuePosition,offsetEq,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,bits,number,memoryAddress,object,values,bound,numberWf,mapped,issued,wf,heights⟩ :=
      store_typed_operands_full view code store inst f after op argument moduleEq typed
    have typesEq : front.map Representation.valueType = types := by
      have eq := input
      simp only [values,List.map_append,List.map_cons,List.map_nil,Representation.valueType,SourceMachine.integerVal,numtype_Inn] at eq
      exact List.append_cancel_right eq
    refine Or.inr ⟨front,bits,number,memoryAddress,object,address,value,offset,values,bound,numberWf,mapped,issued,heights,?_,valuePosition,?_,fetch,?_⟩
    · simpa only [← point.locals,typesEq] using position
    · simp only [offsetEq,proj_uN_0]
    · simpa only [typesEq] using tail
end Itasca.Interp.Machine.Memory

end

/-! ## Memory Certified Step -/

section

namespace Itasca.Interp.Machine.Memory
open Itasca.Interp.MemoryDescriptor
open Aeneas Aeneas.Std WebAssembly Itasca.Spec

theorem core_frame_point_load_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (op : SourceMachine.Memory.Load) (argument : memarg) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Representation.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((∃ nextFrame pc, out.1 = .Ok () ∧
        SourceMachine.Core.step initial = .next {initial with frames := nextFrame :: rest} ∧ pc.val = raw.pc.val+1 ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        SourceMachine.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Representation.decodeStore view code store) {raw with pc := pc} nextFrame compiled C targets next output ∧
        (∃ values, nextFrame = {f with code := after,vals := values}) ∧
        ∃ position word, raw.base.val ≤ position ∧ position < exec.slots.length ∧
          out.2.1.slots.val = exec.slots.val.set position word) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}}) ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) [] ⟨⟨Representation.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄) := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (Representation.decodeStore view code store) {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases core_frame_point_load_prepare view code store inst raw f compiled C targets next output after op argument moduleEq frameTyped point with jump | operation
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
        exact core_point_load_continue point front bits value op.type after values heights valueType tail pc pcNext
      · obtain ⟨word,capacity,exactWords⟩ := footprint success
        exact ⟨raw.base.val+address.val,word,Nat.le_add_right _ _,capacity,exactWords⟩
    · exact Or.inr trapped

theorem core_frame_point_store_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (op : SourceMachine.Memory.Store) (argument : memarg) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Representation.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
      ∃ memoryAddress object, inst.memories.val[0]? = some memoryAddress ∧
        store.memories.val[memoryAddress.index.val]? = some object ∧
        MemoryMutation view store out.2.2.1 memoryAddress object ∧
      ((∃ nextFrame, out.1 = .Ok () ∧
        SourceMachine.Core.step initial = .next {initial with store := Representation.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        SourceMachine.CoreTyped {initial with store := Representation.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view code out.2.2.1) ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with store := Representation.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Representation.decodeStore view code out.2.2.1) {raw with pc := pc} nextFrame compiled C targets next output ∧
        (∃ values, nextFrame = {f with code := after,vals := values})) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Representation.decodeStore view code out.2.2.1 = Representation.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) [] ⟨⟨Representation.decodeStore view code store,ambient⟩,[.TRAP]⟩))) ⦄) := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (Representation.decodeStore view code store) {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases core_frame_point_store_prepare view code store inst raw f compiled C targets next output after op argument moduleEq frameTyped point with jump | operation
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
      · exact core_point_store_continue point extension front _ after values heights tail pc pcNext
    · exact Or.inr trapped

end Itasca.Interp.Machine.Memory

end

/-! ## Memory Run -/

section

namespace Itasca.Interp.Machine.Memory
open Itasca.Interp.MemoryDescriptor
open Aeneas Aeneas.Std WebAssembly Itasca.Spec
theorem step_memory_load_core {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (op : SourceMachine.Memory.Load) (argument : memarg) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : SourceMachine.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint (Representation.decodeStore view code store) {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped {initial with frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with frames := g::rest} ∨ SourceMachine.Core.step initial = .next {initial with frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word)) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ ∃ n, 0 < n ∧
        StepsHN n (SourceMachine.decode initial) [] ⟨⟨Representation.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  rcases core_frame_point_load_step memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point typed with jump | operation
  · obtain ⟨target,forward,fetched,tail⟩ := jump
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      (Representation.decodeStore view code store) ambient {f with code := op.source argument::after} rest C targets next output target
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
      exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (step_h_wf source).2)⟩
    · exact Or.inr ⟨failed,trace⟩

theorem step_memory_store_core {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (op : SourceMachine.Memory.Store) (argument : memarg) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧ Store.MetadataPreserved store out.2.2.1 ∧
      Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view code out.2.2.1) ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      ∃ pc : U32, out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
      ((out.1 = .Ok () ∧ ∃ g : SourceMachine.AFrame,
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint (Representation.decodeStore view code out.2.2.1) {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} ∨
          SourceMachine.Core.step initial = .next {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Representation.decodeStore view code out.2.2.1 = Representation.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) [] ⟨⟨Representation.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  rcases core_frame_point_store_step memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point typed with jump | operation
  · obtain ⟨target,forward,fetched,tail⟩ := jump
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      (Representation.decodeStore view code store) ambient {f with code := op.source argument::after} rest C targets next output target
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
      exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (step_h_wf source).2)⟩
    · have extension : Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view code out.2.2.1) := by
        rw [unchanged]
        exact extend_store_refl _ typed.typed.store
      exact ⟨samePlatform,mutation.frame_metadata,extension,Or.inr ⟨_,_,issued,mutation⟩,pc,exactState,Or.inr ⟨failed,unchanged,trace⟩⟩

end Itasca.Interp.Machine.Memory

end

/-! ## Memory Execution Owned -/

section

namespace Itasca.Interp.Machine.Memory
open Aeneas Aeneas.Std WebAssembly Itasca.Spec
theorem step_memory_load_execution_owned_uniform {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (op : SourceMachine.Memory.Load) (argument : memarg) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      Store.MetadataPreserved store out.2.2.1 ∧
      Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code out.2.2.1 out.2.1
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} ∧
        UniformConcreteSim raw.pc.val pc.val false false initial
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Representation.decodeStore view code out.2.2.1 = Representation.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) []
          ⟨⟨Representation.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_load_head op argument after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,address,offset,input,position,offsetEq,fetched,tail⟩
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
        ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
        ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases transition with same | step
      · rw [← same] at simulation ⊢
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (SourceMachine.Core.load_step_positive _ _ _ _ _ _ _ _ machine.typed step)
    have covered : SourceMachine.SupportedState ⟨Representation.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases transition with same | step
      · rw [← same]; exact machine.core
      · exact Machine.core_step_supported machine.typed machine.core step
    have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
      rcases footprint with same | ⟨position,word,above,bound,changed⟩
      · rw [same]; exact .refl _ _
      · rw [changed]; exact .set _ _ _ _ above
    exact Or.inl ⟨success,pc,g,Execution.ordinary view code ambient {f with code := op.source argument::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound
      program (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,uniform,Machine.owned_transition machine.typed machine.core transition,Machine.bound_transition machine.typed machine.core transition⟩
  · exact Or.inr ⟨failed,rfl,trace⟩

theorem step_memory_load_execution_owned {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (op : SourceMachine.Memory.Load) (argument : memarg) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      Store.MetadataPreserved store out.2.2.1 ∧
      Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code out.2.2.1 out.2.1
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Representation.decodeStore view code out.2.2.1 = Representation.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) []
          ⟨⟨Representation.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_memory_load_execution_owned_uniform memory hooks floats allocator platform index view laws code exec store raw inst compiled ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound point expected machine program)
  rintro out ⟨platform,mutation,metadata,extension,success | trapped⟩
  · rcases success with ⟨success,pc,g,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨platform,mutation,metadata,extension,Or.inl ⟨success,pc,g,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨platform,mutation,metadata,extension,Or.inr trapped⟩

theorem step_memory_store_execution_owned_uniform {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (op : SourceMachine.Memory.Store) (argument : memarg) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      Store.MetadataPreserved store out.2.2.1 ∧
      Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code out.2.2.1 out.2.1
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} ∧
        UniformConcreteSim raw.pc.val pc.val false false initial
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Representation.decodeStore view code out.2.2.1 = Representation.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) []
          ⟨⟨Representation.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_store_head op argument after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,address,value,offset,input,position,valuePosition,offsetEq,fetched,tail⟩
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
        ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
        ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ [] := by
      rcases transition with same | step
      · rw [← same] at simulation ⊢
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (SourceMachine.Core.store_step_positive _ _ _ _ _ _ _ _ machine.typed step)
    have covered : SourceMachine.SupportedState ⟨Representation.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ := by
      rcases transition with same | step
      · rw [← same]; exact machine.core
      · exact Machine.core_step_supported machine.typed machine.core step
    have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
      rw [fields]; exact .refl _ _
    have untouched : {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} := by rw [fields]
    exact Or.inl ⟨success,pc,g,Execution.ordinary view code ambient {f with code := op.source argument::after} g rest expected raw.pc.val false machine
      stores extension raw index pc last frameFound program (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ untouched preserved fresh covered,simulation,uniform,Machine.owned_transition machine.typed machine.core transition,Machine.bound_transition machine.typed machine.core transition⟩
  · exact Or.inr ⟨failed,sameStore,trace⟩

theorem step_memory_store_execution_owned {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (op : SourceMachine.Memory.Store) (argument : memarg) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Representation.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : FramePoint (Representation.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Representation.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Representation.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      Store.MetadataPreserved store out.2.2.1 ∧
      Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code out.2.2.1 out.2.1
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with store := Representation.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Representation.decodeStore view code out.2.2.1 = Representation.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) []
          ⟨⟨Representation.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_memory_store_execution_owned_uniform memory hooks floats allocator platform index view laws code exec store raw inst compiled ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound point expected machine program)
  rintro out ⟨platform,mutation,metadata,extension,success | trapped⟩
  · rcases success with ⟨success,pc,g,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨platform,mutation,metadata,extension,Or.inl ⟨success,pc,g,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨platform,mutation,metadata,extension,Or.inr trapped⟩

end Itasca.Interp.Machine.Memory

end

end

/-! ## Normalization -/

section

/-!
A retained forward administrative instruction must execute before the source operation at its target can be normalized.

Main declarations: `ForwardSkip` and `NormalizedPoint`.
-/

namespace Itasca.Interp.Machine
open Aeneas.Std

/-- A retained forward administrative instruction must execute before the
source operation at its target can be normalized. -/
def ForwardSkip (s : store) (raw : runtime.interp.Frame) (f : SourceMachine.AFrame)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype) : Prop :=
  ∃ target, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
    FramePoint s { raw with pc := target } f compiled C targets next output

/-- A source-only transition retains the actual PC and live slot relation.
Its semantic preservation and finite chaining follow from ErasedStep. -/
def NormalizedPoint (s : store) (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (before : SourceMachine.AFrame) : Prop :=
  ∃ after targets next output,
    ErasedStep before after ∧ FrameSlots exec raw after ∧
    FramePoint s raw after compiled C targets next output

theorem structured_nop_normalizes (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (f : SourceMachine.AFrame) (after : List instr)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := .NOP :: after } compiled C targets next output) :
    ForwardSkip s raw { f with code := .NOP :: after } compiled C targets next output ∨
    NormalizedPoint s exec raw compiled C { f with code := .NOP :: after } := by
  rcases structured_code_linear_inv (by rfl) point.code.current with skip | linear
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched, point.bindings,point.locals,point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := linear
    obtain ⟨rfl, rfl⟩ := linear_emission_nop_inv (ErasedHeads.nop head)
    have endpoint : tail = raw.pc.val := by obtain ⟨_, _, _, _, h⟩ := fragment; simpa using h
    exact Or.inr ⟨{ f with code := after }, targets, next, output, .nop f after, slots,
      point.bindings,point.locals,point.labels, by simpa only [endpoint] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩

theorem structured_drop_normalizes (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (f : SourceMachine.AFrame) (after : List instr)
    (typed : SourceMachine.FrameTyped s { f with code := .DROP :: after } [])
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := .DROP :: after } compiled C targets next output) :
    ForwardSkip s raw { f with code := .DROP :: after } compiled C targets next output ∨
    NormalizedPoint s exec raw compiled C { f with code := .DROP :: after } := by
  rcases structured_code_linear_inv (by rfl) point.code.current with skip | linear
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched, point.bindings,point.locals,point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := linear
    obtain ⟨stack, ty, shape, middleEq, emittedEq⟩ := linear_emission_drop_inv (ErasedHeads.drop head)
    obtain ⟨front, value, split, frontTypes, valueType⟩ := values_type_suffix f.vals stack ty shape
    have endpoint : tail = raw.pc.val := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_nil, Nat.add_zero] using h
    have heights := frame_linear_heights typed (by rfl) front (by simp only [split, List.length_append, List.length_singleton, linearInputs])
    have labels : LabelsMatch (front ++ [value]) f.labels targets := by simpa only [← split] using point.labels
    have labelsAfter : LabelsMatch front f.labels targets := by
      simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
    have values : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
      simpa only [FrameSlots, split, List.append_assoc] using slots
    refine Or.inr ⟨{ f with code := after, vals := front }, targets, next, output,
      ?_, values.locals, point.bindings,point.locals,labelsAfter, ?_, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
    · simpa only [← split] using ErasedStep.drop f after front value
    · simpa only [middleEq, endpoint, frontTypes] using continuation

theorem structured_block_normalizes (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (bt : blocktype) (body after : List instr)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := .BLOCK bt body :: after } compiled C targets next output) :
    ForwardSkip s raw { f with code := .BLOCK bt body :: after } compiled C targets next output ∨
    NormalizedPoint s exec raw compiled C { f with code := .BLOCK bt body :: after } := by
  rcases code_rel_block_inv point.code.current with skip | block
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched, point.bindings,point.locals,point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨front, params, results, normalExit, branchExit, normalLive, branchLive, shape, signature, bodyCode, normal, branch, bounds⟩ := block
    have sourceSignature : Compiler.BlockSignature f.module.TYPES bt params results := by
      simpa only [point.bindings.types] using signature
    refine Or.inr ⟨_,⟨front,results,results,branchExit,normalExit,[],after,normalLive,branchLive⟩::targets,normalExit,front++results,.block f bt body after front params results sourceSignature shape,slots,?_⟩
    refine ⟨point.bindings,point.locals,point.labels.enter front params results results branchExit normalExit [] after shape,?_⟩
    simpa only [shape] using Compiler.StructuredCode.Point.block_body bodyCode normal branch
      point.code.targets point.code.normal point.code.exit point.code.root

theorem structured_label_normalizes (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (label : SourceMachine.Label) (labels : List SourceMachine.Label)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := [], labels := label :: labels } compiled C targets next output) :
    ForwardSkip s raw { f with code := [], labels := label :: labels } compiled C targets next output ∨
    NormalizedPoint s exec raw compiled C { f with code := [], labels := label :: labels } := by
  rcases structured_code_empty_inv point.code.current with skip | empty
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched, point.bindings,point.locals,point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨next', output', represented, continuation, _, _⟩ :=
      label_completion_point exec raw compiled C targets next output s ambient f rest label labels typed slots point empty.1 empty.2.2
    exact Or.inr ⟨_, _, next', output', .label f label labels, represented, continuation⟩

end Itasca.Interp.Machine

end

end
