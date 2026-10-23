import Exec.Interp.StructuredMachine.GlobalPoint
import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.State.GlobalCoreOperands

namespace Exec.Interp.StructuredMachine.Global
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
open Aeneas Aeneas.Std SpecExt

theorem coreFramePoint_globalGet_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (index : Nat)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint emission (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) ∨
    (∃ idx dst address object, index = idx.val ∧
      inst.globals.val[index]? = some address ∧ store.globals.val[address.index.val]? = some object ∧
      dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Code.globalGetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) dst idx) ∧
      Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (f.vals.map Code.valueType ++ [sourceType object.ty.valtype]) after (raw.pc.val+1) next output) := by
  rcases corePoint_globalGet_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨mutability,ty,idx,dst,indexEq,lookup,position,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨address,object,mapped,issued,mutEq,typeEq⟩ := coreGlobal_lookup view code store inst f C index mutability ty moduleEq point.bindings lookup
    refine Or.inr ⟨idx,dst,address,object,indexEq,mapped,issued,?_,?_,?_⟩
    · simpa only [point.locals,List.map_append,Code.slots_append] using position
    · simpa only [typeEq] using fetch
    · simpa only [typeEq] using tail

theorem coreFramePoint_globalSet_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (index : Nat)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [])
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint emission (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) ∨
    (∃ front value idx src address object, index = idx.val ∧ f.vals = front ++ [value] ∧ wf_val value ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      inst.globals.val[index]? = some address ∧ store.globals.val[address.index.val]? = some object ∧
      object.ty.mutability = .Var ∧ sourceType object.ty.valtype = Code.valueType value ∧
      src.val = Code.slots ((f.locals ++ front).map Code.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src idx) ∧
      Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Code.valueType) after (raw.pc.val+1) next output) := by
  rcases corePoint_globalSet_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,ty,idx,src,indexEq,input,lookup,position,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨address,object,mapped,issued,mutEq,typeEq⟩ := coreGlobal_lookup view code store inst f C index (some .MUT) ty moduleEq point.bindings lookup
    obtain ⟨front,value,values,valueWf,heights⟩ := global_set_typed_operand f after index typed
    have shape := input
    simp only [values,List.map_append,List.map_cons,List.map_nil] at shape
    have lengthEq : (front.map Code.valueType).length = types.length := by
      have lengths := congrArg List.length shape
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨typesEq,valueEq⟩ := List.append_inj shape lengthEq
    have valueType : Code.valueType value = ty := by simpa using valueEq
    have mutable : object.ty.mutability = .Var := by
      cases eq : object.ty.mutability <;> simp_all [Store.decodeMut]
    refine Or.inr ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,typeEq.trans valueType.symm,?_,?_,?_⟩
    · simpa only [point.locals,List.map_append,Code.slots_append,typesEq] using position
    · simpa only [typeEq] using fetch
    · simpa only [typesEq] using tail
end Exec.Interp.StructuredMachine.Global
