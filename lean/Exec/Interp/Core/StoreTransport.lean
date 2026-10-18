import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Abs.Core.PureCoverage
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem FrameStoreMetadata.decodeFunctions {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) (view : M → Slice U8) (code : Store.CodeInterpretation) :
    (Store.decodeStore view code after).FUNCS = (Store.decodeStore view code before).FUNCS := by
  have functionEq : Store.decodeFunction code after = Store.decodeFunction code before := by
    funext function
    simp only [Store.decodeFunction,Store.decodeInstance,metadata.types,metadata.instances]
  simp only [Store.decodeStore,metadata.functions,functionEq]

end Exec.Interp
namespace Exec.Abs

theorem CoreState.instruction_tail {s nextStore : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {op : instr} {after : List instr}
    (covered : CoreState ⟨s,ambient,{f with code := op::after}::rest,[]⟩)
    (functions : nextStore.FUNCS = s.FUNCS) (locals values : List val) :
    CoreState ⟨nextStore,ambient,{f with code := after,locals := locals,vals := values}::rest,[]⟩ := by
  have frame := covered.active _ (List.mem_cons_self ..)
  have old : CoreState ⟨s,ambient,{f with code := after,locals := locals,vals := values}::rest,[]⟩ :=
    core_replace_frame covered ⟨fun instruction member => frame.1 instruction (List.mem_cons_of_mem _ member),frame.2⟩
  exact old.store_same functions

end Exec.Abs
