import Exec.Interp.Core.LocalPrefix
import Exec.Interp.FloatCore.LocalInversion
import Exec.Interp.Relations.PrefixDispatch
import Exec.Interp.Relations.LocalCodePoint
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem float_core_localGet_fetch {s raw compiled C targets next output} {f : Abs.AFrame}
    (index : Nat) (after : List instr)
    (point : FloatFramePoint s raw {f with code := .LOCAL_GET (.mk_uN index)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases structuredCode_linear_inv (by rfl) point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,continuation⟩
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨ty,src,dst,localType,emittedEq,middleEq,source,position⟩ := linearEmission_localGet_inv index (floatCoreEmission_localGet_pure index head)
    refine ⟨Code.move ty dst src,?_,move_prefix ty dst src⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

theorem float_core_localWrite_fetch {s raw compiled C targets next output} {f : Abs.AFrame}
    (index : Nat) (keep : Bool) (after : List instr)
    (point : FloatFramePoint s raw {f with code := (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index))::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  have linear : linearSource (if keep then .LOCAL_TEE (.mk_uN index) else .LOCAL_SET (.mk_uN index)) = true := by cases keep <;> rfl
  rcases structuredCode_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,continuation⟩
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨stack,ty,dst,src,shape,localType,emittedEq,middleEq,destination,source⟩ := linearEmission_localWrite_inv index keep (floatCoreEmission_localWrite_pure index keep head)
    refine ⟨Code.move ty dst src,?_,move_prefix ty dst src⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])
end Exec.Interp
