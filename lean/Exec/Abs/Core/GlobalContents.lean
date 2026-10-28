import Exec.Abs.Core.GlobalMutation
import Exec.Abs.Core.ContentExtension

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem StoreContentsTyped.global_write {s : store} (contents : StoreContentsTyped s)
    (wf : wf_store s) (f : frame) (index address : Nat) (object : globalinst) (value : val) (ty : valtype)
    (mapped : f.MODULE.GLOBALS[index]? = some address) (found : s.GLOBALS[address]? = some object)
    (mutable : object.TYPE = .mk_globaltype (some .MUT) ty) (valueTyped : Val_ok s value ty) :
    StoreContentsTyped (Spec.globalWrite s f index value) := by
  have extension := globalWrite_extends s f index address object value ty wf contents mapped found mutable valueTyped
  have valueFresh := val_typed_extend extension valueTyped
  have freshWf := (extend_store_wf extension).2
  have objectFresh : Globalinst_ok (Spec.globalWrite s f index value)
      {object with VALUE := value} {object with VALUE := value}.TYPE := by
    cases object with
    | MKglobalinst type old =>
      dsimp only at mutable
      cases mutable
      exact .mk_Globalinst_ok _ _ _ _ (.mk_Globaltype_ok _ _) valueFresh freshWf
        (.globalinst_case_ _ _ (val_ok_wf valueFresh))
  exact contents.global_replacement extension address {object with VALUE := value}
    (congrArg store.GLOBALS (globalWrite_as_set s f index address object value mapped found))
    rfl rfl rfl rfl objectFresh

end Itasca.Runtime.Abs
