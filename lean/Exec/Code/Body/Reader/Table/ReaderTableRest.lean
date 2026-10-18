import Exec.Code.Local.Relations.Table.BranchTableCallback
import Itasca.Wasm2.Visitor.BrTable
import Itasca.Binary.Leb128
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts Itasca.Wasm2.Visitor

 theorem table_rest_cont {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (env : module.Env) (count index depth : U32)
    (types : signature.ResultType) (arity : Option Usize) (before after : V)
    (next : code.OpIterState) (nextArity : Option Usize) (nextIndex : U32)
    (accepted : tableRest visitor st env count index depth types arity before =
      .ok (.cont (next,after,nextArity,nextIndex))) :
    next = st.core ∧ after = before ∧ index ≠ count ∧ nextIndex.val = index.val + 1 := by
  unfold tableRest at accepted
  obtain ⟨checked,_,rest⟩ := bind_ok_inv _ _ _ accepted
  cases checked with
  | Err error => simp at rest
  | Ok newArity =>
    by_cases final : index = count
    · simp only [final,ite_true] at rest
      obtain ⟨marked,_,rest⟩ := bind_ok_inv _ _ _ rest
      obtain ⟨⟨reply,result⟩,_,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply <;> simp [code.visit] at rest
    · simp only [final,ite_false] at rest
      obtain ⟨incremented,increment,rest⟩ := bind_ok_inv _ _ _ rest
      simp only [Result.ok.injEq,ControlFlow.cont.injEq,Prod.mk.injEq] at rest
      obtain ⟨rfl,rfl,rfl,rfl⟩ := rest
      have arithmetic := UScalar.add_equiv index 1#u32
      rw [increment] at arithmetic
      exact ⟨rfl,rfl,final,by simpa using arithmetic.2.1⟩

theorem table_rest_done {V : Type} (visitor : code.OpVisitor V)
    (st final : code.BodyState) (env : module.Env) (count index depth : U32)
    (types : signature.ResultType) (arity : Option Usize) (before after : V)
    (accepted : tableRest visitor st env count index depth types arity before =
      .ok (.done (.Ok (),final,after))) :
    index = count ∧
    code.mark_unreachable st.core = .ok final.core ∧
    visitor.on_br_table before final.core depth types = .ok (.Ok (),after) := by
  unfold tableRest at accepted
  obtain ⟨checked,_,rest⟩ := bind_ok_inv _ _ _ accepted
  cases checked with
  | Err error => simp at rest
  | Ok newArity =>
    by_cases isLast : index = count
    · simp only [isLast,ite_true] at rest
      obtain ⟨marked,markedCall,rest⟩ := bind_ok_inv _ _ _ rest
      obtain ⟨⟨reply,result⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp [code.visit] at rest
        rcases rest with ⟨stateEq,visitorEq⟩
        cases final
        simp only [code.BodyState.mk.injEq] at stateEq
        subst after
        cases stateEq
        exact ⟨isLast,markedCall,callback⟩
    · simp only [isLast,ite_false] at rest
      obtain ⟨_,_,rest⟩ := bind_ok_inv _ _ _ rest
      simp at rest
end Exec.Code
