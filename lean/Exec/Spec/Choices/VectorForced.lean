import Exec.Spec.Choices.VectorFirstChoice
namespace Exec.Spec

def vectorUnaryFloat : vunop_ → Bool
  | .mk_vunop__1 _ _ _ => true
  | _ => false

def vectorBinaryFloat : vbinop_ → Bool
  | .mk_vbinop__1 _ _ _ => true
  | _ => false

theorem vector_unary_nonfloat_singleton {shape : _root_.shape} {op : vunop_} {input : vec_} {results : List vec_}
    (source : fun_vunop_ shape op input (some results)) (integer : vectorUnaryFloat op = false) :
    ∃ result, results = [result] := by
  cases source
  all_goals try { simp [vectorUnaryFloat] at integer }
  all_goals exact ⟨_,rfl⟩

theorem vector_binary_nonfloat_singleton {shape : _root_.shape} {op : vbinop_} {left right : vec_} {results : List vec_}
    (source : fun_vbinop_ shape op left right (some results)) (integer : vectorBinaryFloat op = false) :
    ∃ result, results = [result] := by
  cases source
  all_goals try { simp [vectorBinaryFloat] at integer }
  all_goals exact ⟨_,rfl⟩

/-- Integer vector result lists are singletons, so their reply agrees with the
same source-only preference used for floating-point lane choices. -/
theorem first_vector_reply_nonfloat {request : VectorRequest} {reply : Option vec_}
    (source : VectorResultAllowed request reply)
    (integer : match request with
      | .unary _ op _ => vectorUnaryFloat op = false
      | .binary _ op _ _ => vectorBinaryFloat op = false
      | .convert _ _ _ _ => False) : FirstVectorReply request reply := by
  cases source with
  | unary relation member inputWf opWf resultWf =>
    obtain ⟨value,singleton⟩ := vector_unary_nonfloat_singleton relation integer
    simp only [singleton,List.mem_singleton] at member
    subst value
    exact ⟨_,relation,by simp only [singleton,List.head?_cons]⟩
  | unary_trap relation inputWf opWf =>
    obtain ⟨value,impossible⟩ := vector_unary_nonfloat_singleton relation integer
    cases impossible
  | binary relation member leftWf rightWf opWf resultWf =>
    obtain ⟨value,singleton⟩ := vector_binary_nonfloat_singleton relation integer
    simp only [singleton,List.mem_singleton] at member
    subst value
    exact ⟨_,relation,by simp only [singleton,List.head?_cons]⟩
  | binary_trap relation leftWf rightWf opWf =>
    obtain ⟨value,impossible⟩ := vector_binary_nonfloat_singleton relation integer
    cases impossible
  | convert => exact False.elim integer
end Exec.Spec
