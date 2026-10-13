import Itasca.Wasm1.ProfileSyntax

namespace Itasca.Wasm1

/-- The version profile observes label signatures only. In particular its
meaning is independent of the Rust environment and of later module segments. -/
theorem Instructions.congr_labels {C : context} {ops : List instr}
    (h : Instructions C ops) : ∀ D, C.LABELS = D.LABELS → Instructions D ops := by
  induction h using Instructions.rec
    (motive_1 := fun C op _ => ∀ D, C.LABELS = D.LABELS → Instruction D op)
  case leaf C op hp D he =>
    apply Instruction.leaf
    cases op <;> simp_all [Leaf, SameTargets]
  case block C bt body hb ih D he =>
    apply Instruction.block
    apply ih
    simp [Control.labelContext_labels, he]
  case loop C bt body hb ih D he =>
    apply Instruction.loop
    apply ih
    simp [Control.labelContext_labels, he]
  case ifElse C bt yes no hy hn ihy ihn D he =>
    apply Instruction.ifElse
    · apply ihy; simp [Control.labelContext_labels, he]
    · apply ihn; simp [Control.labelContext_labels, he]
  case nil C => intro D _; exact .nil D
  case cons C op ops hop hops ih ihs =>
    intro D he
    exact .cons (ih D he) (ihs D he)

theorem Instruction.congr_labels {C D : context} {op : instr}
    (h : Instruction C op) (he : C.LABELS = D.LABELS) : Instruction D op :=
  Instructions.singleton_iff.mp ((Instructions.singleton_iff.mpr h).congr_labels D he)

end Itasca.Wasm1
