import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservation
import Itasca.Runtime.Compiler.Local.Relations.Layout.ObservationLayout
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std


theorem compiler_enter_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_enter_observation ops before after state kind bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed


theorem compiler_end_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_end_observation ops before after state kind bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed


theorem compiler_else_layout_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (known : ConcreteStack state.vals.val) (locals : LocalLayout after)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    CompilerLayout after (Itasca.Sequence.stackTypes state.vals.val) := by
  obtain ⟨middle, observed⟩ := compiler_else_observation ops before after state bt accepted
  exact compiler_observe_layout_success ops law middle after state known locals observed

end Itasca.Runtime.Code
