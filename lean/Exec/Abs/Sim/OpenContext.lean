import Exec.Spec.Open.Host
import Exec.Abs.Sim.Context
import Exec.Abs.HostCallSite
import Exec.Abs.Indirect.HostTyping
import Exec.Spec.IndirectCallSource
namespace Exec.Abs.OpenContext
open SpecExt Exec.Spec Exec.Spec.OpenHost

def compose : Context → Context → Context
  | .hole,inner => inner
  | .label arity cont wf tail,inner => .label arity cont wf (compose tail inner)
  | .frame arity outer wf tail,inner => .frame arity outer wf (compose tail inner)
  | .instructions values after hv ha tail,inner => .instructions values after hv ha (compose tail inner)

theorem compose_plug (outer inner : Context) (configuration : config) :
    (compose outer inner).plug configuration=outer.plug (inner.plug configuration) := by
  induction outer with
  | hole => rfl
  | label arity cont wf tail ih => simp only [compose,Context.plug,ih]
  | frame arity outer wf tail ih => simp only [compose,Context.plug,ih]
  | instructions values after hv ha tail ih => simp only [compose,Context.plug,ih]

def labels : (stack : List Label) → (values : List val) → LabelsWf stack → Forall wf_val values → Context
  | [],values,_,hv => .instructions values [] hv (by simp [Forall]) .hole
  | label::rest,values,hl,hv =>
    compose (labels rest (values.take label.height) (fun item member=>hl item (by simp [member]))
      (fun value member=>hv value (List.mem_of_mem_take member)))
      (.instructions [] (label.after.map admininstr_instr) (by simp [Forall]) (wf_instrs (hl label (by simp)).2)
        (.label label.arity label.cont (hl label (by simp)).1
          (.instructions (values.drop label.height) [] (fun value member=>hv value (List.mem_of_mem_drop member)) (by simp [Forall]) .hole)))

theorem labels_plug (stack : List Label) (values : List val) (hl : LabelsWf stack) (hv : Forall wf_val values)
    (z : state) (body : List admininstr) : (labels stack values hl hv).plug ⟨z,body⟩=⟨z,decodeLabels stack values body⟩ := by
  induction stack generalizing values body with
  | nil => simp [labels,Context.plug,instrContext,decodeLabels]
  | cons label rest ih =>
    simp only [labels,compose_plug,Context.plug,instrContext,Exec.Spec.labelContext,vals,List.map_nil,List.nil_append,List.append_nil]
    rw [ih]
    rfl

def frames (ambient : frame) (ha : wf_frame ambient) : (stack : List AFrame) → Forall FrameWf stack → Context
  | [],_ => .hole
  | f::rest,hf =>
    compose (frames ambient ha rest (fun item member=>hf item (by simp [member])))
      (.frame f.arity (activeFrame ambient rest) (activeFrame_wf ha (fun item member=>hf item (by simp [member])))
        (compose (labels f.labels f.vals (hf f (by simp)).2.1 (hf f (by simp)).2.2.1)
          (.instructions [] (f.code.map admininstr_instr) (by simp [Forall]) (wf_instrs (hf f (by simp)).2.2.2) .hole)))

theorem frames_plug (ambient : frame) (ha : wf_frame ambient) (stack : List AFrame) (hf : Forall FrameWf stack)
    (s : store) (body : List admininstr) :
    (frames ambient ha stack hf).plug ⟨⟨s,activeFrame ambient stack⟩,body⟩=⟨⟨s,ambient⟩,decodeFrames stack body⟩ := by
  induction stack generalizing body with
  | nil => rfl
  | cons f rest ih =>
    simp only [frames,compose_plug,Context.plug,instrContext,vals,List.map_nil,List.nil_append]
    rw [labels_plug]
    simp only [frameContext]
    change (frames ambient ha rest _).plug ⟨⟨s,activeFrame ambient rest⟩,
      [.FRAME_ f.arity f.toFrame (decodeLabels f.labels f.vals (body++f.code.map admininstr_instr))]⟩ = _
    rw [ih]
    rfl

def active (ambient : frame) (ha : wf_frame ambient) (rest : List AFrame) (hr : Forall FrameWf rest) (arity : Nat) : Context :=
  compose (frames ambient ha rest hr) (.frame arity (activeFrame ambient rest) (activeFrame_wf ha hr) .hole)

theorem active_plug (ambient : frame) (ha : wf_frame ambient) (rest : List AFrame) (hr : Forall FrameWf rest)
    (arity : Nat) (s : store) (inner : frame) (body : List admininstr) :
    (active ambient ha rest hr arity).plug ⟨⟨s,inner⟩,body⟩=⟨⟨s,ambient⟩,decodeFrames rest [.FRAME_ arity inner body]⟩ := by
  simp only [active,compose_plug,Context.plug,frameContext]
  exact frames_plug ambient ha rest hr s _

/-- The exact evaluation context surrounding a host redex in a flat source
frame stack, with its operand prefix and remaining instructions retained. -/
def host (ambient : frame) (ha : wf_frame ambient) (f : AFrame) (rest : List AFrame) (hr : Forall FrameWf rest)
    (after : List instr) (hc : Forall wf_instr after) (front : List val) (hv : Forall wf_val front)
    (hl : LabelsWf f.labels) : Context :=
  compose (active ambient ha rest hr f.arity)
    (compose (labels f.labels front hl hv) (.instructions [] (after.map admininstr_instr) (by simp [Forall]) (wf_instrs hc) .hole))

theorem host_plug (ambient : frame) (ha : wf_frame ambient) (f : AFrame) (rest : List AFrame) (hr : Forall FrameWf rest)
    (after : List instr) (hc : Forall wf_instr after) (front : List val) (hv : Forall wf_val front)
    (hl : LabelsWf f.labels) (s : store) (body : List admininstr) :
    (host ambient ha f rest hr after hc front hv hl).plug ⟨⟨s,f.toFrame⟩,body⟩=
      ⟨⟨s,ambient⟩,decodeFrames rest [.FRAME_ f.arity f.toFrame (decodeLabels f.labels front (body++after.map admininstr_instr))]⟩ := by
  simp only [host,compose_plug,Context.plug,instrContext,vals,List.map_nil,List.nil_append]
  rw [labels_plug,active_plug]

end Exec.Abs.OpenContext
