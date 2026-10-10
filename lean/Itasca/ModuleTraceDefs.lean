import Itasca.ModuleFramingComplete
import Itasca.ModuleNames

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

/-- Custom callbacks retain their offsets within the component byte region. -/
inductive Event where
  | custom (chunk : types.CustomSection)

/-- Successful custom callbacks append the exact original argument. -/
def RecordsCustom {V : Type} (visitor : module.ModuleVisitor V) (observe : V → List Event) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') →
    observe v' = observe v ++ [.custom chunk]

/-- Exact independent framing of a reported custom section, including its
UTF-8 name and the payload interval immediately following that encoded name. -/
def CustomAt (data : Slice U8) (start finish : Usize) (chunk : types.CustomSection) : Prop :=
  ∃ first nm, ModuleBinary.SectionHeader data start 0#u8 first finish ∧
    ModuleBinary.At ModuleBinary.NameEncoding data first nm chunk.payload_start ∧
    chunk.payload_start.val ≤ finish.val ∧ chunk.payload_end = finish ∧ chunk.name_len.val = nm.length

theorem CustomAt.span {data start finish chunk} (h : CustomAt data start finish chunk) :
    start.val < finish.val ∧ finish.val ≤ data.length := by
  obtain ⟨first, _, hh, _, hp, he, _⟩ := h
  have := hh.span
  omega

/-- Every section interval is traversed exactly once. Allowed ordinary sections
emit no custom callback; each custom section emits its independently framed
argument. This relation mentions no extracted decoder or callback execution. -/
inductive SectionTrace (data : Slice U8) (allowed : U8 → Prop) :
    Usize → Usize → List Event → Prop where
  | done (pos : Usize) (hpos : pos.val ≤ data.length) : SectionTrace data allowed pos pos []
  | custom {start middle finish chunk events} : CustomAt data start middle chunk →
      SectionTrace data allowed middle finish events →
      SectionTrace data allowed start finish (.custom chunk :: events)
  | ordinary {start first middle finish id events} : allowed id → id ≠ 0#u8 →
      ModuleBinary.SectionHeader data start id first middle →
      SectionTrace data allowed middle finish events → SectionTrace data allowed start finish events

theorem SectionTrace.span {data allowed start finish events}
    (h : SectionTrace data allowed start finish events) :
    start.val ≤ finish.val ∧ finish.val ≤ data.length := by
  induction h with
  | done => exact ⟨le_rfl, ‹_›⟩
  | custom hc _ ih => have := hc.span; omega
  | ordinary _ _ hh _ ih => have := hh.span; omega

def EnvTrace (data : Slice U8) (finish : Usize) (events : List Event) : Prop :=
  ∃ start, Wasm.BytesAt data 0#usize ModuleBinary.magicVersion start ∧
    SectionTrace data (fun id => 1 ≤ id.val ∧ id.val < 10) start finish events

def TailTrace (data : Slice U8) (start : Usize) (events : List Event) : Prop :=
  SectionTrace data (fun id => id = 11#u8) start (Slice.len data) events

end Itasca.ModuleTrace
