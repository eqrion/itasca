import Itasca.ModuleCodeComplete
import Itasca.ModuleNames

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

/-- Module callbacks retain their original offsets. Opcode callbacks inside an
entry have their separate, slice-relative `CodeEntry.AcceptedTrace` contract. -/
inductive Event where
  | custom (chunk : types.CustomSection)
  | needBytes (finish : Usize)
  | codeEntry (index start content finish : Usize)

/-- Successful custom callbacks append the exact original argument. -/
def RecordsCustom {V : Type} (visitor : module.ModuleVisitor V) (observe : V → List Event) : Prop :=
  ∀ v chunk v', visitor.on_custom_section v chunk = .ok (.Ok (), v') →
    observe v' = observe v ++ [.custom chunk]

/-- Readiness requests and successful entry handoffs are distinct observable
callbacks. Recording them does not assert that an entry was validated. -/
structure RecordsCode {V : Type} (visitor : module.CodeVisitor V) (observe : V → List Event) : Prop where
  need_bytes : ∀ v finish reply v', visitor.on_need_bytes v finish = .ok (reply, v') →
    observe v' = observe v ++ [.needBytes finish]
  entry : ∀ v data env index start content finish v',
    visitor.on_code_entry v data env index start content finish = .ok (.Ok (), v') →
    observe v' = observe v ++ [.codeEntry index start content finish]

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

/-- The two readiness requests preceding each handoff are fixed by the exact
size-prefix position and decoded frame end. Entries remain unvalidated here. -/
inductive CodeEntriesTrace (data : Slice U8) (count : Nat) :
    Usize → Usize → Usize → List Event → Prop where
  | done (index pos : Usize) : count ≤ index.val → pos.val ≤ data.length →
      CodeEntriesTrace data count index pos pos []
  | more {index nextIndex start content last finish need events} :
      index.val < count → nextIndex.val = index.val + 1 →
      need.val = start.val + limits.MAX_LEB_BYTES.val → ModuleCode.Extent data start content last →
      CodeEntriesTrace data count nextIndex last finish events →
      CodeEntriesTrace data count index start finish
        (.needBytes need :: .needBytes last :: .codeEntry index start content last :: events)

/-- Independent framing of the complete code callback stream. The initial
request includes the maximum section-header size; empty code still requests
that header. Absent and present code sections remain distinguished. -/
inductive CodeTrace (data : Slice U8) (count : Nat) : Usize → Usize → List Event → Prop where
  | absent {pos need} : count = 0 → ModuleCode.AbsentAt data pos →
      need.val = pos.val + 11 → CodeTrace data count pos pos [.needBytes need]
  | present {pos first entries last need size events} :
      need.val = pos.val + 11 → ModuleBinary.SectionHeader data pos 10#u8 first last →
      Leb128.Decoded data first size entries → size.val = count →
      CodeEntriesTrace data count 0#usize entries last events →
      CodeTrace data count pos last (.needBytes need :: events)

theorem CodeTrace.span {data count start finish events} (h : CodeTrace data count start finish events) :
    start.val ≤ finish.val ∧ finish.val ≤ data.length := by
  cases h with
  | absent _ hs _ =>
    rcases hs with h | ⟨_, _, _, hh, _⟩
    · exact ⟨le_rfl, h.le⟩
    · have := hh.span; omega
  | present _ hh _ _ _ => have := hh.span; omega

end Itasca.ModuleTrace
