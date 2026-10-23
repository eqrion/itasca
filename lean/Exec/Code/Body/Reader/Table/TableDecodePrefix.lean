import Exec.Code.Body.Reader.Table.ReaderTableSafetyWasm2
import Itasca.Binary.Wasm1.EncodingUnique

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Independently decoded table labels remaining at a reader boundary. The
scratch labels are an exact prefix of the source list, indexed by callbacks. -/
structure TableDecodePrefix (data : Slice U8) (all : List U32) (finish : Usize)
    (index : Nat) (state : code.OpIterState) (depths : List U32) : Prop where
  length : depths.length = index
  suffix : ∃ tail, all = depths ++ tail ∧ BrTable.LabelsDecoded data state.pos tail finish

/-- A label has been read but its callback has not yet appended it. Keeping
its value in the relation prevents arbitrary event arguments from replacing
source-decoded targets. -/
structure TableDecodeRead (data : Slice U8) (all : List U32) (finish : Usize)
    (index : Nat) (state : code.OpIterState) (depths : List U32) (depth : U32) : Prop where
  length : depths.length = index
  suffix : ∃ tail, all = depths ++ depth :: tail ∧ BrTable.LabelsDecoded data state.pos tail finish

/-- Each independently decoded label consumes at least one source byte. -/
theorem table_labels_length_span {data start depths finish}
    (decoded : BrTable.LabelsDecoded data start depths finish) :
    start.val + depths.length ≤ finish.val := by
  induction decoded with
  | nil => simp
  | snoc prior label ih =>
    have span := label.span
    simp only [List.length_append,List.length_singleton]
    omega

theorem TableDecodePrefix.initial {data all finish} (state : code.OpIterState)
    (decoded : BrTable.LabelsDecoded data state.pos all finish) :
    TableDecodePrefix data all finish 0 state [] := by
  exact ⟨rfl,all,by simp,decoded⟩

/-- The actual successful reader fixes both the next target and byte cursor
by uniqueness of independent unsigned LEB128 decoding. -/
theorem TableDecodePrefix.read {data all finish index depths depth ts out} {state : code.BodyState}
    (held : TableDecodePrefix data all finish index state.core depths)
    (remaining : index < all.length)
    (read : code.read_label_info state data = .ok (.Ok (depth,ts),out)) :
    TableDecodeRead data all finish index out.core depths depth := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  cases tail with
  | nil =>
    have length := congrArg List.length whole
    simp only [List.length_append,List.length_nil,Nat.add_zero] at length
    have prefixLength := held.length
    omega
  | cons first tail =>
    obtain ⟨middle,head,rest⟩ := BrTable.LabelsDecoded.cons_iff.mp decoded
    have actual := reader_table_label_wasm2 state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨_,_,bytes,_⟩ := actual depth ts rfl
    dsimp only at bytes
    obtain ⟨rfl,position⟩ := bytes.unique head
    exact ⟨held.length,tail,whole,by simpa only [position] using rest⟩

/-- The successful callback appends exactly the depth just read. -/
theorem TableDecodeRead.collect {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth) :
    TableDecodePrefix data all finish (index+1) state (depths++[depth]) := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  refine ⟨by simp [held.length],tail,?_,decoded⟩
  simpa [List.append_assoc] using whole

/-- At the separately decoded fallback, all remaining targets have been
accounted for. The vector labels followed by this fallback are exactly the
independent source target list. -/
theorem TableDecodeRead.complete {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth)
    (count : all.length = index+1) : all = depths++[depth] := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  have length := congrArg List.length whole
  simp only [List.length_append,List.length_cons] at length
  have prefixLength := held.length
  have empty : tail.length = 0 := by omega
  simpa only [List.length_eq_zero_iff.mp empty] using whole

/-- After reading the separately encoded fallback, the cursor is the source
end of the entire table immediate. -/
theorem TableDecodeRead.cursor {data all finish index state depths depth}
    (held : TableDecodeRead data all finish index state depths depth)
    (count : all.length = index+1) : state.pos = finish := by
  obtain ⟨tail,whole,decoded⟩ := held.suffix
  have length := congrArg List.length whole
  simp only [List.length_append,List.length_cons] at length
  have prefixLength := held.length
  have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
  subst tail
  exact (decoded.unique .nil rfl).2.symm

end Exec.Code
