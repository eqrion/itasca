import Itasca.Runtime.Interp.StructuredMachine.Heads
import Itasca.Runtime.Interp.StructuredMachine.IndexedLinear
namespace Itasca.Runtime.Interp.StructuredMachine
variable {emission : ContextEmission} [OrdinaryHeads emission]

theorem emission_not_block {C before after emitted bt body}
    (head : emission C before (.BLOCK bt body) emitted after) : False := by
  have h := OrdinaryHeads.ordinary head
  cases h

theorem emission_not_loop {C before after emitted bt body}
    (head : emission C before (.LOOP bt body) emitted after) : False := by
  have h := OrdinaryHeads.ordinary head
  cases h

theorem emission_not_if {C before after emitted bt yes no}
    (head : emission C before (.IFELSE bt yes no) emitted after) : False := by
  have h := OrdinaryHeads.ordinary head
  cases h

theorem emission_not_br {C before after emitted depth}
    (head : emission C before (.BR (.mk_uN depth)) emitted after) : False := by
  have h := OrdinaryHeads.ordinary head
  cases h

theorem emission_not_br_if {C before after emitted depth}
    (head : emission C before (.BR_IF (.mk_uN depth)) emitted after) : False := by
  have h := OrdinaryHeads.ordinary head
  cases h

theorem emission_not_call {C before after emitted index}
    (head : emission C before (.CALL (.mk_uN index)) emitted after) : False := by
  have h := OrdinaryHeads.ordinary head
  cases h

theorem emission_not_return {C before after emitted}
    (head : emission C before .RETURN emitted after) : False := by
  have h := OrdinaryHeads.ordinary head
  cases h
end Itasca.Runtime.Interp.StructuredMachine
