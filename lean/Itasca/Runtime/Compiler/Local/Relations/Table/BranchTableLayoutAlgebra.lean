import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableLayout
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Extension
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Concatenation
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem BranchTableEntry.extend {locals labels stack code depth entry next}
    (fragment : BranchTableEntry locals labels stack code depth entry next) (suffix : List Bytecode) :
    BranchTableEntry locals labels stack (code ++ suffix) depth entry next := by
  obtain ⟨label,dst,src,count,last,foundAt,live,layout,segment,remaining,scope⟩ := fragment
  exact ⟨label,dst,src,count,last,foundAt,live,layout,segment.extend suffix,remaining,by simp; omega⟩

theorem BranchTableEntry.relabel {locals labels stack code depth entry next other}
    (fragment : BranchTableEntry locals labels stack code depth entry next) (shape : LabelsShape labels other) :
    BranchTableEntry locals other stack code depth entry next := by
  obtain ⟨label,dst,src,count,last,foundAt,live,layout,segment,remaining,scope⟩ := fragment
  obtain ⟨target,found,same⟩ := shape.lookup foundAt
  refine ⟨target,dst,src,count,last,found,same.branchLive.symm.trans live,?_,?_,remaining,scope⟩
  · simpa only [BranchLayout,← same.front,← same.branchTypes] using layout
  · simpa only [← same.target] using segment

theorem BranchTableEntry.weaken_next {locals labels stack code depth entry next final}
    (fragment : BranchTableEntry locals labels stack code depth entry next)
    (order : next ≤ final) (bound : final ≤ code.length) :
    BranchTableEntry locals labels stack code depth entry final := by
  obtain ⟨label,dst,src,count,last,foundAt,live,layout,segment,remaining,scope⟩ := fragment
  exact ⟨label,dst,src,count,last,foundAt,live,layout,segment,remaining.trans order,bound⟩

theorem BranchTableLayout.extend {tables locals labels stack code depths fallback pc next selector start len}
    (table : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    (suffix : List Bytecode) :
    BranchTableLayout tables locals labels stack (code ++ suffix) depths fallback pc next selector start len := by
  refine ⟨table.selectorSlot,table.length,fetch_extend table.instruction suffix,table.arithmetic,?_⟩
  intro index depth found
  obtain ⟨entry,lookup,fragment⟩ := table.entries index depth found
  exact ⟨entry,lookup,fragment.extend suffix⟩

theorem BranchTableLayout.relabel {tables locals labels stack code depths fallback pc next selector start len other}
    (table : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    (shape : LabelsShape labels other) :
    BranchTableLayout tables locals other stack code depths fallback pc next selector start len := by
  refine ⟨table.selectorSlot,table.length,table.instruction,table.arithmetic,?_⟩
  intro index depth found
  obtain ⟨entry,lookup,fragment⟩ := table.entries index depth found
  exact ⟨entry,lookup,fragment.relabel shape⟩

theorem BranchTableLayout.weaken_next {tables locals labels stack code depths fallback pc next selector start len final}
    (table : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    (order : next ≤ final) (bound : final ≤ code.length) :
    BranchTableLayout tables locals labels stack code depths fallback pc final selector start len := by
  refine ⟨table.selectorSlot,table.length,table.instruction,table.arithmetic,?_⟩
  intro index depth found
  obtain ⟨entry,lookup,fragment⟩ := table.entries index depth found
  exact ⟨entry,lookup,fragment.weaken_next order bound⟩

theorem BranchTableLayout.append_tables {tables locals labels stack code depths fallback pc next selector start len}
    (table : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    (suffix : List U32) :
    BranchTableLayout (tables ++ suffix) locals labels stack code depths fallback pc next selector start len := by
  refine ⟨table.selectorSlot,table.length,table.instruction,table.arithmetic,?_⟩
  intro index depth found
  obtain ⟨entry,lookup,fragment⟩ := table.entries index depth found
  exact ⟨entry,by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).1]; exact lookup,fragment⟩
end Itasca.Runtime.Code
