import Exec.Abs.Stateful.Descriptor

namespace Exec.Abs.Stateful

/-- Canonical source index spaces determine the operand/result types. -/
inductive Signature (C : context) : Instruction → List valtype → List valtype → Prop where
  | refNull (type) : Signature C (.refNull type) [] [valtype_reftype type]
  | refFunc (index) (type : functype) (found : C.FUNCS[index]? = some type) :
      Signature C (.refFunc index) [] [.FUNCREF]
  | refIsNull (type) : Signature C .refIsNull [valtype_reftype type] [.I32]
  | tableGet (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableGet index) [.I32] [valtype_reftype type]
  | tableSet (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableSet index) [.I32, valtype_reftype type] []
  | tableSize (index) (type : tabletype) (found : C.TABLES[index]? = some type) :
      Signature C (.tableSize index) [] [.I32]
  | tableGrow (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableGrow index) [valtype_reftype type, .I32] [.I32]
  | tableFill (index) (type) (bounds) (found : C.TABLES[index]? = some (.mk_tabletype bounds type)) :
      Signature C (.tableFill index) [.I32, valtype_reftype type, .I32] []
  | tableCopy (destination source) (type) (destinationBounds sourceBounds)
      (destinationFound : C.TABLES[destination]? = some (.mk_tabletype destinationBounds type))
      (sourceFound : C.TABLES[source]? = some (.mk_tabletype sourceBounds type)) :
      Signature C (.tableCopy destination source) [.I32, .I32, .I32] []
  | tableInit (table element) (type) (bounds)
      (tableFound : C.TABLES[table]? = some (.mk_tabletype bounds type))
      (elementFound : C.ELEMS[element]? = some type) :
      Signature C (.tableInit table element) [.I32, .I32, .I32] []
  | elemDrop (index) (type : reftype) (found : C.ELEMS[index]? = some type) :
      Signature C (.elemDrop index) [] []
  | memorySize (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memorySize [] [.I32]
  | memoryGrow (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryGrow [.I32] [.I32]
  | memoryFill (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryFill [.I32, .I32, .I32] []
  | memoryCopy (type : memtype) (found : C.MEMS[0]? = some type) :
      Signature C .memoryCopy [.I32, .I32, .I32] []
  | memoryInit (index) (type : memtype) (found : C.MEMS[0]? = some type)
      (dataFound : C.DATAS[index]? = some .OK) :
      Signature C (.memoryInit index) [.I32, .I32, .I32] []
  | dataDrop (index) (found : C.DATAS[index]? = some .OK) :
      Signature C (.dataDrop index) [] []

theorem Signature.input_length {C op input output} (signature : Signature C op input output) :
    input.length = op.arity := by
  cases signature <;> rfl

private theorem reference_scalar (type : reftype) : valtype_reftype type ≠ valtype.V128 := by
  cases type <;> decide

theorem Signature.inputs_scalar {C op input output} (signature : Signature C op input output) :
    ∀ type ∈ input, type ≠ valtype.V128 := by
  cases signature <;> simp_all [reference_scalar]

end Exec.Abs.Stateful
