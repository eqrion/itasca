import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Code.Local.Relations.Common.CoreFunction
import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Exec.Abs.Stateful

theorem Signature.context {C D op input output}
    (functions : D.FUNCS = C.FUNCS) (tables : D.TABLES = C.TABLES)
    (memories : D.MEMS = C.MEMS) (elements : D.ELEMS = C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]? = some datatype.OK → D.DATAS[index]? = some datatype.OK)
    (signature : Signature C op input output) : Signature D op input output := by
  cases signature with
  | refNull type => exact .refNull type
  | refFunc index type found => exact .refFunc index type (by simpa only [functions] using found)
  | refIsNull type => exact .refIsNull type
  | tableGet index type bounds found => exact .tableGet index type bounds (by simpa only [tables] using found)
  | tableSet index type bounds found => exact .tableSet index type bounds (by simpa only [tables] using found)
  | tableSize index type found => exact .tableSize index type (by simpa only [tables] using found)
  | tableGrow index type bounds found => exact .tableGrow index type bounds (by simpa only [tables] using found)
  | tableFill index type bounds found => exact .tableFill index type bounds (by simpa only [tables] using found)
  | tableCopy destination source type destinationBounds sourceBounds destinationFound sourceFound =>
    exact .tableCopy destination source type destinationBounds sourceBounds
      (by simpa only [tables] using destinationFound) (by simpa only [tables] using sourceFound)
  | tableInit table element type bounds tableFound elementFound =>
    exact .tableInit table element type bounds (by simpa only [tables] using tableFound)
      (by simpa only [elements] using elementFound)
  | elemDrop index type found => exact .elemDrop index type (by simpa only [elements] using found)
  | memorySize type found => exact .memorySize type (by simpa only [memories] using found)
  | memoryGrow type found => exact .memoryGrow type (by simpa only [memories] using found)
  | memoryFill type found => exact .memoryFill type (by simpa only [memories] using found)
  | memoryCopy type found => exact .memoryCopy type (by simpa only [memories] using found)
  | memoryInit index type found dataFound =>
    exact .memoryInit index type (by simpa only [memories] using found) (datas index dataFound)
  | dataDrop index found => exact .dataDrop index (datas index found)
end Exec.Abs.Stateful
