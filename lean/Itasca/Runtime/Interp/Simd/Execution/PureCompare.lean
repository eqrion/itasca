import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Integer.Compare
import Itasca.Runtime.Interp.Simd.Float.Compare

/-!
Source correspondence of pure comparison opcode entries.

Main declarations: `pure_entry_35` and `pure_entry_219`. A direct consumer is `Interp.Simd.Execution.PureSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_35 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 35#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure35 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 .EQ offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_36 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 36#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure36 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 .NE offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_37 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 37#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure37 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.LT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_38 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 38#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure38 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.LT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_39 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 39#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure39 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.GT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_40 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 40#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure40 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.GT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_41 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 41#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure41 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.LE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_42 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 42#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure42 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.LE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_43 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 43#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure43 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.GE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_44 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 44#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure44 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.GE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_45 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 45#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure45 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 .EQ offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_46 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 46#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure46 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 .NE offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_47 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 47#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure47 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.LT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_48 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 48#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure48 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.LT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_49 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 49#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure49 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.GT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_50 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 50#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure50 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.GT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_51 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 51#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure51 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.LE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_52 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 52#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure52 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.LE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_53 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 53#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure53 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.GE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_54 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 54#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure54 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.GE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_55 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 55#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure55 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 .EQ offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_56 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 56#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure56 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 .NE offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_57 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 57#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure57 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.LT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_58 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 58#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure58 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.LT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_59 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 59#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure59 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.GT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_60 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 60#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure60 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.GT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_61 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 61#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure61 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.LE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_62 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 62#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure62 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.LE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_63 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 63#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure63 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.GE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_64 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 64#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure64 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.GE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_65 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 65#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure65 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .EQ offset laneIndex bits x y z memory

theorem pure_entry_66 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 66#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure66 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .NE offset laneIndex bits x y z memory

theorem pure_entry_67 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 67#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure67 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .LT offset laneIndex bits x y z memory

theorem pure_entry_68 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 68#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure68 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .GT offset laneIndex bits x y z memory

theorem pure_entry_69 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 69#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure69 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .LE offset laneIndex bits x y z memory

theorem pure_entry_70 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 70#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure70 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .GE offset laneIndex bits x y z memory

theorem pure_entry_71 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 71#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure71 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .EQ offset laneIndex bits x y z memory

theorem pure_entry_72 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 72#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure72 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .NE offset laneIndex bits x y z memory

theorem pure_entry_73 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 73#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure73 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .LT offset laneIndex bits x y z memory

theorem pure_entry_74 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 74#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure74 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .GT offset laneIndex bits x y z memory

theorem pure_entry_75 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 75#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure75 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .LE offset laneIndex bits x y z memory

theorem pure_entry_76 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 76#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure76 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .GE offset laneIndex bits x y z memory

theorem pure_entry_214 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 214#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure214 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 .EQ offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_215 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 215#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure215 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 .NE offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_216 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 216#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure216 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 (.LT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_217 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 217#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure217 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 (.GT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_218 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 218#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure218 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 (.LE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_219 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 219#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure219 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 (.GE .S) offset laneIndex bits x y z memory (by trivial)

end Itasca.Runtime.Interp.Simd
