import Exec.Interp.Simd.Common.SimdPureRelation
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticSound
import Exec.Interp.Simd.Integer.SimdIntegerSaturatingSound
import Exec.Interp.Simd.Integer.SimdIntegerMinMaxSound
import Exec.Interp.Simd.Common.SimdAverageSound
import Exec.Interp.Simd.Integer.SimdQ15Sound
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_110 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 110#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure110 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I8 .add offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_111 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 111#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure111 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I8 .addS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_112 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 112#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure112 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I8 .addU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_113 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 113#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure113 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I8 .sub offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_114 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 114#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure114 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I8 .subS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_115 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 115#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure115 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I8 .subU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_118 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 118#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure118 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I8 .minS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_119 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 119#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure119 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I8 .minU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_120 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 120#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure120 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I8 .maxS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_121 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 121#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure121 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I8 .maxU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_123 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 123#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure123 = some op at meaning
  cases meaning
  with_unfolding_all exact average_simd_sound floats .I8 offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_130 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 130#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure130 = some op at meaning
  cases meaning
  with_unfolding_all exact q15_simd_sound floats  offset laneIndex bits x y z memory

theorem pure_entry_142 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 142#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure142 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I16 .add offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_143 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 143#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure143 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I16 .addS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_144 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 144#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure144 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I16 .addU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_145 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 145#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure145 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I16 .sub offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_146 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 146#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure146 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I16 .subS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_147 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 147#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure147 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_saturating_simd_sound floats .I16 .subU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_149 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 149#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure149 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I16 .mul offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_150 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 150#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure150 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I16 .minS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_151 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 151#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure151 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I16 .minU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_152 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 152#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure152 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I16 .maxS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_153 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 153#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure153 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I16 .maxU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_155 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 155#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure155 = some op at meaning
  cases meaning
  with_unfolding_all exact average_simd_sound floats .I16 offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_174 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 174#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure174 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I32 .add offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_177 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 177#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure177 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I32 .sub offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_181 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 181#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure181 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I32 .mul offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_182 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 182#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure182 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I32 .minS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_183 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 183#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure183 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I32 .minU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_184 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 184#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure184 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I32 .maxS offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_185 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 185#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure185 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_minmax_simd_sound floats .I32 .maxU offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_206 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 206#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure206 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I64 .add offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_209 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 209#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure209 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I64 .sub offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_213 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 213#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure213 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_arithmetic_simd_sound floats .I64 .mul offset laneIndex bits x y z memory (by trivial)

end Itasca.Runtime.Interp.Simd
