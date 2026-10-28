import Itasca.Runtime.Abs.ReferenceBounds
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.Representation.Values
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A retained source reference bound discharges the concrete result decoder's
usize conversion, including its nonzero reference sentinel. -/
theorem resultIndexFits_of_reference_bound (value : val)
    (bounded : Abs.ReferenceBound Usize.max value) : ResultIndexFits value := by
  cases value <;> simp_all [Abs.ReferenceBound, ResultIndexFits] <;> omega

end Itasca.Runtime.Interp
