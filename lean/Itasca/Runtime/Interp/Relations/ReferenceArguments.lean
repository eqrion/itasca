import Itasca.Runtime.SourceMachine.ReferenceBounds
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.Representation.Values
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A retained source reference bound discharges the concrete result decoder's
usize conversion, including its nonzero reference sentinel. -/
theorem result_index_fits_of_reference_bound (value : val)
    (bounded : SourceMachine.ReferenceBound Usize.max value) : ResultIndexFits value := by
  cases value <;> simp_all [SourceMachine.ReferenceBound, ResultIndexFits] <;> omega

end Itasca.Runtime.Interp
