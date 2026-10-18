import SpecExt.Builtins.Float.Round
import SpecExt.Builtins.Int

/-! Scalar floating-point operations, including the nondeterministic NaN sets,
signed-zero rules, exact comparisons, and rational rounding. -/

open SpecExt.Builtins.Float

def fabs_ (_width : N) (value : fN) : List fN := [.POS (magnitude value)]
def fneg_ (_width : N) (value : fN) : List fN :=
  [withSign (!negative value) (magnitude value)]
def fcopysign_ (_width : N) (a b : fN) : List fN :=
  [withSign (negative b) (magnitude a)]

def feq_ (width : N) (a b : fN) : u32 := .mk_uN (if equal width a b then 1 else 0)
def fne_ (width : N) (a b : fN) : u32 := .mk_uN (if equal width a b then 0 else 1)
def flt_ (width : N) (a b : fN) : u32 := .mk_uN (if less width a b then 1 else 0)
def fgt_ (width : N) (a b : fN) : u32 := flt_ width b a
def fle_ (width : N) (a b : fN) : u32 :=
  .mk_uN (if less width a b || equal width a b then 1 else 0)
def fge_ (width : N) (a b : fN) : u32 := fle_ width b a

def fmin_ (width : N) (a b : fN) : List fN :=
  if isNaN a || isNaN b then nans width [a, b]
  else if isZero a && isZero b then [withSign (negative a || negative b) (.SUBNORM 0)]
  else [if less width a b then a else b]

def fmax_ (width : N) (a b : fN) : List fN :=
  if isNaN a || isNaN b then nans width [a, b]
  else if isZero a && isZero b then [withSign (negative a && negative b) (.SUBNORM 0)]
  else [if less width a b then b else a]

def fpmin_ (width : N) (a b : fN) : List fN := [if less width b a then b else a]
def fpmax_ (width : N) (a b : fN) : List fN := [if less width a b then b else a]

def fadd_ (width : N) (a b : fN) : List fN :=
  if isNaN a || isNaN b then nans width [a, b]
  else if isInf a && isInf b && negative a != negative b then nans width []
  else if isInf a then [a]
  else if isInf b then [b]
  else [round width (finiteValue width a + finiteValue width b)
    (isZero a && isZero b && negative a && negative b)]

def fsub_ (width : N) (a b : fN) : List fN :=
  if isNaN a || isNaN b then nans width [a, b]
  else fadd_ width a (withSign (!negative b) (magnitude b))

def fmul_ (width : N) (a b : fN) : List fN :=
  if isNaN a || isNaN b then nans width [a, b]
  else if (isInf a && isZero b) || (isZero a && isInf b) then nans width []
  else if isInf a || isInf b then [withSign (negative a != negative b) .INF]
  else [round width (finiteValue width a * finiteValue width b) (negative a != negative b)]

def fdiv_ (width : N) (a b : fN) : List fN :=
  if isNaN a || isNaN b then nans width [a, b]
  else if (isInf a && isInf b) || (isZero a && isZero b) then nans width []
  else if isInf a || isZero b then [withSign (negative a != negative b) .INF]
  else if isInf b || isZero a then [withSign (negative a != negative b) (.SUBNORM 0)]
  else [round width (finiteValue width a / finiteValue width b)]

def fsqrt_ (width : N) (value : fN) : List fN :=
  if isNaN value then nans width [value]
  else if isZero value then [value]
  else if negative value then nans width []
  else if isInf value then [value]
  else [roundSqrt width (finiteValue width value)]

namespace SpecExt.Builtins.Float

/-- Mathematical nearest integer, ties to the even integer (also for negatives). -/
def nearestInteger (q : Rat) : Int :=
  let lo := q.floor
  let fraction := q - (lo : Rat)
  if fraction < 1 / 2 then lo
  else if 1 / 2 < fraction then lo + 1
  else if lo % 2 = 0 then lo else lo + 1

def integral (op : Rat → Int) (width : N) (value : fN) : List fN :=
  if isNaN value then nans width [value]
  else if isInf value || isZero value then [value]
  else [round width (op (finiteValue width value) : Rat) (negative value)]

end SpecExt.Builtins.Float

def fceil_ (width : N) (value : fN) : List fN := integral Rat.ceil width value
def ffloor_ (width : N) (value : fN) : List fN := integral Rat.floor width value
def ftrunc_ (width : N) (value : fN) : List fN := integral truncz width value
def fnearest_ (width : N) (value : fN) : List fN := integral nearestInteger width value
