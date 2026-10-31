module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Scalar covariance-order bounds for GLS mean-squared error

Task L-004, corresponding to the finite covariance-order step behind the
conditional MSE bound (manuscript `eq:mse-bound`).  This module treats the
one-dimensional case: a scalar linear functional with loading `a` and scalar
covariance (variance) `v`.  It intentionally does not claim the matrix
covariance-order result or any asymptotic statement; those require separate
finite-dimensional and probabilistic modules.

The central fact is that the map `v |-> a^2 * v` preserves order.  Thus an
upper bound on a scalar covariance transfers to the MSE of the corresponding
linear estimator.  The final two theorems record the usual scalar GLS form
`variance / information` when the information is positive.
-/

public section

namespace InfillGLSLean

/-- The mean-squared-error contribution of a scalar loading under a scalar
variance.  In dimension one this is the quadratic form `a * v * a`. -/
def scalarMSE (loading variance : ℝ) : ℝ :=
  loading ^ 2 * variance

/-- Scalar GLS MSE written as a variance divided by positive information. -/
noncomputable def scalarGLSMSE (variance information : ℝ) : ℝ :=
  variance / information

/-- A nonnegative scalar variance gives a nonnegative scalar MSE. -/
theorem scalarMSE_nonneg {loading variance : ℝ} (hvariance : 0 ≤ variance) :
    0 ≤ scalarMSE loading variance := by
  unfold scalarMSE
  exact mul_nonneg (sq_nonneg loading) hvariance

/-- Scalar covariance order transfers through a fixed scalar loading. -/
theorem scalarMSE_mono {loading lower upper : ℝ} (hcovariance : lower ≤ upper) :
    scalarMSE loading lower ≤ scalarMSE loading upper := by
  unfold scalarMSE
  exact mul_le_mul_of_nonneg_left hcovariance (sq_nonneg loading)

/-- The square of a weighted scalar error is its loading-squared times its
squared error. -/
theorem weighted_error_sq (loading error : ℝ) :
    (loading * error) ^ 2 = loading ^ 2 * error ^ 2 := by
  ring

/-- A bound on a scalar squared error transfers to its weighted version. -/
theorem weighted_error_sq_le_scalarMSE {loading error variance : ℝ}
    (herror : error ^ 2 ≤ variance) :
    (loading * error) ^ 2 ≤ scalarMSE loading variance := by
  rw [weighted_error_sq]
  exact scalarMSE_mono herror

/-- The scalar GLS MSE is nonnegative when variance is nonnegative and
information is positive. -/
theorem scalarGLSMSE_nonneg {variance information : ℝ}
    (hvariance : 0 ≤ variance) (hinformation : 0 < information) :
    0 ≤ scalarGLSMSE variance information := by
  unfold scalarGLSMSE
  exact div_nonneg hvariance (le_of_lt hinformation)

/-- A covariance upper bound transfers to the scalar GLS MSE for fixed,
positive information. -/
theorem scalarGLSMSE_mono {lower upper information : ℝ}
    (hcovariance : lower ≤ upper) (hinformation : 0 < information) :
    scalarGLSMSE lower information ≤ scalarGLSMSE upper information := by
  unfold scalarGLSMSE
  exact div_le_div_of_nonneg_right hcovariance (le_of_lt hinformation)

/-- A zero scalar loading has zero covariance contribution. -/
theorem scalarMSE_zero_loading (variance : ℝ) :
    scalarMSE 0 variance = 0 := by
  simp [scalarMSE]

end InfillGLSLean
