module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Scalar Gaussian building blocks for GLS inference

Task L-005 begins the normal-inference layer with exact distributional facts.
The manuscript's full asymptotic-normality proposition additionally needs
matrix covariance comparison and a vanishing bias sequence.  This module
proves the reusable affine-Gaussian step without assuming those later bridges.
-/

public section

namespace InfillGLSLean

open MeasureTheory ProbabilityTheory

/-- Adding a deterministic bias to a centered Gaussian shifts its mean and
does not change its variance. -/
theorem gaussian_shift_of_centered
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {variance : NNReal} (hX : HasLaw X (gaussianReal 0 variance) P)
    (bias : ℝ) :
    HasLaw (fun ω => X ω + bias) (gaussianReal bias variance) P := by
  simpa using gaussianReal_add_const hX bias

/-- An affine transformation of a real Gaussian is Gaussian with the
corresponding affine mean and squared-scale variance. -/
theorem gaussian_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {mean : ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal mean variance) P)
    (scale bias : ℝ) :
    HasLaw (fun ω => scale * X ω + bias)
      (gaussianReal (scale * mean + bias)
        (NNReal.mk (scale ^ 2) (sq_nonneg scale) * variance)) P := by
  simpa using gaussianReal_add_const (gaussianReal_const_mul hX scale) bias

end InfillGLSLean
