module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic.Ring

public section

/-!
# Gaussian rank-one quadratic moments

This module formalizes the exact second-moment calculation for a real
Gaussian linear statistic.  It is a narrowly scoped helper for the
residual-scale proof in manuscript Appendix `app:scale`, whose displayed
quadratic-form expectation is `tr(P_n Γ_n) + ‖b_n‖²` and whose variance is a
separate noncentral matrix formula.  Before such a full matrix calculation
can be applied, each residual direction has a centered Gaussian square whose
expectation is its variance.

The results intentionally do not claim either displayed Appendix `app:scale`
matrix identity, its trace bounds, or its `O_p(N_n⁻¹ᐟ²)` conclusion.  They
expose only concrete scalar and diagonal exact Gaussian calculations without
adding unproved principles or placeholders.
-/

namespace InfillGLSLean

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A Gaussian linear statistic has centered second moment equal to its
variance parameter. -/
theorem gaussian_centered_square_integral
    {X : Ω → ℝ} {mean : ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal mean variance) P) :
    (∫ ω, (X ω - mean) ^ 2 ∂P) = variance := by
  have hmean : ∫ ω, X ω ∂P = mean := by
    calc
      (∫ ω, X ω ∂P) = ∫ x, x ∂gaussianReal mean variance := hX.integral_eq
      _ = mean := integral_id_gaussianReal
  calc
    (∫ ω, (X ω - mean) ^ 2 ∂P) =
        ∫ ω, (X ω - ∫ z, X z ∂P) ^ 2 ∂P := by rw [hmean]
    _ = Var[X; P] := (variance_eq_integral hX.aemeasurable).symm
    _ = Var[id; gaussianReal mean variance] := hX.variance_eq
    _ = variance := variance_id_gaussianReal

/-- The centered square of any scalar multiple of a Gaussian linear statistic
has the correspondingly scaled variance. -/
theorem gaussian_scaled_centered_square_integral
    {X : Ω → ℝ} {mean scale : ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal mean variance) P) :
    (∫ ω, (scale * (X ω - mean)) ^ 2 ∂P) = scale ^ 2 * variance := by
  calc
    (∫ ω, (scale * (X ω - mean)) ^ 2 ∂P) =
        ∫ ω, scale ^ 2 * (X ω - mean) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
    _ = scale ^ 2 * ∫ ω, (X ω - mean) ^ 2 ∂P := by
          rw [integral_const_mul]
    _ = scale ^ 2 * variance := by
          rw [gaussian_centered_square_integral hX]

/-- An affine Gaussian statistic has squared error around its affine mean
equal to the scale-squared times its original variance. -/
theorem gaussian_affine_square_error_integral
    {X : Ω → ℝ} {mean scale shift : ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal mean variance) P) :
    (∫ ω, (scale * X ω + shift - (scale * mean + shift)) ^ 2 ∂P) =
      scale ^ 2 * variance := by
  have h := gaussian_scaled_centered_square_integral (scale := scale) hX
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  ring

/-- A centered Gaussian's uncentered square is its variance.  This is the
form most directly used after whitening a residual direction. -/
theorem centered_gaussian_square_integral
    {X : Ω → ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal 0 variance) P) :
    (∫ ω, (X ω) ^ 2 ∂P) = variance := by
  simpa using gaussian_centered_square_integral hX

/-- A finite diagonal Gaussian quadratic statistic has expectation equal to
the corresponding weighted sum of marginal variances.  Independence is not
needed because no cross-products appear; a full quadratic-form trace formula
would additionally require those covariance terms. -/
theorem gaussian_diagonal_quadratic_integral
    {ι : Type*} [Fintype ι] [IsProbabilityMeasure P] {X : ι → Ω → ℝ} {mean : ι → ℝ}
    {variance : ι → NNReal} (hX : ∀ i, HasLaw (X i) (gaussianReal (mean i) (variance i)) P)
    (scale : ι → ℝ) :
    (∫ ω, ∑ i, (scale i * (X i ω - mean i)) ^ 2 ∂P) =
      ∑ i, scale i ^ 2 * variance i := by
  let f : ι → Ω → ℝ := fun i ω => (scale i * (X i ω - mean i)) ^ 2
  have hintegrable : ∀ i, Integrable (f i) P := by
    intro i
    have hmemX : MemLp (X i) 2 P :=
      (hX i).memLp (memLp_id_gaussianReal' 2 (by norm_num))
    have hmemCentered : MemLp (fun ω => X i ω - mean i) 2 P :=
      hmemX.sub (memLp_const (mean i))
    have hmemScaled : MemLp (fun ω => scale i * (X i ω - mean i)) 2 P :=
      hmemCentered.const_mul (scale i)
    simpa only [f, Real.norm_eq_abs, sq_abs] using
      hmemScaled.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  change (∫ ω, ∑ i, f i ω ∂P) = ∑ i, scale i ^ 2 * variance i
  calc
    (∫ ω, ∑ i, f i ω ∂P) = ∑ i, ∫ ω, f i ω ∂P :=
      integral_finsetSum Finset.univ (fun i _ => hintegrable i)
    _ = ∑ i, scale i ^ 2 * variance i := by
      apply Finset.sum_congr rfl
      intro i _
      exact gaussian_scaled_centered_square_integral (scale := scale i) (hX i)

end InfillGLSLean
