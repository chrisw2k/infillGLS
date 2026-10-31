module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# Mean-square bounds imply consistency in probability

Task L-008 (consistency layer), supporting the manuscript's infill-consistency
claims.  This module proves the scalar probabilistic bridge only: a centered
real-valued error sequence with finite second moments and a deterministic
mean-square-error upper bound converging to zero converges to zero in
probability (Lean's `TendstoInMeasure`).  It uses Mathlib's Chebyshev
inequality and does not formalize the spatial construction of the bound.

The theorem is deliberately stated for a fixed finite measure space (and is
the usual convergence-in-probability statement when that measure is a
probability measure). Conditional versions and the manuscript's regional and
covariance-space arguments require separate modules that construct the
hypotheses used here.
-/

public section

namespace InfillGLSLean

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The (unconditional) mean squared error of a real-valued random error. -/
noncomputable def meanSquaredError (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (X ω) ^ 2 ∂μ

/-- A mean squared error is nonnegative. -/
theorem meanSquaredError_nonneg (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ meanSquaredError X μ := by
  unfold meanSquaredError
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Chebyshev's inequality in the centered, mean-squared-error form.

The right-hand side is a genuine finite-second-moment bound, not an assumed
tail inequality. -/
theorem chebyshev_meanSquaredError_bound [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (hcenter : ∫ ω, X ω ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |X ω|} ≤ ENNReal.ofReal (meanSquaredError X μ / ε ^ 2) := by
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hX hε
  rw [ProbabilityTheory.variance_of_integral_eq_zero hX.aemeasurable hcenter] at hcheb
  simpa [meanSquaredError, hcenter] using hcheb

/-- A pointwise deterministic upper bound tending to zero squeezes the MSE to
zero. -/
theorem meanSquaredError_tendsto_zero_of_bound
    {X : ℕ → Ω → ℝ} {bound : ℕ → ℝ}
    (hbound : ∀ n, meanSquaredError (X n) μ ≤ bound n)
    (hbound_zero : Tendsto bound atTop (𝓝 0)) :
    Tendsto (fun n => meanSquaredError (X n) μ) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact meanSquaredError_nonneg (X n) μ
  · exact hbound
  · exact hbound_zero

/-- A centered finite-MSE error sequence converges in probability to zero when
its deterministic MSE upper bound vanishes.

`TendstoInMeasure` is Mathlib's convergence-in-measure notion, which is the
standard convergence-in-probability formulation for a probability measure.
Applying this theorem to an estimator minus its target is the consistency step
used by later GLS asymptotic modules. -/
theorem tendstoInMeasure_zero_of_meanSquaredError_bound [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {bound : ℕ → ℝ}
    (hX : ∀ n, MemLp (X n) 2 μ)
    (hcenter : ∀ n, ∫ ω, X n ω ∂μ = 0)
    (hbound : ∀ n, meanSquaredError (X n) μ ≤ bound n)
    (hbound_zero : Tendsto bound atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hupper : Tendsto (fun n => ENNReal.ofReal (bound n / ε ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hbound_zero.div_const (ε ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => zero_le) ?_
  intro n
  simp only [dist_zero_right, Real.norm_eq_abs]
  calc
    μ {ω | ε ≤ |X n ω|} ≤ ENNReal.ofReal (meanSquaredError (X n) μ / ε ^ 2) :=
      chebyshev_meanSquaredError_bound (hX n) (hcenter n) hε
    _ ≤ ENNReal.ofReal (bound n / ε ^ 2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hbound n) (sq_nonneg ε))

end InfillGLSLean
