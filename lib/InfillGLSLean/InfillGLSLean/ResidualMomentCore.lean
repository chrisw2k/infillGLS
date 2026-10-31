module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic.Ring

public section

/-!
# Residual-scale mean-square decomposition

This finite probability-space module records the exact bias--variance
decomposition needed before a residual-scale estimator can be shown to be
consistent.  It does not assume Gaussianity and does not assert the
paper's spatial asymptotic result; a separate calculation must bound the two
terms exposed below.
-/

namespace InfillGLSLean

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Mean squared error of a real residual-scale statistic around a fixed
target scale. -/
noncomputable def residualScaleMSE (statistic : Ω → ℝ) (target : ℝ)
    (μ : Measure Ω) : ℝ :=
  ∫ ω, (statistic ω - target) ^ 2 ∂μ

/-- Exact bias--variance decomposition for a square-integrable residual-scale
statistic on a probability space. -/
theorem residualScaleMSE_eq_variance_add_bias_sq [IsProbabilityMeasure μ]
    {statistic : Ω → ℝ} (hstatistic : MemLp statistic 2 μ) (target : ℝ) :
    residualScaleMSE statistic target μ =
      Var[statistic; μ] + (μ[statistic] - target) ^ 2 := by
  let centered : Ω → ℝ := fun ω => statistic ω - target
  have hcentered : MemLp centered 2 μ := by
    exact hstatistic.sub (memLp_const target)
  have hmean : μ[centered] = μ[statistic] - target := by
    dsimp [centered]
    rw [integral_sub (hstatistic.integrable one_le_two) (integrable_const _), integral_const]
    simp
  calc
    residualScaleMSE statistic target μ = μ[centered ^ 2] := by
      simp [residualScaleMSE, centered]
    _ = Var[centered; μ] + μ[centered] ^ 2 := by
      rw [variance_eq_sub hcentered]
      ring
    _ = Var[statistic; μ] + (μ[statistic] - target) ^ 2 := by
      rw [variance_sub_const hstatistic.aestronglyMeasurable target, hmean]

/-- Deterministic upper bounds on variance and squared bias give an upper
bound on residual-scale mean squared error. -/
theorem residualScaleMSE_le_of_variance_le_and_bias_sq_le [IsProbabilityMeasure μ]
    {statistic : Ω → ℝ} (hstatistic : MemLp statistic 2 μ) (target varianceBound biasBound : ℝ)
    (hvariance : Var[statistic; μ] ≤ varianceBound)
    (hbias : (μ[statistic] - target) ^ 2 ≤ biasBound) :
    residualScaleMSE statistic target μ ≤ varianceBound + biasBound := by
  rw [residualScaleMSE_eq_variance_add_bias_sq hstatistic target]
  exact add_le_add hvariance hbias

/-- The order-two extended Lp seminorm of a residual-scale error is the
square root of its mean squared error. -/
theorem eLpNorm_two_residualScaleError_eq [IsProbabilityMeasure μ]
    {statistic : Ω → ℝ} (hstatistic : MemLp statistic 2 μ) (target : ℝ) :
    eLpNorm (fun ω => statistic ω - target) 2 μ =
      ENNReal.ofReal ((residualScaleMSE statistic target μ) ^ (1 / 2 : ℝ)) := by
  have herror : MemLp (fun ω => statistic ω - target) 2 μ :=
    hstatistic.sub (memLp_const target)
  rw [herror.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp [residualScaleMSE, Real.norm_eq_abs]

/-- Vanishing residual-scale mean squared error implies convergence in
probability of the statistic to its target. -/
theorem residualScale_tendstoInMeasure_of_MSE [IsProbabilityMeasure μ]
    {statistic : ℕ → Ω → ℝ} (target : ℝ)
    (hstatistic : ∀ n, MemLp (statistic n) 2 μ)
    (hmse : Tendsto (fun n => residualScaleMSE (statistic n) target μ)
      atTop (𝓝 0)) :
    TendstoInMeasure μ statistic atTop (fun _ => target) := by
  have hrpow : Tendsto
      (fun n => (residualScaleMSE (statistic n) target μ) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have hpow :=
      (Real.continuousAt_rpow_const (0 : ℝ) (1 / 2 : ℝ)
        (Or.inr (by norm_num : 0 ≤ (1 / 2 : ℝ)))).tendsto
    simpa [Function.comp_def] using hpow.comp hmse
  have henorm : Tendsto
      (fun n => ENNReal.ofReal
        ((residualScaleMSE (statistic n) target μ) ^ (1 / 2 : ℝ)))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hrpow
  refine tendstoInMeasure_of_tendsto_eLpNorm (μ := μ) (p := (2 : ℝ≥0∞)) (by norm_num) ?_
  apply henorm.congr'
  filter_upwards [] with n
  exact (eLpNorm_two_residualScaleError_eq (hstatistic n) target).symm

/-- If the variance and squared-bias bounds vanish along a sequence, then its
residual-scale MSE vanishes.  This is the finite-moment input for the existing
L2-to-convergence-in-probability bridge. -/
theorem residualScaleMSE_tendsto_zero_of_bounds [IsProbabilityMeasure μ]
    {statistic : ℕ → Ω → ℝ} {varianceBound biasBound : ℕ → ℝ} (target : ℝ)
    (hstatistic : ∀ n, MemLp (statistic n) 2 μ)
    (hvariance : ∀ n, Var[statistic n; μ] ≤ varianceBound n)
    (hbias : ∀ n, (μ[statistic n] - target) ^ 2 ≤ biasBound n)
    (hvariance_zero : Filter.Tendsto varianceBound Filter.atTop (𝓝 0))
    (hbias_zero : Filter.Tendsto biasBound Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => residualScaleMSE (statistic n) target μ)
      Filter.atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    unfold residualScaleMSE
    exact integral_nonneg (fun _ => sq_nonneg _)
  · intro n
    exact residualScaleMSE_le_of_variance_le_and_bias_sq_le
      (hstatistic n) target (varianceBound n) (biasBound n) (hvariance n) (hbias n)
  · simpa using hvariance_zero.add hbias_zero

/-- A residual-scale sequence converges in probability once its variance and
squared bias are bounded by deterministic sequences that both vanish. -/
theorem residualScale_tendstoInMeasure_of_variance_and_bias_bounds [IsProbabilityMeasure μ]
    {statistic : ℕ → Ω → ℝ} {varianceBound biasBound : ℕ → ℝ} (target : ℝ)
    (hstatistic : ∀ n, MemLp (statistic n) 2 μ)
    (hvariance : ∀ n, Var[statistic n; μ] ≤ varianceBound n)
    (hbias : ∀ n, (μ[statistic n] - target) ^ 2 ≤ biasBound n)
    (hvariance_zero : Tendsto varianceBound atTop (𝓝 0))
    (hbias_zero : Tendsto biasBound atTop (𝓝 0)) :
    TendstoInMeasure μ statistic atTop (fun _ => target) :=
  residualScale_tendstoInMeasure_of_MSE target hstatistic
    (residualScaleMSE_tendsto_zero_of_bounds target hstatistic hvariance hbias
      hvariance_zero hbias_zero)

end InfillGLSLean
