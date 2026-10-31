module

public import InfillGLSLean.AsymptoticCore
public import Mathlib.Probability.Distributions.Gaussian.Real

public section

/-!
# Abstract infill-GLS propositions

This module gives named, fully checked abstract forms of the three principal
asymptotic implications in the manuscript:

* consistency from a vanishing conditional-MSE envelope;
* asymptotic normality from a standardized-score limit, a scale comparison,
  and negligible bias;
* transfer of a standardized normal limit to a studentized statistic.

The spatial regional-average construction, matrix covariance inequalities,
Gaussian quadratic-form calculation, and conditional-probability construction
are deliberately hypotheses of these statements rather than concealed
assumptions.  Their dedicated finite and measure-theoretic components live in
the supporting modules.
-/

namespace InfillGLSLean

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- **Abstract consistency proposition.**

If the variance and squared-bias terms in a GLS MSE decomposition both vanish,
then the estimator error converges in probability to zero.  Under a fixed
probability measure, `TendstoInMeasure` is convergence in probability. -/
theorem infillGLS_consistency
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {estimationError : ℕ → Ω → ℝ}
    {varianceTerm biasTerm : ℕ → ℝ≥0∞}
    (hmse : ∀ n, quadraticL2Error (estimationError n) μ ≤ varianceTerm n + biasTerm n)
    (hvariance : Tendsto varianceTerm atTop (𝓝 0))
    (hbias : Tendsto biasTerm atTop (𝓝 0)) :
    TendstoInMeasure μ estimationError atTop (fun _ => 0) :=
  gls_consistency_of_split_quadraticL2_bound hmse hvariance hbias

/-- **Abstract asymptotic-normality proposition.**

The conclusion is a standard normal distributional limit once a separately
constructed standardized score tends to a standard Gaussian, its scale tends
to one, and its bias tends to zero in probability.  The explicit
`HasLaw` hypothesis records the target law; no geographic or covariance-model
claim is made here. -/
theorem infillGLS_asymptotic_normality
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {statistic centeredScore scale bias : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hstatistic : ∀ n ω, statistic n ω = centeredScore n ω * scale n ω + bias n ω)
    (hcentered : TendstoInDistribution centeredScore atTop Z (fun _ => μ) μ')
    (hscale : TendstoInMeasure μ scale atTop (fun _ => (1 : ℝ)))
    (hscale_meas : ∀ n, AEMeasurable (scale n) μ)
    (hbias : TendstoInMeasure μ bias atTop (fun _ => (0 : ℝ)))
    (hbias_meas : ∀ n, AEMeasurable (bias n) μ)
    (_hZ : HasLaw Z (gaussianReal 0 1) μ') :
    TendstoInDistribution statistic atTop Z (fun _ => μ) μ' := by
  have hlimit := tendstoInDistribution_scale_bias_of_standardized
    hcentered hscale hscale_meas hbias hbias_meas
  refine hlimit.congr ?_ ?_
  · intro n
    filter_upwards [] with ω
    exact (hstatistic n ω).symm
  · filter_upwards [] with ω
    rfl

/-- **Abstract studentization transfer.**

If a standardized GLS score has a standard-normal limit and the ratio that
converts it to the reported studentized statistic converges in probability to
one, then the reported studentized statistic has the same normal limit.  In a
GLS application the scale is normally `sqrt(actualVariance / reportedVariance)`;
proving that representation and its convergence is intentionally external to
this theorem. -/
theorem infillGLS_studentized_normality
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {studentized standardized scale : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hstudentized : ∀ n ω, studentized n ω = standardized n ω * scale n ω)
    (hstandardized : TendstoInDistribution standardized atTop Z (fun _ => μ) μ')
    (hscale : TendstoInMeasure μ scale atTop (fun _ => (1 : ℝ)))
    (hscale_meas : ∀ n, AEMeasurable (scale n) μ)
    (_hZ : HasLaw Z (gaussianReal 0 1) μ') :
    TendstoInDistribution studentized atTop Z (fun _ => μ) μ' := by
  have hlimit := tendstoInDistribution_mul_of_tendstoInMeasure_one
    hstandardized hscale hscale_meas
  refine hlimit.congr ?_ ?_
  · intro n
    filter_upwards [] with ω
    exact (hstudentized n ω).symm
  · filter_upwards [] with ω
    rfl

end InfillGLSLean
