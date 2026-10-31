module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Vanishing-bias Gaussian limits

This file provides a small, reusable asymptotic-normality building block.  It
does **not** prove the full infill-GLS normality theorem: that theorem requires
the statistical assumptions that identify a GLS error with the Gaussian random
variable used below.  Instead, it verifies the distributional step once such
a representation has been established.
-/

public section

namespace InfillGLSLean

open Filter MeasureTheory ProbabilityTheory Topology

/-- A deterministic shift of a centered Gaussian statistic has the expected
Gaussian law at every index of a sequence. -/
theorem gaussian_shift_sequence_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {variance : NNReal} (hX : HasLaw X (gaussianReal 0 variance) P)
    (bias : ℕ → ℝ) (n : ℕ) :
    HasLaw (fun ω => X ω + bias n) (gaussianReal (bias n) variance) P := by
  simpa using gaussianReal_add_const hX (bias n)

/-- If the deterministic bias of a centered Gaussian statistic vanishes, then
the shifted statistics converge in distribution to that centered Gaussian
statistic.  This is the bias-negligibility component of a Gaussian
asymptotic-normality argument. -/
theorem gaussian_vanishing_bias_tendstoInDistribution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {variance : NNReal} (hX : HasLaw X (gaussianReal 0 variance) P)
    {bias : ℕ → ℝ} (hbias : Tendsto bias atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => X ω + bias n) atTop X (fun _ => P) P := by
  have h_bias_in_measure :
      TendstoInMeasure P (fun n (_ : Ω) => bias n) atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact stronglyMeasurable_const.aestronglyMeasurable
    · filter_upwards [] with ω
      simpa using hbias
  have h_bias_measurable : ∀ n, AEMeasurable (fun _ : Ω => bias n) P := by
    intro n
    exact stronglyMeasurable_const.aemeasurable
  have h_limit :=
    (tendstoInDistribution_const hX.aemeasurable).add_of_tendstoInMeasure_const
      h_bias_in_measure h_bias_measurable
  refine h_limit.congr ?_ ?_
  · intro n
    filter_upwards [] with ω
    change (X + fun _ : Ω => bias n) ω = X ω + bias n
    rfl
  · filter_upwards [] with ω
    simp

/-- A common Gaussian statistic remains asymptotically unchanged when its
deterministic scale tends to one and its deterministic bias tends to zero.
This is the distributional step used after a GLS score has been coupled to a
standard Gaussian statistic and its variance comparison has supplied the
scale sequence. -/
theorem gaussian_scale_and_bias_tendstoInDistribution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {variance : NNReal} (hX : HasLaw X (gaussianReal 0 variance) P)
    {scale bias : ℕ → ℝ}
    (hscale : Tendsto scale atTop (𝓝 1))
    (hbias : Tendsto bias atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => scale n * X ω + bias n) atTop X
      (fun _ => P) P := by
  refine tendstoInDistribution_of_ae_tendsto ?_ hX.aemeasurable ?_
  · intro n
    exact (hX.aemeasurable.const_mul (scale n)).add_const (bias n)
  · filter_upwards [] with ω
    simpa using (hscale.mul_const (X ω)).add hbias

end InfillGLSLean
