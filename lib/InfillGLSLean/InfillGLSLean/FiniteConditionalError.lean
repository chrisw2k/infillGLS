module

public import InfillGLSLean.FiniteWeightedScoreMSE
public import Mathlib.Tactic.Ring

/-!
# Finite conditional-error decomposition

For a fixed conditional regressor realization, this module makes the two
elementary probability identities in the proof of `prop:consistency` explicit:
the weighted regional error is a deterministic weighted conditional mean plus
a centered weighted score, and its square expectation is squared bias plus
the covariance quadratic form.

`μ` is the fixed conditional law, `error` is the finite regional error vector
`ε_n`, `mean` is the supplied vector `m_n`, and `weight` is `ω_n`.  The
coordinate-centering hypothesis is deliberately explicit: it is the place
where a future conditional-expectation model must establish that
`error - mean` is centered.  This module does not construct the spatial field,
the conditional law, or the GLS weight identity.
-/

public section

namespace InfillGLSLean

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]

/-- The coordinatewise centered version of a finite error vector. -/
@[expose]
noncomputable def centeredFiniteError (error : ι → Ω → ℝ)
    (mean : ι → ℝ) : ι → Ω → ℝ :=
  fun i ω => error i ω - mean i

omit [MeasurableSpace Ω] [Fintype ι] in
/-- Public pointwise expansion of a centered finite error. -/
@[simp]
theorem centeredFiniteError_apply (error : ι → Ω → ℝ) (mean : ι → ℝ)
    (i : ι) (ω : Ω) :
    centeredFiniteError error mean i ω = error i ω - mean i :=
  rfl

omit [MeasurableSpace Ω] in
/-- The weighted raw error decomposes into its weighted mean and centered
weighted score.  This is the finite form of `eq:decomposition`. -/
theorem finiteWeightedError_eq_bias_add_centeredScore
    (weight : ι → ℝ) (error : ι → Ω → ℝ) (mean : ι → ℝ) :
    finiteWeightedScore weight error =
      fun ω => (∑ i, weight i * mean i) +
        finiteWeightedScore weight (centeredFiniteError error mean) ω := by
  funext ω
  unfold finiteWeightedScore centeredFiniteError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The raw weighted-error square integral is the MSE of its deterministic
bias plus centered score. -/
theorem finiteWeightedError_sq_integral_eq_finiteWeightedScoreMSE
    (weight : ι → ℝ) (error : ι → Ω → ℝ) (mean : ι → ℝ) :
    (∫ ω, (finiteWeightedScore weight error ω) ^ 2 ∂μ) =
      finiteWeightedScoreMSE (weight ⬝ᵥ mean) weight
        (centeredFiniteError error mean) μ := by
  rw [finiteWeightedScoreMSE_eq_integral (weight ⬝ᵥ mean) weight
    (centeredFiniteError error mean) μ]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact congrArg (fun x : ℝ => x ^ 2)
    (congrFun (finiteWeightedError_eq_bias_add_centeredScore weight error mean) ω)

/-- Under coordinatewise centering, the raw weighted error has exactly the
squared-bias-plus-covariance MSE in `eq:exact-mse`. -/
theorem finiteWeightedError_sq_integral_eq_bias_sq_add_quadraticForm
    [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (error : ι → Ω → ℝ) (mean : ι → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ)
    (hcentered : ∀ i, μ[centeredFiniteError error mean i] = 0) :
    (∫ ω, (finiteWeightedScore weight error ω) ^ 2 ∂μ) =
      (weight ⬝ᵥ mean) ^ 2 +
        quadraticForm (finiteErrorCovariance (centeredFiniteError error mean) μ) weight := by
  have hcenteredLp : ∀ i, MemLp (centeredFiniteError error mean i) 2 μ := by
    intro i
    exact (herror i).sub (memLp_const (mean i))
  have hscore := memLp_finiteWeightedScore weight (centeredFiniteError error mean)
    hcenteredLp
  have hscore_centered := integral_finiteWeightedScore_eq_zero
    weight (centeredFiniteError error mean) hcenteredLp hcentered
  rw [finiteWeightedError_sq_integral_eq_finiteWeightedScoreMSE]
  exact finiteWeightedScoreMSE_eq_bias_sq_add_quadraticForm
    (weight ⬝ᵥ mean) weight (centeredFiniteError error mean) hcenteredLp hscore
      hscore_centered

end InfillGLSLean
