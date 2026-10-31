module

public import InfillGLSLean.FiniteConditionalError
public import InfillGLSLean.GLSBiasBound

/-!
# Finite GLS conditional-MSE bound

This module composes the exact finite identities used in the proof of
`prop:consistency`.  It is deliberately written after conditioning on one
fixed regressor realization: `μ` is the conditional outcome law,
`workingCovariance` is `K_n`, `outcomeWeight` is `ω_n`, `mean` is `m_n`, and
`error` is `ε_n` at one fixed resolution.

The final theorem has the displayed algebraic form of `eq:mse-bound`.  Its
explicit hypotheses are the pieces that the manuscript derives from the
spatial model: centered regional errors, `Σ_n ⪯ C K_n`, the exact GLS weight
normalization, and control orthogonality for the same fixed coefficient `c`.
It does not itself construct those objects across resolutions, prove the
relative-mean condition, or establish conditional convergence in probability.
-/

public section

namespace InfillGLSLean

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The finite MSE bound for a centered score plus a deterministic GLS bias.
This is the post-conditioning core before replacing the score by the original
regional error vector. -/
theorem finiteGLS_MSE_bound_fixed_control [IsProbabilityMeasure μ]
    {workingCovariance : Matrix ι ι ℝ}
    (hworking : workingCovariance.PosDef)
    (outcomeWeight mean : ι → ℝ) (controls : Matrix ι κ ℝ)
    (fixedControl : κ → ℝ) (centeredError : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (centeredError i) 2 μ)
    (hscore : MemLp (finiteWeightedScore outcomeWeight centeredError) 2 μ)
    (hscore_centered : μ[finiteWeightedScore outcomeWeight centeredError] = 0)
    {scale information : ℝ}
    (hcovariance :
      (scale • workingCovariance - finiteErrorCovariance centeredError μ).PosSemidef)
    (hweight_norm : quadraticForm workingCovariance outcomeWeight = 1 / information)
    (hcontrols : outcomeWeight ⬝ᵥ (controls *ᵥ fixedControl) = 0) :
    finiteWeightedScoreMSE (outcomeWeight ⬝ᵥ mean) outcomeWeight centeredError μ ≤
      (scale + quadraticForm workingCovariance⁻¹
        (mean - controls *ᵥ fixedControl)) / information := by
  exact finiteWeightedScoreMSE_le_add_div_information
    (outcomeWeight ⬝ᵥ mean) outcomeWeight centeredError herror hscore hscore_centered
    hcovariance hweight_norm
    (gls_bias_bound_fixed_control hworking outcomeWeight mean controls fixedControl
      hweight_norm hcontrols)

/-- The finite conditional-MSE inequality in the raw regional-error notation
of `eq:mse-bound`.  The coordinate-centering assumption is the finite
post-conditioning form of `E(ε_n - m_n | X,W) = 0`. -/
theorem finiteGLS_rawError_MSE_bound_fixed_control [IsProbabilityMeasure μ]
    {workingCovariance : Matrix ι ι ℝ}
    (hworking : workingCovariance.PosDef)
    (outcomeWeight mean : ι → ℝ) (controls : Matrix ι κ ℝ)
    (fixedControl : κ → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ)
    (hcentered : ∀ i, μ[centeredFiniteError error mean i] = 0)
    {scale information : ℝ}
    (hcovariance : (scale • workingCovariance -
      finiteErrorCovariance (centeredFiniteError error mean) μ).PosSemidef)
    (hweight_norm : quadraticForm workingCovariance outcomeWeight = 1 / information)
    (hcontrols : outcomeWeight ⬝ᵥ (controls *ᵥ fixedControl) = 0) :
    (∫ ω, (finiteWeightedScore outcomeWeight error ω) ^ 2 ∂μ) ≤
      (scale + quadraticForm workingCovariance⁻¹
        (mean - controls *ᵥ fixedControl)) / information := by
  have hcenteredLp : ∀ i, MemLp (centeredFiniteError error mean i) 2 μ := by
    intro i
    exact (herror i).sub (memLp_const (mean i))
  have hscore := memLp_finiteWeightedScore outcomeWeight
    (centeredFiniteError error mean) hcenteredLp
  have hscore_centered := integral_finiteWeightedScore_eq_zero outcomeWeight
    (centeredFiniteError error mean) hcenteredLp hcentered
  rw [finiteWeightedError_sq_integral_eq_finiteWeightedScoreMSE]
  exact finiteGLS_MSE_bound_fixed_control hworking outcomeWeight mean controls fixedControl
    (centeredFiniteError error mean) hcenteredLp hscore hscore_centered hcovariance
    hweight_norm hcontrols

end InfillGLSLean
