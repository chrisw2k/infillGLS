module

public import InfillGLSLean.FiniteRandomScore
public import Mathlib.Tactic.Ring

public section

/-!
# Finite weighted-score mean-squared error

This module assembles the finite score covariance calculation with the exact
bias--variance decomposition.  It is the probability-space core of the
manuscript's GLS MSE inequality: the spatial construction of the error vector,
the working weight normalization, and asymptotic hypotheses remain separate.

## Manuscript correspondence and boundary

For one fixed conditional regressor realization, `μ` represents the
conditional law, `finiteWeightedScore weight error` represents
`ω_n' (ε_n - m_n)`, and `bias` represents `ω_n' m_n` in `eq:decomposition`.
`hscore_centered` is precisely the finite centered-score condition.  In the
normalized bound, `hweight` represents the exact weight identity
`ω_n' K_n ω_n = 1 / Q_n`; `hcovariance` represents the finite covariance
order `Σ_n ≼ scale K_n`; and `hbias` represents the separately established
Cauchy--Schwarz/mean-energy bound.  Consequently the final theorem is the
finite MSE inequality shape of `eq:mse-bound`, not Proposition
`prop:consistency`: it does not construct conditional laws, derive the score
centering from a spatial field, establish the named weight identity, or prove
the sequence-level infill assumptions and convergence.
-/

namespace InfillGLSLean

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]

/-- Mean squared error of a deterministic bias plus a finite weighted random
score. -/
@[expose]
noncomputable def finiteWeightedScoreMSE (bias : ℝ) (weight : ι → ℝ)
    (error : ι → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (bias + finiteWeightedScore weight error ω) ^ 2 ∂μ

/-- Public expansion of the finite weighted-score MSE. -/
@[simp]
theorem finiteWeightedScoreMSE_eq_integral (bias : ℝ) (weight : ι → ℝ)
    (error : ι → Ω → ℝ) (μ : Measure Ω) :
    finiteWeightedScoreMSE bias weight error μ =
      ∫ ω, (bias + finiteWeightedScore weight error ω) ^ 2 ∂μ :=
  rfl

/-- Exact finite bias--variance decomposition for a GLS-style weighted score.
The covariance term is written as the finite covariance quadratic form. -/
theorem finiteWeightedScoreMSE_eq_bias_sq_add_quadraticForm [IsProbabilityMeasure μ]
    (bias : ℝ) (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ)
    (hscore : MemLp (finiteWeightedScore weight error) 2 μ)
    (hscore_centered : μ[finiteWeightedScore weight error] = 0) :
    finiteWeightedScoreMSE bias weight error μ =
      bias ^ 2 + quadraticForm (finiteErrorCovariance error μ) weight := by
  let score : Ω → ℝ := finiteWeightedScore weight error
  have hscore' : MemLp score 2 μ := by
    simpa only [score] using hscore
  have hmean : μ[score] = 0 := by
    simpa only [score] using hscore_centered
  have hshift : MemLp (fun ω => bias + score ω) 2 μ :=
    (memLp_const bias).add hscore'
  have hshift_mean : μ[fun ω => bias + score ω] = bias := by
    rw [integral_add (integrable_const _) (hscore'.integrable one_le_two), integral_const, hmean]
    simp
  calc
    finiteWeightedScoreMSE bias weight error μ =
        Var[fun ω => bias + score ω; μ] + (μ[fun ω => bias + score ω]) ^ 2 := by
          change (∫ ω, (bias + score ω) ^ 2 ∂μ) =
            Var[fun ω => bias + score ω; μ] + (μ[fun ω => bias + score ω]) ^ 2
          have hvariance_shift :
              Var[fun ω => bias + score ω; μ] =
                (∫ ω, (bias + score ω) ^ 2 ∂μ) - bias ^ 2 := by
            rw [variance_eq_sub hshift, hshift_mean]
            simp only [Pi.pow_apply]
          calc
            (∫ ω, (bias + score ω) ^ 2 ∂μ) =
                ((∫ ω, (bias + score ω) ^ 2 ∂μ) - bias ^ 2) + bias ^ 2 := by ring
            _ = Var[fun ω => bias + score ω; μ] + bias ^ 2 := by
              rw [← hvariance_shift]
            _ = Var[fun ω => bias + score ω; μ] +
                (μ[fun ω => bias + score ω]) ^ 2 := by rw [hshift_mean]
    _ = Var[score; μ] + bias ^ 2 := by
          rw [variance_const_add hscore'.aestronglyMeasurable bias, hshift_mean]
    _ = bias ^ 2 + quadraticForm (finiteErrorCovariance error μ) weight := by
          have hvariance :=
            variance_finiteWeightedScore_eq_quadraticForm weight error herror
          change Var[finiteWeightedScore weight error; μ] + bias ^ 2 = _
          rw [hvariance]
          simp only [quadraticForm_eq_dotProduct_mulVec]
          ring

/-- A finite covariance Loewner upper bound controls the MSE of a weighted
score up to its deterministic squared bias. -/
theorem finiteWeightedScoreMSE_le_bias_sq_add_scale_div_information
    [IsProbabilityMeasure μ]
    (bias : ℝ) (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ)
    (hscore : MemLp (finiteWeightedScore weight error) 2 μ)
    (hscore_centered : μ[finiteWeightedScore weight error] = 0)
    {working : Matrix ι ι ℝ} {scale information : ℝ}
    (hcovariance : (scale • working - finiteErrorCovariance error μ).PosSemidef)
    (hweight : quadraticForm working weight = 1 / information) :
    finiteWeightedScoreMSE bias weight error μ ≤ bias ^ 2 + scale / information := by
  rw [finiteWeightedScoreMSE_eq_bias_sq_add_quadraticForm bias weight error herror hscore
    hscore_centered]
  have hvariance :=
    variance_finiteWeightedScore_le_scale_div_information weight error herror hcovariance hweight
  rw [variance_finiteWeightedScore_eq_quadraticForm weight error herror] at hvariance
  exact add_le_add le_rfl hvariance

/-- The finite GLS MSE inequality in normalized form.  The separate
`biasBound` hypothesis is where a Cauchy--Schwarz/mean-energy calculation is
inserted by the GLS-weight layer. -/
theorem finiteWeightedScoreMSE_le_add_div_information [IsProbabilityMeasure μ]
    (bias : ℝ) (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ)
    (hscore : MemLp (finiteWeightedScore weight error) 2 μ)
    (hscore_centered : μ[finiteWeightedScore weight error] = 0)
    {working : Matrix ι ι ℝ} {scale biasBound information : ℝ}
    (hcovariance : (scale • working - finiteErrorCovariance error μ).PosSemidef)
    (hweight : quadraticForm working weight = 1 / information)
    (hbias : bias ^ 2 ≤ biasBound / information) :
    finiteWeightedScoreMSE bias weight error μ ≤
      (scale + biasBound) / information := by
  calc
    finiteWeightedScoreMSE bias weight error μ ≤ bias ^ 2 + scale / information :=
      finiteWeightedScoreMSE_le_bias_sq_add_scale_div_information bias weight error
        herror hscore hscore_centered hcovariance hweight
    _ ≤ biasBound / information + scale / information :=
      add_le_add hbias le_rfl
    _ = (scale + biasBound) / information := by ring

end InfillGLSLean
