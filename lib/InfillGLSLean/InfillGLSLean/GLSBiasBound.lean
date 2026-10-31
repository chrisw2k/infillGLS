module

public import InfillGLSLean.MatrixCovarianceOrder
public import Mathlib.Tactic.Ring

public section

/-!
# Finite GLS bias bound

This module formalizes the finite Cauchy--Schwarz calculation in
`eq:bias-bound`, after conditioning on a fixed regressor realization.

## Manuscript mapping and boundary

`workingCovariance` is `K_n`, `workingCovariance⁻¹` is `K_n^{-1}`,
`outcomeWeight` is the GLS outcome-weight vector `ω_n`, `mean` is `m_n`,
`controls` is `W_n`, and `fixedControl` is the *same fixed* coefficient
vector `c` at every resolution.  `hcontrols` is exactly
`ω_n' W_n = 0` applied to `c`; `hweight_norm` is the separately established
weight identity `ω_n' K_n ω_n = 1 / Q_n`.

The conclusion is the finite inequality used inside the proof of
`prop:consistency`.  It does not establish the full proposition: it does not
construct conditional means/covariances, prove the GLS weight identities from
the paper's complete design, nor establish `Q_n` divergence or the
sequence-level relative-mean condition.
-/

namespace InfillGLSLean

open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Passing a GLS outcome weight through its working covariance and then the
working precision recovers its ordinary score against any vector. -/
theorem workingCovariance_dual_score_eq
    {workingCovariance : Matrix ι ι ℝ}
    (hworking : workingCovariance.PosDef)
    (outcomeWeight vector : ι → ℝ) :
    (workingCovariance *ᵥ outcomeWeight) ⬝ᵥ
        (workingCovariance⁻¹ *ᵥ vector) =
      outcomeWeight ⬝ᵥ vector := by
  have hdet : IsUnit workingCovariance.det :=
    workingCovariance.isUnit_iff_isUnit_det.mp hworking.isUnit
  have hsymm : workingCovariance.transpose = workingCovariance := by
    simpa using hworking.isHermitian.eq
  calc
    (workingCovariance *ᵥ outcomeWeight) ⬝ᵥ
        (workingCovariance⁻¹ *ᵥ vector) =
        (workingCovariance⁻¹ *ᵥ vector) ⬝ᵥ
          (workingCovariance *ᵥ outcomeWeight) := dotProduct_comm _ _
    _ = outcomeWeight ⬝ᵥ
        (workingCovariance.transpose *ᵥ (workingCovariance⁻¹ *ᵥ vector)) := by
          symm
          exact dotProduct_transpose_mulVec workingCovariance outcomeWeight
            (workingCovariance⁻¹ *ᵥ vector)
    _ = outcomeWeight ⬝ᵥ
        (workingCovariance *ᵥ (workingCovariance⁻¹ *ᵥ vector)) := by
          rw [hsymm]
    _ = outcomeWeight ⬝ᵥ
        ((workingCovariance * workingCovariance⁻¹) *ᵥ vector) := by
          rw [Matrix.mulVec_mulVec]
    _ = outcomeWeight ⬝ᵥ (1 *ᵥ vector) := by
          rw [Matrix.mul_nonsing_inv _ hdet]
    _ = outcomeWeight ⬝ᵥ vector := by simp

/-- The precision quadratic form of the working-covariance transform of a
GLS outcome weight is its ordinary working-covariance quadratic form. -/
theorem quadraticForm_inverse_working_mulVec_eq
    {workingCovariance : Matrix ι ι ℝ}
    (hworking : workingCovariance.PosDef)
    (outcomeWeight : ι → ℝ) :
    quadraticForm workingCovariance⁻¹ (workingCovariance *ᵥ outcomeWeight) =
      quadraticForm workingCovariance outcomeWeight := by
  have hdet : IsUnit workingCovariance.det :=
    workingCovariance.isUnit_iff_isUnit_det.mp hworking.isUnit
  simp only [quadraticForm_eq_dotProduct_mulVec]
  calc
    (workingCovariance *ᵥ outcomeWeight) ⬝ᵥ
        (workingCovariance⁻¹ *ᵥ (workingCovariance *ᵥ outcomeWeight)) =
        (workingCovariance *ᵥ outcomeWeight) ⬝ᵥ
          ((workingCovariance⁻¹ * workingCovariance) *ᵥ outcomeWeight) := by
            rw [Matrix.mulVec_mulVec]
    _ = (workingCovariance *ᵥ outcomeWeight) ⬝ᵥ (1 *ᵥ outcomeWeight) := by
          rw [Matrix.nonsing_inv_mul _ hdet]
    _ = outcomeWeight ⬝ᵥ (workingCovariance *ᵥ outcomeWeight) := by
          simp [dotProduct_comm]

/-- GLS orthogonality to a fixed control combination transfers to the
precision-coordinate form required by matrix Cauchy--Schwarz. -/
theorem workingCovariance_dual_control_orthogonal
    {workingCovariance : Matrix ι ι ℝ}
    (hworking : workingCovariance.PosDef)
    (outcomeWeight : ι → ℝ) (controls : Matrix ι κ ℝ)
    (fixedControl : κ → ℝ)
    (hcontrols : outcomeWeight ⬝ᵥ (controls *ᵥ fixedControl) = 0) :
    (workingCovariance *ᵥ outcomeWeight) ⬝ᵥ
      (workingCovariance⁻¹ *ᵥ (controls *ᵥ fixedControl)) = 0 := by
  rw [workingCovariance_dual_score_eq hworking outcomeWeight
    (controls *ᵥ fixedControl)]
  exact hcontrols

/-- The finite post-conditioning GLS bias bound.  This is the
Cauchy--Schwarz line of `eq:bias-bound`, with all normalization and control
orthogonality assumptions shown explicitly. -/
theorem gls_bias_bound_fixed_control
    {workingCovariance : Matrix ι ι ℝ}
    (hworking : workingCovariance.PosDef)
    (outcomeWeight mean : ι → ℝ) (controls : Matrix ι κ ℝ)
    (fixedControl : κ → ℝ) {information : ℝ}
    (hweight_norm : quadraticForm workingCovariance outcomeWeight = 1 / information)
    (hcontrols : outcomeWeight ⬝ᵥ (controls *ᵥ fixedControl) = 0) :
    (outcomeWeight ⬝ᵥ mean) ^ 2 ≤
      quadraticForm workingCovariance⁻¹ (mean - controls *ᵥ fixedControl) / information := by
  let residualMean : ι → ℝ := mean - controls *ᵥ fixedControl
  have hscore : outcomeWeight ⬝ᵥ mean = outcomeWeight ⬝ᵥ residualMean := by
    dsimp [residualMean]
    rw [dotProduct_sub, hcontrols]
    ring
  have hprecision : workingCovariance⁻¹.PosDef := hworking.inv
  have hcauchy := normalized_precision_score_sq_le_energy_div_information
    hprecision (workingCovariance *ᵥ outcomeWeight) residualMean
    (by
      rw [quadraticForm_inverse_working_mulVec_eq hworking outcomeWeight]
      exact hweight_norm)
  rw [workingCovariance_dual_score_eq hworking outcomeWeight residualMean] at hcauchy
  rw [hscore]
  simpa only [residualMean] using hcauchy

end InfillGLSLean
