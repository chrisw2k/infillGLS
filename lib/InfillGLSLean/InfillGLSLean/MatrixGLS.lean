module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.FieldSimp

/-!
# Finite full-matrix GLS foundations

This module records the deterministic, no-control part of GLS over a finite
index type.  The covariance matrix is a real positive-definite matrix, so its
nonsingular inverse is a legitimate precision matrix.  This is deliberately
finite-dimensional: it does not formalize stochastic covariance, controls,
or an infill limit.
-/

public section

namespace InfillGLSLean

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The GLS information for one treatment vector and a full covariance matrix. -/
noncomputable def inverseInformation (covariance : Matrix ι ι ℝ)
    (treatment : ι → ℝ) : ℝ :=
  treatment ⬝ᵥ (covariance⁻¹ *ᵥ treatment)

/-- The no-control generalized least-squares coefficient. -/
noncomputable def glsNoControls (covariance : Matrix ι ι ℝ)
    (treatment outcome : ι → ℝ) : ℝ :=
  (treatment ⬝ᵥ (covariance⁻¹ *ᵥ outcome)) /
    inverseInformation covariance treatment

/-- A positive-definite covariance matrix gives strictly positive GLS
information for every nonzero treatment vector. -/
theorem inverseInformation_pos {covariance : Matrix ι ι ℝ}
    (hcovariance : covariance.PosDef) {treatment : ι → ℝ}
    (htreatment : treatment ≠ 0) :
    0 < inverseInformation covariance treatment := by
  unfold inverseInformation
  simpa using hcovariance.inv.dotProduct_mulVec_pos htreatment

/-- Hence the GLS information denominator is nonzero. -/
theorem inverseInformation_ne_zero {covariance : Matrix ι ι ℝ}
    (hcovariance : covariance.PosDef) {treatment : ι → ℝ}
    (htreatment : treatment ≠ 0) :
    inverseInformation covariance treatment ≠ 0 :=
  ne_of_gt (inverseInformation_pos hcovariance htreatment)

/--
Under a no-control linear model, full-matrix GLS equals the target coefficient
plus its precision-weighted error score divided by GLS information.
-/
theorem glsNoControls_error_identity
    (covariance : Matrix ι ι ℝ) (treatment outcome error : ι → ℝ)
    (beta : ℝ)
    (hinformation : inverseInformation covariance treatment ≠ 0)
    (hmodel : outcome = beta • treatment + error) :
    glsNoControls covariance treatment outcome =
      beta +
        (treatment ⬝ᵥ (covariance⁻¹ *ᵥ error)) /
          inverseInformation covariance treatment := by
  unfold glsNoControls
  rw [hmodel, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]
  change
    (beta * inverseInformation covariance treatment +
      treatment ⬝ᵥ (covariance⁻¹ *ᵥ error)) /
        inverseInformation covariance treatment =
      beta +
        (treatment ⬝ᵥ (covariance⁻¹ *ᵥ error)) /
          inverseInformation covariance treatment
  field_simp [hinformation]

/-- The same identity with its nonzero-denominator condition discharged by
positive definiteness of the covariance matrix. -/
theorem glsNoControls_error_identity_of_posDef
    (covariance : Matrix ι ι ℝ) (treatment outcome error : ι → ℝ)
    (beta : ℝ) (hcovariance : covariance.PosDef)
    (htreatment : treatment ≠ 0)
    (hmodel : outcome = beta • treatment + error) :
    glsNoControls covariance treatment outcome =
      beta +
        (treatment ⬝ᵥ (covariance⁻¹ *ᵥ error)) /
          inverseInformation covariance treatment := by
  exact glsNoControls_error_identity covariance treatment outcome error beta
    (inverseInformation_ne_zero hcovariance htreatment) hmodel

/-- In difference form, the finite full-matrix GLS estimation error is exactly
the precision-weighted error score divided by information. -/
theorem glsNoControls_sub_beta_of_posDef
    (covariance : Matrix ι ι ℝ) (treatment outcome error : ι → ℝ)
    (beta : ℝ) (hcovariance : covariance.PosDef)
    (htreatment : treatment ≠ 0)
    (hmodel : outcome = beta • treatment + error) :
    glsNoControls covariance treatment outcome - beta =
      (treatment ⬝ᵥ (covariance⁻¹ *ᵥ error)) /
        inverseInformation covariance treatment := by
  rw [glsNoControls_error_identity_of_posDef covariance treatment outcome error beta
    hcovariance htreatment hmodel]
  ring

end InfillGLSLean
