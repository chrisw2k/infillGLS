module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Finite multi-control matrix GLS / Frisch--Waugh--Lovell algebra

Task L-010 records the finite-dimensional multi-control algebra behind the
manuscript's `eq:information` and `eq:FWL`.  The working precision matrix is
an arbitrary real matrix here; positive definiteness is used only where a
strictly positive information denominator is needed.  The control Gram matrix
is assumed nonsingular through its determinant.  Thus the results below are
the exact matrix FWL identities conditional on the usual full-rank design
assumption, rather than an asymptotic claim.
-/

public section

namespace InfillGLSLean

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The multi-control precision-weighted Gram matrix `W' P W`. -/
@[expose]
noncomputable def controlGram (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) : Matrix κ κ ℝ :=
  controls.transpose * precision * controls

/-- The multi-control precision score `W' P v`. -/
@[expose]
noncomputable def controlScore (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (vector : ι → ℝ) : κ → ℝ :=
  controls.transpose *ᵥ (precision *ᵥ vector)

/-- Residualize a vector against all columns of `controls` using precision `P`. -/
@[expose]
noncomputable def residualizeControls (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (vector : ι → ℝ) : ι → ℝ :=
  vector - controls *ᵥ ((controlGram precision controls)⁻¹ *ᵥ
    controlScore precision controls vector)

/-- The residualized-treatment information `Q = r' P r`. -/
@[expose]
noncomputable def controlInformation (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (treatment : ι → ℝ) : ℝ :=
  let residual := residualizeControls precision controls treatment
  residual ⬝ᵥ (precision *ᵥ residual)

/-- The finite multi-control FWL estimator. -/
@[expose]
noncomputable def fwlEstimateControls (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (treatment outcome : ι → ℝ) : ℝ :=
  let residualTreatment := residualizeControls precision controls treatment
  residualTreatment ⬝ᵥ (precision *ᵥ residualizeControls precision controls outcome) /
    controlInformation precision controls treatment

omit [DecidableEq κ] in
/-- Scoring a linear combination of controls produces its control Gram score. -/
theorem controlScore_controls (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (coefficients : κ → ℝ) :
    controlScore precision controls (controls *ᵥ coefficients) =
      controlGram precision controls *ᵥ coefficients := by
  unfold controlScore controlGram
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

omit [Fintype κ] [DecidableEq κ] in
/-- The multi-control score is additive in the scored vector. -/
theorem controlScore_add (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (left right : ι → ℝ) :
    controlScore precision controls (left + right) =
      controlScore precision controls left + controlScore precision controls right := by
  unfold controlScore
  rw [Matrix.mulVec_add, Matrix.mulVec_add]

omit [Fintype κ] [DecidableEq κ] in
/-- The multi-control score is homogeneous in the scored vector. -/
theorem controlScore_smul (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (scalar : ℝ) (vector : ι → ℝ) :
    controlScore precision controls (scalar • vector) =
      scalar • controlScore precision controls vector := by
  unfold controlScore
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]

/-- Multi-control residualization is additive. -/
theorem residualizeControls_add (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (left right : ι → ℝ) :
    residualizeControls precision controls (left + right) =
      residualizeControls precision controls left +
        residualizeControls precision controls right := by
  unfold residualizeControls
  rw [controlScore_add, Matrix.mulVec_add, Matrix.mulVec_add]
  abel

/-- Multi-control residualization is homogeneous. -/
theorem residualizeControls_smul (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (scalar : ℝ) (vector : ι → ℝ) :
    residualizeControls precision controls (scalar • vector) =
      scalar • residualizeControls precision controls vector := by
  unfold residualizeControls
  rw [controlScore_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_sub]

/-- Residualization annihilates every linear combination of controls. -/
theorem residualizeControls_controls (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (coefficients : κ → ℝ)
    (hgram : IsUnit (controlGram precision controls).det) :
    residualizeControls precision controls (controls *ᵥ coefficients) = 0 := by
  unfold residualizeControls
  rw [controlScore_controls]
  calc
    controls *ᵥ coefficients -
        controls *ᵥ ((controlGram precision controls)⁻¹ *ᵥ
          (controlGram precision controls *ᵥ coefficients)) =
      controls *ᵥ coefficients -
        controls *ᵥ (((controlGram precision controls)⁻¹ *
          controlGram precision controls) *ᵥ coefficients) := by
            rw [Matrix.mulVec_mulVec coefficients]
    _ = controls *ᵥ coefficients - controls *ᵥ (1 *ᵥ coefficients) := by
          rw [Matrix.nonsing_inv_mul _ hgram]
    _ = 0 := by simp

/-- Residualization makes the precision score against all controls vanish. -/
theorem controlScore_residualizeControls (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (vector : ι → ℝ)
    (hgram : IsUnit (controlGram precision controls).det) :
    controlScore precision controls (residualizeControls precision controls vector) = 0 := by
  unfold residualizeControls controlScore
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
  change controlScore precision controls vector -
      controlScore precision controls
        (controls *ᵥ ((controlGram precision controls)⁻¹ *ᵥ
          controlScore precision controls vector)) = 0
  rw [controlScore_controls]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv]
  · simp
  · exact hgram

/-- Under a linear outcome model, control residualization removes all controls. -/
theorem residualizeControls_model (precision : Matrix ι ι ℝ)
    (controls : Matrix ι κ ℝ) (treatment outcome error : ι → ℝ)
    (beta : ℝ) (coefficients : κ → ℝ)
    (hgram : IsUnit (controlGram precision controls).det)
    (hmodel : outcome = beta • treatment + controls *ᵥ coefficients + error) :
    residualizeControls precision controls outcome =
      beta • residualizeControls precision controls treatment +
        residualizeControls precision controls error := by
  calc
    residualizeControls precision controls outcome =
        residualizeControls precision controls
          (beta • treatment + controls *ᵥ coefficients + error) := by rw [hmodel]
    _ = residualizeControls precision controls
          (beta • treatment + controls *ᵥ coefficients) +
        residualizeControls precision controls error :=
          residualizeControls_add precision controls
            (beta • treatment + controls *ᵥ coefficients) error
    _ = (residualizeControls precision controls (beta • treatment) +
          residualizeControls precision controls (controls *ᵥ coefficients)) +
        residualizeControls precision controls error := by
          rw [residualizeControls_add]
    _ = (beta • residualizeControls precision controls treatment +
          residualizeControls precision controls (controls *ᵥ coefficients)) +
        residualizeControls precision controls error := by
          rw [residualizeControls_smul]
    _ = beta • residualizeControls precision controls treatment +
        residualizeControls precision controls error := by
          rw [residualizeControls_controls precision controls coefficients hgram]
          simp

/-- Positive-definite precision makes nonzero residualized treatment carry
strictly positive information. -/
theorem controlInformation_pos {precision : Matrix ι ι ℝ}
    (hprecision : precision.PosDef) {controls : Matrix ι κ ℝ}
    {treatment : ι → ℝ}
    (hresidual : residualizeControls precision controls treatment ≠ 0) :
    0 < controlInformation precision controls treatment := by
  unfold controlInformation
  exact hprecision.dotProduct_mulVec_pos hresidual

/-- Hence a nonzero residualized treatment has a nonzero FWL denominator. -/
theorem controlInformation_ne_zero {precision : Matrix ι ι ℝ}
    (hprecision : precision.PosDef) {controls : Matrix ι κ ℝ}
    {treatment : ι → ℝ}
    (hresidual : residualizeControls precision controls treatment ≠ 0) :
    controlInformation precision controls treatment ≠ 0 :=
  ne_of_gt (controlInformation_pos hprecision hresidual)

/--
The finite multi-control FWL estimator equals the target coefficient plus its
residualized precision-weighted error score divided by `Q`.
-/
theorem fwlEstimateControls_error_identity
    (precision : Matrix ι ι ℝ) (controls : Matrix ι κ ℝ)
    (treatment outcome error : ι → ℝ) (beta : ℝ) (coefficients : κ → ℝ)
    (hgram : IsUnit (controlGram precision controls).det)
    (hinformation : controlInformation precision controls treatment ≠ 0)
    (hmodel : outcome = beta • treatment + controls *ᵥ coefficients + error) :
    fwlEstimateControls precision controls treatment outcome =
      beta +
        (residualizeControls precision controls treatment ⬝ᵥ
          (precision *ᵥ residualizeControls precision controls error)) /
          controlInformation precision controls treatment := by
  have hresidual := residualizeControls_model precision controls treatment outcome error
    beta coefficients hgram hmodel
  simp only [fwlEstimateControls]
  rw [hresidual, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul]
  change
    (beta * controlInformation precision controls treatment +
      (residualizeControls precision controls treatment ⬝ᵥ
        (precision *ᵥ residualizeControls precision controls error))) /
        controlInformation precision controls treatment =
      beta +
        (residualizeControls precision controls treatment ⬝ᵥ
          (precision *ᵥ residualizeControls precision controls error)) /
          controlInformation precision controls treatment
  field_simp [hinformation]

/-- The same exact FWL error identity with its denominator discharged by
positive definiteness and nonzero residualized treatment. -/
theorem fwlEstimateControls_error_identity_of_posDef
    (precision : Matrix ι ι ℝ) (controls : Matrix ι κ ℝ)
    (treatment outcome error : ι → ℝ) (beta : ℝ) (coefficients : κ → ℝ)
    (hprecision : precision.PosDef)
    (hresidual : residualizeControls precision controls treatment ≠ 0)
    (hgram : IsUnit (controlGram precision controls).det)
    (hmodel : outcome = beta • treatment + controls *ᵥ coefficients + error) :
    fwlEstimateControls precision controls treatment outcome =
      beta +
        (residualizeControls precision controls treatment ⬝ᵥ
          (precision *ᵥ residualizeControls precision controls error)) /
          controlInformation precision controls treatment := by
  exact fwlEstimateControls_error_identity precision controls treatment outcome error
    beta coefficients hgram (controlInformation_ne_zero hprecision hresidual) hmodel

end InfillGLSLean
