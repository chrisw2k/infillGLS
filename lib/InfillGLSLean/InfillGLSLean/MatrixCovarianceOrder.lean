module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Ring

/-!
# Matrix covariance-order bounds for GLS scores

This module gives the finite-dimensional Loewner-order step behind the
covariance contribution in the manuscript's MSE bound.  It is deliberately
deterministic: a separate probability layer identifies a score variance with
the covariance quadratic form used here.
-/

public section

namespace InfillGLSLean

open Matrix

variable {ι : Type*} [Fintype ι]

/-- The real quadratic form associated with a finite square matrix. -/
@[expose]
noncomputable def quadraticForm (matrix : Matrix ι ι ℝ) (vector : ι → ℝ) : ℝ :=
  vector ⬝ᵥ (matrix *ᵥ vector)

/-- Public expansion rule for the quadratic form.  Keeping this lemma explicit
makes the finite-matrix API usable from other Lean modules even when module
definitions are opaque across an import boundary. -/
@[simp]
theorem quadraticForm_eq_dotProduct_mulVec (matrix : Matrix ι ι ℝ)
    (vector : ι → ℝ) :
    quadraticForm matrix vector = vector ⬝ᵥ (matrix *ᵥ vector) :=
  rfl

/-- A positive semidefinite matrix has a nonnegative quadratic form. -/
theorem quadraticForm_nonneg {matrix : Matrix ι ι ℝ}
    (hmatrix : matrix.PosSemidef) (vector : ι → ℝ) :
    0 ≤ quadraticForm matrix vector := by
  simpa [quadraticForm] using hmatrix.dotProduct_mulVec_nonneg vector

/-- If `upper - lower` is positive semidefinite, every quadratic form of
`lower` is bounded by the corresponding quadratic form of `upper`. -/
theorem quadraticForm_mono_of_posSemidef_sub
    {lower upper : Matrix ι ι ℝ} (horder : (upper - lower).PosSemidef)
    (vector : ι → ℝ) :
    quadraticForm lower vector ≤ quadraticForm upper vector := by
  have hnonneg := horder.dotProduct_mulVec_nonneg vector
  change 0 ≤ vector ⬝ᵥ ((upper - lower) *ᵥ vector) at hnonneg
  rw [sub_mulVec, dotProduct_sub] at hnonneg
  change vector ⬝ᵥ (lower *ᵥ vector) ≤ vector ⬝ᵥ (upper *ᵥ vector)
  linarith

/-- Scaling a covariance matrix scales its score variance by the same scalar. -/
theorem quadraticForm_smul (scale : ℝ) (matrix : Matrix ι ι ℝ)
    (vector : ι → ℝ) :
    quadraticForm (scale • matrix) vector = scale * quadraticForm matrix vector := by
  unfold quadraticForm
  rw [smul_mulVec]
  simp only [dotProduct, Pi.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Matrix Cauchy--Schwarz for a positive-definite precision matrix. -/
theorem precision_score_sq_le_quadraticForms
    {precision : Matrix ι ι ℝ} (hprecision : precision.PosDef)
    (left right : ι → ℝ) :
    (left ⬝ᵥ (precision *ᵥ right)) ^ 2 ≤
      quadraticForm precision left * quadraticForm precision right := by
  simpa [quadraticForm, pow_two] using
    hprecision.star_dotProduct_mulVec_mul_le left right

/-- The normalized Cauchy--Schwarz bound for a GLS outcome weight.  When its
working quadratic form is `1 / information`, the squared score against a
mean vector is bounded by that mean vector's precision energy divided by the
information. -/
theorem normalized_precision_score_sq_le_energy_div_information
    {precision : Matrix ι ι ℝ} {information : ℝ}
    (hprecision : precision.PosDef) (weight mean : ι → ℝ)
    (hweight : quadraticForm precision weight = 1 / information) :
    (weight ⬝ᵥ (precision *ᵥ mean)) ^ 2 ≤
      quadraticForm precision mean / information := by
  calc
    (weight ⬝ᵥ (precision *ᵥ mean)) ^ 2 ≤
        quadraticForm precision weight * quadraticForm precision mean :=
      precision_score_sq_le_quadraticForms hprecision weight mean
    _ = quadraticForm precision mean / information := by
      rw [hweight]
      ring

/-- A matrix covariance upper bound transfers to the variance of every fixed
linear score.  This is the exact finite matrix counterpart of the covariance
term in equation `eq:mse-bound`. -/
theorem quadraticForm_le_scale_of_posSemidef_sub
    {truth working : Matrix ι ι ℝ} {scale : ℝ}
    (horder : (scale • working - truth).PosSemidef) (weight : ι → ℝ) :
    quadraticForm truth weight ≤ scale * quadraticForm working weight := by
  calc
    quadraticForm truth weight ≤ quadraticForm (scale • working) weight :=
      quadraticForm_mono_of_posSemidef_sub horder weight
    _ = scale * quadraticForm working weight :=
      quadraticForm_smul scale working weight

/-- The working covariance-normalized version used for GLS outcome weights.
If a weight vector has working quadratic form `1 / information`, covariance
order bounds its true quadratic form by `scale / information`. -/
theorem quadraticForm_le_scale_div_information
    {truth working : Matrix ι ι ℝ} {scale information : ℝ}
    (horder : (scale • working - truth).PosSemidef) (weight : ι → ℝ)
    (hweight : quadraticForm working weight = 1 / information) :
    quadraticForm truth weight ≤ scale / information := by
  calc
    quadraticForm truth weight ≤ scale * quadraticForm working weight :=
      quadraticForm_le_scale_of_posSemidef_sub horder weight
    _ = scale / information := by rw [hweight]; simp [div_eq_mul_inv]

/-- A two-sided finite covariance order transfers to a two-sided bound on a
working-covariance-normalized score.  This is the deterministic covariance
sandwich used before taking the Gaussian limit in the inference result. -/
theorem quadraticForm_sandwich_div_information
    {truth working : Matrix ι ι ℝ} {lower upper information : ℝ}
    (hlower : (truth - lower • working).PosSemidef)
    (hupper : (upper • working - truth).PosSemidef) (weight : ι → ℝ)
    (hweight : quadraticForm working weight = 1 / information) :
    lower / information ≤ quadraticForm truth weight ∧
      quadraticForm truth weight ≤ upper / information := by
  constructor
  · calc
      lower / information = lower * quadraticForm working weight := by
        rw [hweight]
        ring
      _ = quadraticForm (lower • working) weight :=
        (quadraticForm_smul lower working weight).symm
      _ ≤ quadraticForm truth weight :=
        quadraticForm_mono_of_posSemidef_sub hlower weight
  · exact quadraticForm_le_scale_div_information hupper weight hweight

end InfillGLSLean
