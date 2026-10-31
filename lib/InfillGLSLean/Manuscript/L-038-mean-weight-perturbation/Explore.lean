module

public import InfillGLSLean.GLSBiasBound
public import Mathlib.Tactic

public section

/-!
# Exact finite Cauchy--Schwarz transfer for Appendix `lem:mean`

This file formalizes only the final covariance Cauchy--Schwarz transfer in
the working-weight paragraph of Appendix `lem:mean`.  It neither derives the
preceding perturbation inequality nor changes a manuscript proposition.
-/

namespace InfillGLSLean.MeanWeightPerturbation

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Covariance Cauchy--Schwarz written in the coordinates used by the final
line of Appendix `lem:mean`. -/
theorem covariance_score_sq_le
    {covariance : Matrix I I ℝ} (hcovariance : covariance.PosDef)
    (difference test : I → ℝ) :
    (difference ⬝ᵥ test) ^ 2 ≤
      quadraticForm covariance difference * quadraticForm covariance⁻¹ test := by
  have hcs := precision_score_sq_le_quadraticForms
    hcovariance.inv (covariance *ᵥ difference) test
  rw [quadraticForm_inverse_working_mulVec_eq hcovariance difference,
    workingCovariance_dual_score_eq hcovariance difference test] at hcs
  exact hcs

/-- The scaled finite transfer after any established true-covariance bound on
the working-minus-true GLS weight difference. -/
theorem scaled_covariance_score_sq_le_of_quadratic_bound
    {covariance : Matrix I I ℝ} (hcovariance : covariance.PosDef)
    {scale bound : ℝ} (hscale : 0 ≤ scale)
    (difference test : I → ℝ)
    (hbound : quadraticForm covariance difference ≤ bound) :
    scale * (difference ⬝ᵥ test) ^ 2 ≤
      scale * bound * quadraticForm covariance⁻¹ test := by
  have hcs := covariance_score_sq_le hcovariance difference test
  have hinv_nonneg : 0 ≤ quadraticForm covariance⁻¹ test :=
    quadraticForm_nonneg hcovariance.inv.posSemidef test
  calc
    scale * (difference ⬝ᵥ test) ^ 2 ≤
        scale * (quadraticForm covariance difference * quadraticForm covariance⁻¹ test) :=
      mul_le_mul_of_nonneg_left hcs hscale
    _ ≤ scale * (bound * quadraticForm covariance⁻¹ test) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hbound hinv_nonneg) hscale
    _ = scale * bound * quadraticForm covariance⁻¹ test := by ring

/-- The literal squared covariance-Cauchy--Schwarz transfer used immediately
after equation `eq:working-weight-perturbation` in Appendix `lem:mean`.  The
premise is that exact displayed perturbation inequality; this theorem does
not assert how it is obtained. -/
theorem working_weight_perturbation_score_sq_le
    {covariance : Matrix I I ℝ} (hcovariance : covariance.PosDef)
    {information delta trueSlopeVariance : ℝ} (hinformation : 0 ≤ information)
    (difference test : I → ℝ)
    (hperturbation :
      quadraticForm covariance difference ≤
        (delta ^ 2 / (1 - delta) ^ 2) * trueSlopeVariance) :
    information * (difference ⬝ᵥ test) ^ 2 ≤
      information * ((delta ^ 2 / (1 - delta) ^ 2) * trueSlopeVariance) *
        quadraticForm covariance⁻¹ test := by
  exact scaled_covariance_score_sq_le_of_quadratic_bound hcovariance
    hinformation difference test hperturbation

/-- The scalar division step in the proof of
`eq:working-weight-perturbation`.  Once the first-order conditions have given
the coercive inequality and the relative-error bilinear estimate, this is the
literal `delta^2 / (1-delta)^2` conclusion in the manuscript. -/
theorem relative_perturbation_scalar_bound
    {delta displacementVariance referenceVariance crossTerm : ℝ}
    (hdelta_nonneg : 0 ≤ delta) (hdelta_lt_one : delta < 1)
    (hdisplacement_nonneg : 0 ≤ displacementVariance)
    (href_nonneg : 0 ≤ referenceVariance)
    (hcoercive : (1 - delta) * displacementVariance ≤ -crossTerm)
    (hbilinear : crossTerm ^ 2 ≤
      delta ^ 2 * displacementVariance * referenceVariance) :
    displacementVariance ≤
      (delta ^ 2 / (1 - delta) ^ 2) * referenceVariance := by
  have hdelta_sq_nonneg : 0 ≤ delta ^ 2 := by
    simpa [pow_two] using mul_nonneg hdelta_nonneg hdelta_nonneg
  have hgap_pos : 0 < 1 - delta := by linarith
  have hleft_nonneg : 0 ≤ (1 - delta) * displacementVariance :=
    mul_nonneg (le_of_lt hgap_pos) hdisplacement_nonneg
  have hcross_nonpos : crossTerm ≤ 0 := by linarith
  have hsq : ((1 - delta) * displacementVariance) ^ 2 ≤ crossTerm ^ 2 := by
    have h := (sq_le_sq₀ hleft_nonneg (neg_nonneg.mpr hcross_nonpos)).mpr hcoercive
    simpa using h
  have hproduct :
      displacementVariance * ((1 - delta) ^ 2 * displacementVariance) ≤
        displacementVariance * (delta ^ 2 * referenceVariance) := by
    calc
      displacementVariance * ((1 - delta) ^ 2 * displacementVariance) =
          ((1 - delta) * displacementVariance) ^ 2 := by ring
      _ ≤ crossTerm ^ 2 := hsq
      _ ≤ delta ^ 2 * displacementVariance * referenceVariance := hbilinear
      _ = displacementVariance * (delta ^ 2 * referenceVariance) := by ring
  by_cases hzero : displacementVariance = 0
  · subst displacementVariance
    exact mul_nonneg (div_nonneg hdelta_sq_nonneg (sq_nonneg _)) href_nonneg
  have hdisplacement_pos : 0 < displacementVariance :=
    lt_of_le_of_ne hdisplacement_nonneg (Ne.symm hzero)
  have hcore : (1 - delta) ^ 2 * displacementVariance ≤
      delta ^ 2 * referenceVariance :=
    by nlinarith [hproduct]
  have hgap_sq_pos : 0 < (1 - delta) ^ 2 := sq_pos_of_pos hgap_pos
  calc
    displacementVariance =
        ((1 - delta) ^ 2 * displacementVariance) / (1 - delta) ^ 2 := by
          field_simp [hgap_sq_pos.ne']
    _ ≤ (delta ^ 2 * referenceVariance) / (1 - delta) ^ 2 :=
      div_le_div_of_nonneg_right hcore (le_of_lt hgap_sq_pos)
    _ = (delta ^ 2 / (1 - delta) ^ 2) * referenceVariance := by ring

/-- The finite coordinate consequence of the paper's statement
`‖E‖_{op} ≤ δ`: after applying `E` to a vector, its squared Euclidean norm
is at most `δ²` times the original squared norm.  This lemma is the ordinary
Euclidean Cauchy--Schwarz step that turns that bound into the displayed
bilinear estimate `|d' E a| ≤ δ ‖d‖ ‖a‖`, in squared form. -/
theorem relative_error_bilinear_sq_le_of_l2_bound
    {relativeError : Matrix I I ℝ} {delta : ℝ}
    (difference reference : I → ℝ)
    (hoperator : ∀ vector : I → ℝ,
      (relativeError *ᵥ vector) ⬝ᵥ (relativeError *ᵥ vector) ≤
        delta ^ 2 * (vector ⬝ᵥ vector)) :
    (difference ⬝ᵥ (relativeError *ᵥ reference)) ^ 2 ≤
      delta ^ 2 * (difference ⬝ᵥ difference) * (reference ⬝ᵥ reference) := by
  have hdifference_nonneg : 0 ≤ difference ⬝ᵥ difference := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (difference i)
  have hone : (1 : Matrix I I ℝ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos isHermitian_one ?_
    intro vector hvector
    rw [one_mulVec]
    obtain ⟨i, hi⟩ : ∃ i, vector i ≠ 0 := by
      by_contra! hzero
      apply hvector
      funext j
      exact hzero j
    unfold dotProduct
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (vector j))
      ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩
  have hcauchy := precision_score_sq_le_quadraticForms
    hone
    difference (relativeError *ᵥ reference)
  have hcauchy' :
      (difference ⬝ᵥ (relativeError *ᵥ reference)) ^ 2 ≤
        (difference ⬝ᵥ difference) *
          ((relativeError *ᵥ reference) ⬝ᵥ (relativeError *ᵥ reference)) := by
    simpa only [quadraticForm_eq_dotProduct_mulVec, one_mulVec] using hcauchy
  calc
    (difference ⬝ᵥ (relativeError *ᵥ reference)) ^ 2 ≤
        (difference ⬝ᵥ difference) *
          ((relativeError *ᵥ reference) ⬝ᵥ (relativeError *ᵥ reference)) :=
      hcauchy'
    _ ≤ (difference ⬝ᵥ difference) *
          (delta ^ 2 * (reference ⬝ᵥ reference)) :=
      mul_le_mul_of_nonneg_left (hoperator reference) hdifference_nonneg
    _ = delta ^ 2 * (difference ⬝ᵥ difference) * (reference ⬝ᵥ reference) := by
      ring

/-- Congruence preserves the lower half of the covariance sandwich in the
whitened coordinates of the transfer paragraph.  In the manuscript take
`truth = Σ`, `working = σ² K`, and `whitening = Σ⁻¹ᐟ²`; the normalization
premise is the defining identity for those coordinates. -/
theorem relative_error_lower_sandwich_of_covariance_lower_sandwich
    {truth working whitening : Matrix I I ℝ} {delta : ℝ}
    (hnormalize : whiteningᵀ * truth * whitening = 1)
    (hlower : (working - (1 - delta) • truth).PosSemidef) :
    (delta • (1 : Matrix I I ℝ) +
      whiteningᵀ * (working - truth) * whitening).PosSemidef := by
  have hcongr := hlower.conjTranspose_mul_mul_same whitening
  have herror :
      whiteningᵀ * (working - truth) * whitening =
        whiteningᵀ * working * whitening - whiteningᵀ * truth * whitening := by
    rw [mul_sub, sub_mul]
  have hscaled :
      whiteningᵀ * ((1 - delta) • truth) * whitening =
        (1 - delta) • (whiteningᵀ * truth * whitening) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hworking :
      whiteningᵀ * (working - (1 - delta) • truth) * whitening =
        whiteningᵀ * working * whitening -
          (1 - delta) • (whiteningᵀ * truth * whitening) := by
    rw [mul_sub, sub_mul, hscaled]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hcongr
  rw [hworking, hnormalize] at hcongr
  rw [herror, hnormalize]
  have hmatrix :
      delta • (1 : Matrix I I ℝ) +
          (whiteningᵀ * working * whitening - (1 : Matrix I I ℝ)) =
        whiteningᵀ * working * whitening -
          (1 - delta) • (1 : Matrix I I ℝ) := by
    rw [← one_smul ℝ (1 : Matrix I I ℝ)]
    module
  rw [hmatrix]
  exact hcongr

/-- Congruence preserves the upper half of the covariance sandwich in the
same whitened coordinates.  Together with the preceding lemma this is the
literal Loewner-order input for the paper's claim `‖E‖op ≤ δ`. -/
theorem relative_error_upper_sandwich_of_covariance_upper_sandwich
    {truth working whitening : Matrix I I ℝ} {delta : ℝ}
    (hnormalize : whiteningᵀ * truth * whitening = 1)
    (hupper : ((1 + delta) • truth - working).PosSemidef) :
    (delta • (1 : Matrix I I ℝ) -
      whiteningᵀ * (working - truth) * whitening).PosSemidef := by
  have hcongr := hupper.conjTranspose_mul_mul_same whitening
  have herror :
      whiteningᵀ * (working - truth) * whitening =
        whiteningᵀ * working * whitening - whiteningᵀ * truth * whitening := by
    rw [mul_sub, sub_mul]
  have hscaled :
      whiteningᵀ * ((1 + delta) • truth) * whitening =
        (1 + delta) • (whiteningᵀ * truth * whitening) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hworking :
      whiteningᵀ * ((1 + delta) • truth - working) * whitening =
        (1 + delta) • (whiteningᵀ * truth * whitening) -
          whiteningᵀ * working * whitening := by
    rw [mul_sub, sub_mul, hscaled]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hcongr
  rw [hworking, hnormalize] at hcongr
  rw [herror, hnormalize]
  have hmatrix :
      delta • (1 : Matrix I I ℝ) -
          (whiteningᵀ * working * whitening - (1 : Matrix I I ℝ)) =
        (1 + delta) • (1 : Matrix I I ℝ) -
          whiteningᵀ * working * whitening := by
    rw [← one_smul ℝ (1 : Matrix I I ℝ)]
    module
  rw [hmatrix]
  exact hcongr

/-- Each half of the relative-error Loewner sandwich bounds the corresponding
quadratic form.  This is the finite real form of the manuscript's
`‖E‖op ≤ δ` premise before polarization. -/
theorem relative_error_quadratic_bounds_of_sandwich
    {relativeError : Matrix I I ℝ} {delta : ℝ}
    (hlower : (delta • (1 : Matrix I I ℝ) + relativeError).PosSemidef)
    (hupper : (delta • (1 : Matrix I I ℝ) - relativeError).PosSemidef)
    (vector : I → ℝ) :
    -(delta * (vector ⬝ᵥ vector)) ≤ vector ⬝ᵥ (relativeError *ᵥ vector) ∧
      vector ⬝ᵥ (relativeError *ᵥ vector) ≤ delta * (vector ⬝ᵥ vector) := by
  have hupper_nonneg := hupper.dotProduct_mulVec_nonneg vector
  have hlower_nonneg := hlower.dotProduct_mulVec_nonneg vector
  have hupper_rewrite :
      star vector ⬝ᵥ ((delta • (1 : Matrix I I ℝ) - relativeError) *ᵥ vector) =
        delta * (vector ⬝ᵥ vector) - vector ⬝ᵥ (relativeError *ᵥ vector) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, one_mulVec,
      dotProduct_sub, dotProduct_smul]
    simp only [star_trivial, smul_eq_mul]
  have hlower_rewrite :
      star vector ⬝ᵥ ((delta • (1 : Matrix I I ℝ) + relativeError) *ᵥ vector) =
        delta * (vector ⬝ᵥ vector) + vector ⬝ᵥ (relativeError *ᵥ vector) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, one_mulVec,
      dotProduct_add, dotProduct_smul]
    simp only [star_trivial, smul_eq_mul]
  rw [hupper_rewrite] at hupper_nonneg
  rw [hlower_rewrite] at hlower_nonneg
  constructor <;> linarith

/- The finite real polarization identity used to obtain the bilinear
operator bound from the two relative-error quadratic-form bounds. -/
omit [DecidableEq I] in
theorem relative_error_polarization_identity
    {relativeError : Matrix I I ℝ}
    (hhermitian : relativeError.IsHermitian)
    (difference reference : I → ℝ) (scale : ℝ) :
    4 * scale * (difference ⬝ᵥ (relativeError *ᵥ reference)) =
      (scale • difference + reference) ⬝ᵥ
          (relativeError *ᵥ (scale • difference + reference)) -
        (scale • difference - reference) ⬝ᵥ
          (relativeError *ᵥ (scale • difference - reference)) := by
  have hcross : difference ⬝ᵥ (relativeError *ᵥ reference) =
      reference ⬝ᵥ (relativeError *ᵥ difference) := by
    simpa using hhermitian.star_dotProduct_mulVec_comm difference reference
  simp only [mulVec_add, mulVec_sub, Matrix.mulVec_smul,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
    smul_dotProduct, dotProduct_smul]
  rw [hcross]
  ring

/-- The one-dimensional minimization in the polarization proof.  Choosing
`scale = sqrt (rightNorm / leftNorm)` gives the exact product coefficient;
no rate or approximation is used. -/
theorem relative_error_scalar_bilinear_bound_of_polarization
    {delta leftNorm rightNorm crossTerm : ℝ}
    (hdelta : 0 ≤ delta) (hleft : 0 < leftNorm) (hright : 0 < rightNorm)
    (hpolar : ∀ scale : ℝ, 0 < scale →
      -(2 * delta * (scale ^ 2 * leftNorm + rightNorm)) ≤ 4 * scale * crossTerm ∧
        4 * scale * crossTerm ≤ 2 * delta * (scale ^ 2 * leftNorm + rightNorm)) :
    crossTerm ^ 2 ≤ delta ^ 2 * leftNorm * rightNorm := by
  let scale : ℝ := √(rightNorm / leftNorm)
  have hratio_pos : 0 < rightNorm / leftNorm := div_pos hright hleft
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact Real.sqrt_pos.mpr hratio_pos
  have hscale_sq : scale ^ 2 = rightNorm / leftNorm := by
    dsimp [scale]
    exact Real.sq_sqrt hratio_pos.le
  have hscale_sq_mul : scale ^ 2 * leftNorm = rightNorm := by
    rw [hscale_sq]
    field_simp [hleft.ne']
  have hpolar_scale := hpolar scale hscale_pos
  have hscaled_lower : -(delta * rightNorm) ≤ scale * crossTerm := by
    nlinarith [hpolar_scale.1, hscale_sq_mul]
  have hscaled_upper : scale * crossTerm ≤ delta * rightNorm := by
    nlinarith [hpolar_scale.2, hscale_sq_mul]
  have hdelta_right_nonneg : 0 ≤ delta * rightNorm :=
    mul_nonneg hdelta hright.le
  have hproduct_nonneg : 0 ≤
      (delta * rightNorm - scale * crossTerm) *
        (delta * rightNorm + scale * crossTerm) :=
    mul_nonneg (by linarith) (by linarith)
  have hscaled_sq : (scale * crossTerm) ^ 2 ≤ (delta * rightNorm) ^ 2 := by
    nlinarith [hproduct_nonneg]
  have hscale_sq_pos : 0 < scale ^ 2 := sq_pos_of_pos hscale_pos
  apply le_of_mul_le_mul_left ?_ hscale_sq_pos
  calc
    scale ^ 2 * crossTerm ^ 2 = (scale * crossTerm) ^ 2 := by ring
    _ ≤ (delta * rightNorm) ^ 2 := hscaled_sq
    _ = delta ^ 2 * (scale ^ 2 * leftNorm) * rightNorm := by
      rw [hscale_sq_mul]
      ring
    _ = scale ^ 2 * (delta ^ 2 * leftNorm * rightNorm) := by ring

/-- The exact finite real-symmetric support lemma for the manuscript's
sentence "The covariance bounds give `‖E‖op ≤ δ`".  It uses both literal PSD
inequalities `δ I + E ⪰ 0` and `δ I - E ⪰ 0`, whose Hermitian property is
already part of `PosSemidef`, and concludes precisely the squared bilinear
bound used in the next displayed line of Appendix `lem:mean`. -/
theorem relative_error_bilinear_sq_le_of_sandwich
    {relativeError : Matrix I I ℝ} {delta : ℝ}
    (hlower : (delta • (1 : Matrix I I ℝ) + relativeError).PosSemidef)
    (hupper : (delta • (1 : Matrix I I ℝ) - relativeError).PosSemidef)
    (difference reference : I → ℝ) :
    (difference ⬝ᵥ (relativeError *ᵥ reference)) ^ 2 ≤
      delta ^ 2 * (difference ⬝ᵥ difference) * (reference ⬝ᵥ reference) := by
  by_cases hdifference_zero : difference = 0
  · subst difference
    simp
  by_cases hreference_zero : reference = 0
  · subst reference
    simp
  have hdiff_nonneg : 0 ≤ difference ⬝ᵥ difference := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (difference i)
  have href_nonneg : 0 ≤ reference ⬝ᵥ reference := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (reference i)
  have hdiff_sq_ne : difference ⬝ᵥ difference ≠ 0 := by
    intro hzero
    exact hdifference_zero (dotProduct_self_eq_zero.mp hzero)
  have href_sq_ne : reference ⬝ᵥ reference ≠ 0 := by
    intro hzero
    exact hreference_zero (dotProduct_self_eq_zero.mp hzero)
  have hdiff_pos : 0 < difference ⬝ᵥ difference :=
    lt_of_le_of_ne hdiff_nonneg (Ne.symm hdiff_sq_ne)
  have href_pos : 0 < reference ⬝ᵥ reference :=
    lt_of_le_of_ne href_nonneg (Ne.symm href_sq_ne)
  have hquadratic := relative_error_quadratic_bounds_of_sandwich hlower hupper
  have hdelta_nonneg : 0 ≤ delta := by
    have htest := hquadratic difference
    nlinarith [htest.1, htest.2]
  have hscalar_hermitian : (delta • (1 : Matrix I I ℝ)).IsHermitian :=
    isHermitian_one.smul (star_trivial delta)
  have hhermitian : relativeError.IsHermitian := by
    rw [← sub_sub_cancel (delta • (1 : Matrix I I ℝ)) relativeError]
    exact hscalar_hermitian.sub hupper.isHermitian
  have hpolar : ∀ scale : ℝ, 0 < scale →
      -(2 * delta * (scale ^ 2 * (difference ⬝ᵥ difference) +
        (reference ⬝ᵥ reference))) ≤
        4 * scale * (difference ⬝ᵥ (relativeError *ᵥ reference)) ∧
      4 * scale * (difference ⬝ᵥ (relativeError *ᵥ reference)) ≤
        2 * delta * (scale ^ 2 * (difference ⬝ᵥ difference) +
          (reference ⬝ᵥ reference)) := by
    intro scale _
    have hplus := hquadratic (scale • difference + reference)
    have hminus := hquadratic (scale • difference - reference)
    have hpolarization := relative_error_polarization_identity
      hhermitian difference reference scale
    have hnorm_sum :
        ((scale • difference + reference) ⬝ᵥ (scale • difference + reference)) +
          ((scale • difference - reference) ⬝ᵥ (scale • difference - reference)) =
          2 * (scale ^ 2 * (difference ⬝ᵥ difference) +
            (reference ⬝ᵥ reference)) := by
      simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
        smul_dotProduct, dotProduct_smul]
      ring
    have hdelta_norm_sum :
        delta * ((scale • difference + reference) ⬝ᵥ
            (scale • difference + reference)) +
          delta * ((scale • difference - reference) ⬝ᵥ
            (scale • difference - reference)) =
          2 * delta * (scale ^ 2 * (difference ⬝ᵥ difference) +
            (reference ⬝ᵥ reference)) := by
      calc
        delta * ((scale • difference + reference) ⬝ᵥ
            (scale • difference + reference)) +
            delta * ((scale • difference - reference) ⬝ᵥ
              (scale • difference - reference)) =
            delta * (((scale • difference + reference) ⬝ᵥ
              (scale • difference + reference)) +
              ((scale • difference - reference) ⬝ᵥ
                (scale • difference - reference))) := by ring
        _ = delta * (2 * (scale ^ 2 * (difference ⬝ᵥ difference) +
            (reference ⬝ᵥ reference))) := by rw [hnorm_sum]
        _ = 2 * delta * (scale ^ 2 * (difference ⬝ᵥ difference) +
            (reference ⬝ᵥ reference)) := by ring
    constructor
    · calc
        -(2 * delta * (scale ^ 2 * (difference ⬝ᵥ difference) +
            (reference ⬝ᵥ reference))) =
            -(delta * ((scale • difference + reference) ⬝ᵥ
              (scale • difference + reference)) +
              delta * ((scale • difference - reference) ⬝ᵥ
                (scale • difference - reference))) := by
              rw [hdelta_norm_sum]
        _ ≤ (scale • difference + reference) ⬝ᵥ
              (relativeError *ᵥ (scale • difference + reference)) -
            (scale • difference - reference) ⬝ᵥ
              (relativeError *ᵥ (scale • difference - reference)) := by
              linarith [hplus.1, hminus.2]
        _ = 4 * scale * (difference ⬝ᵥ (relativeError *ᵥ reference)) :=
          hpolarization.symm
    · calc
        4 * scale * (difference ⬝ᵥ (relativeError *ᵥ reference)) =
            (scale • difference + reference) ⬝ᵥ
              (relativeError *ᵥ (scale • difference + reference)) -
            (scale • difference - reference) ⬝ᵥ
              (relativeError *ᵥ (scale • difference - reference)) :=
          hpolarization
        _ ≤ delta * ((scale • difference + reference) ⬝ᵥ
              (scale • difference + reference)) +
              delta * ((scale • difference - reference) ⬝ᵥ
                (scale • difference - reference)) := by
              linarith [hplus.2, hminus.1]
        _ = 2 * delta * (scale ^ 2 * (difference ⬝ᵥ difference) +
            (reference ⬝ᵥ reference)) := hdelta_norm_sum
  exact relative_error_scalar_bilinear_bound_of_polarization
    hdelta_nonneg hdiff_pos href_pos hpolar

/-- The first-order-condition reduction in the proof of
`eq:working-weight-perturbation`.  This keeps the whitened relative-error
matrix explicit.  The bilinear premise is exactly the operator-norm estimate
for that matrix used in the paper; the preceding
`relative_error_bilinear_sq_le_of_sandwich` discharges it from the literal
two-sided relative-error PSD sandwich. -/
theorem relative_perturbation_bound_of_stationarity
    {relativeError : Matrix I I ℝ}
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_lt_one : delta < 1)
    (hlower :
      ((1 : Matrix I I ℝ) + relativeError -
        (1 - delta) • (1 : Matrix I I ℝ)).PosSemidef)
    (reference difference : I → ℝ)
    (horthogonal : difference ⬝ᵥ reference = 0)
    (hstationary : difference ⬝ᵥ
      (((1 : Matrix I I ℝ) + relativeError) *ᵥ (reference + difference)) = 0)
    (hbilinear :
      (difference ⬝ᵥ (relativeError *ᵥ reference)) ^ 2 ≤
        delta ^ 2 * (difference ⬝ᵥ difference) * (reference ⬝ᵥ reference)) :
    difference ⬝ᵥ difference ≤
      (delta ^ 2 / (1 - delta) ^ 2) * (reference ⬝ᵥ reference) := by
  have hdiff_nonneg : 0 ≤ difference ⬝ᵥ difference := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (difference i)
  have href_nonneg : 0 ≤ reference ⬝ᵥ reference := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (reference i)
  have hquadratic_lower := quadraticForm_mono_of_posSemidef_sub hlower difference
  have hlower_score :
      (1 - delta) * (difference ⬝ᵥ difference) ≤
        difference ⬝ᵥ (((1 : Matrix I I ℝ) + relativeError) *ᵥ difference) := by
    calc
      (1 - delta) * (difference ⬝ᵥ difference) =
          quadraticForm ((1 - delta) • (1 : Matrix I I ℝ)) difference := by
            rw [quadraticForm_smul, quadraticForm_eq_dotProduct_mulVec, one_mulVec]
      _ ≤ quadraticForm ((1 : Matrix I I ℝ) + relativeError) difference :=
        hquadratic_lower
      _ = difference ⬝ᵥ (((1 : Matrix I I ℝ) + relativeError) *ᵥ difference) :=
        quadraticForm_eq_dotProduct_mulVec _ _
  have hstationary_expanded :
      difference ⬝ᵥ reference +
        difference ⬝ᵥ (relativeError *ᵥ reference) +
        (difference ⬝ᵥ difference + difference ⬝ᵥ (relativeError *ᵥ difference)) = 0 := by
    calc
      difference ⬝ᵥ reference +
          difference ⬝ᵥ (relativeError *ᵥ reference) +
          (difference ⬝ᵥ difference + difference ⬝ᵥ (relativeError *ᵥ difference)) =
          difference ⬝ᵥ (((1 : Matrix I I ℝ) + relativeError) *ᵥ
            (reference + difference)) := by
              simp only [mulVec_add, add_mulVec, one_mulVec, dotProduct_add]
      _ = 0 := hstationary
  have hstationary_difference :
      difference ⬝ᵥ (((1 : Matrix I I ℝ) + relativeError) *ᵥ difference) =
        -(difference ⬝ᵥ (relativeError *ᵥ reference)) := by
    rw [add_mulVec, one_mulVec, dotProduct_add]
    linarith [hstationary_expanded, horthogonal]
  exact relative_perturbation_scalar_bound hdelta_nonneg hdelta_lt_one
    hdiff_nonneg href_nonneg
    (by simpa [hstationary_difference] using hlower_score)
    hbilinear

/-- The exact finite working-weight perturbation inequality in the paper's
whitened variables.  Its hypotheses are precisely the two relative-error
Loewner inequalities and the two first-order conditions displayed in the
transfer paragraph of Appendix `lem:mean`; it concludes the manuscript's
coefficient `δ²/(1-δ)²` without an asymptotic replacement. -/
theorem relative_perturbation_bound_of_sandwich_and_stationarity
    {relativeError : Matrix I I ℝ}
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_lt_one : delta < 1)
    (hlower : (delta • (1 : Matrix I I ℝ) + relativeError).PosSemidef)
    (hupper : (delta • (1 : Matrix I I ℝ) - relativeError).PosSemidef)
    (reference difference : I → ℝ)
    (horthogonal : difference ⬝ᵥ reference = 0)
    (hstationary : difference ⬝ᵥ
      (((1 : Matrix I I ℝ) + relativeError) *ᵥ (reference + difference)) = 0) :
    difference ⬝ᵥ difference ≤
      (delta ^ 2 / (1 - delta) ^ 2) * (reference ⬝ᵥ reference) := by
  have hstationarity_lower :
      ((1 : Matrix I I ℝ) + relativeError -
        (1 - delta) • (1 : Matrix I I ℝ)).PosSemidef := by
    have hmatrix :
        (1 : Matrix I I ℝ) + relativeError -
            (1 - delta) • (1 : Matrix I I ℝ) =
          delta • (1 : Matrix I I ℝ) + relativeError := by
      rw [← one_smul ℝ (1 : Matrix I I ℝ)]
      module
    rw [hmatrix]
    exact hlower
  exact relative_perturbation_bound_of_stationarity
    hdelta_nonneg hdelta_lt_one hstationarity_lower reference difference
    horthogonal hstationary
    (relative_error_bilinear_sq_le_of_sandwich hlower hupper difference reference)

end InfillGLSLean.MeanWeightPerturbation
