module

public import «L-038-mean-weight-perturbation».Explore
public import InfillGLSLean.GLSWeightIdentities
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic

public section

/-!
# Literal GLS and whitening bridges for Appendix `lem:mean`

This module proves the source-definition bridges for the
working-weight transfer paragraph in `the source manuscript`, lines 584--602.
It uses the existing literal `glsOutcomeWeight` definition and Mathlib's
positive square root; it does not alter a manuscript proposition, a covariance
assumption, or the whitening construction.
-/

namespace InfillGLSLean.MeanWeightPerturbation

open Matrix
open scoped MatrixOrder

variable {I Kappa : Type*} [Fintype I] [DecidableEq I]
  [Fintype Kappa] [DecidableEq Kappa]

/-- The literal normal equation for the source-defined finite GLS outcome
weight.  This is the finite `A w` form behind the constrained first-order
condition used in Appendix `lem:mean`. -/
theorem source_gls_weight_normal_equation
    (workingCovariance : Matrix I I ℝ) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa ℝ) (treatment : I → ℝ) :
    workingCovariance *ᵥ glsOutcomeWeight workingCovariance controls treatment =
      (controlInformation (Inv.inv workingCovariance) controls treatment)⁻¹ •
        residualizeControls (Inv.inv workingCovariance) controls treatment := by
  let precision : Matrix I I ℝ := Inv.inv workingCovariance
  let residual : I → ℝ :=
    residualizeControls precision controls treatment
  let information : ℝ :=
    controlInformation precision controls treatment
  have hdet : IsUnit workingCovariance.det :=
    (Matrix.isUnit_iff_isUnit_det workingCovariance).mp hworking.isUnit
  have hworking_precision : workingCovariance *ᵥ (precision *ᵥ residual) = residual := by
    calc
      workingCovariance *ᵥ (precision *ᵥ residual) =
          (workingCovariance * precision) *ᵥ residual := by
            rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix I I ℝ) *ᵥ residual := by
            rw [show precision = Inv.inv workingCovariance by rfl]
            rw [Matrix.mul_nonsing_inv workingCovariance hdet]
      _ = residual := by simp
  ext i
  rw [glsOutcomeWeight_eq]
  change Finset.univ.sum (fun j => workingCovariance i j *
    (Inv.inv information * (precision *ᵥ residual) j)) =
      Inv.inv information * residual i
  calc
    Finset.univ.sum (fun j => workingCovariance i j *
        (Inv.inv information * (precision *ᵥ residual) j)) =
        Inv.inv information * Finset.univ.sum (fun j =>
          workingCovariance i j * (precision *ᵥ residual) j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = Inv.inv information *
        (workingCovariance *ᵥ (precision *ᵥ residual)) i := by rfl
    _ = Inv.inv information * residual i := by rw [hworking_precision]

/-- The equality of the GLS objective's directional derivative to zero along
the literal treatment/control constraint set, derived from `glsOutcomeWeight`.
This is exactly the unwhitened first-order condition used in the appendix. -/
theorem source_gls_weight_first_order_condition
    (workingCovariance : Matrix I I ℝ) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa ℝ) (treatment : I → ℝ)
    (hgram : IsUnit
      (controlGram (Inv.inv workingCovariance) controls).det)
    (hresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0))
    (candidate : I → ℝ)
    (hcandidate_treatment : candidate ⬝ᵥ treatment = 1)
    (hcandidate_controls : ∀ coefficients : Kappa → ℝ,
      candidate ⬝ᵥ (controls *ᵥ coefficients) = 0) :
    (candidate - glsOutcomeWeight workingCovariance controls treatment) ⬝ᵥ
      (workingCovariance *ᵥ glsOutcomeWeight workingCovariance controls treatment) = 0 := by
  let coefficients : Kappa → ℝ :=
    (controlGram (Inv.inv workingCovariance) controls)⁻¹ *ᵥ
      controlScore (Inv.inv workingCovariance) controls treatment
  have hweight_treatment :
      glsOutcomeWeight workingCovariance controls treatment ⬝ᵥ treatment = 1 :=
    glsOutcomeWeight_dot_treatment_eq_one workingCovariance hworking controls treatment
      hgram hresidual
  have hweight_controls :
      glsOutcomeWeight workingCovariance controls treatment ⬝ᵥ (controls *ᵥ coefficients) = 0 :=
    glsOutcomeWeight_dot_controls_eq_zero workingCovariance controls treatment hgram coefficients
  have hdifference_residual :
      (candidate - glsOutcomeWeight workingCovariance controls treatment) ⬝ᵥ
        residualizeControls (Inv.inv workingCovariance) controls treatment = 0 := by
    change (candidate - glsOutcomeWeight workingCovariance controls treatment) ⬝ᵥ
        (treatment - controls *ᵥ coefficients) = 0
    simp only [sub_dotProduct, dotProduct_sub]
    rw [hcandidate_treatment, hweight_treatment, hcandidate_controls, hweight_controls]
    ring
  rw [source_gls_weight_normal_equation workingCovariance hworking controls treatment]
  rw [dotProduct_smul, hdifference_residual]
  simp

/-- The two unwhitened first-order identities for the literal true and working
GLS outcome weights in Appendix `lem:mean`. -/
theorem source_two_gls_weights_first_order_conditions
    (truth workingCovariance : Matrix I I ℝ)
    (htruth : truth.PosDef) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa ℝ) (treatment : I → ℝ)
    (htruthgram : IsUnit (controlGram (Inv.inv truth) controls).det)
    (hworkinggram : IsUnit (controlGram (Inv.inv workingCovariance) controls).det)
    (htruthresidual : Not (residualizeControls (Inv.inv truth) controls treatment = 0))
    (hworkingresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0)) :
    let trueWeight := glsOutcomeWeight truth controls treatment
    let workingWeight := glsOutcomeWeight workingCovariance controls treatment
    (workingWeight - trueWeight) ⬝ᵥ (truth *ᵥ trueWeight) = 0 ∧
      (workingWeight - trueWeight) ⬝ᵥ (workingCovariance *ᵥ workingWeight) = 0 := by
  change
    (glsOutcomeWeight workingCovariance controls treatment -
        glsOutcomeWeight truth controls treatment) ⬝ᵥ
        (truth *ᵥ glsOutcomeWeight truth controls treatment) = 0 ∧
      (glsOutcomeWeight workingCovariance controls treatment -
        glsOutcomeWeight truth controls treatment) ⬝ᵥ
        (workingCovariance *ᵥ glsOutcomeWeight workingCovariance controls treatment) = 0
  constructor
  · exact source_gls_weight_first_order_condition truth htruth controls treatment
      htruthgram htruthresidual
      (glsOutcomeWeight workingCovariance controls treatment)
      (glsOutcomeWeight_dot_treatment_eq_one workingCovariance hworking controls treatment
        hworkinggram hworkingresidual)
      (fun coefficients => glsOutcomeWeight_dot_controls_eq_zero
        workingCovariance controls treatment hworkinggram coefficients)
  · have hreverse := source_gls_weight_first_order_condition
      workingCovariance hworking controls treatment hworkinggram hworkingresidual
      (glsOutcomeWeight truth controls treatment)
      (glsOutcomeWeight_dot_treatment_eq_one truth htruth controls treatment
        htruthgram htruthresidual)
      (fun coefficients => glsOutcomeWeight_dot_controls_eq_zero
        truth controls treatment htruthgram coefficients)
    rw [show glsOutcomeWeight workingCovariance controls treatment -
        glsOutcomeWeight truth controls treatment =
        -(glsOutcomeWeight truth controls treatment -
          glsOutcomeWeight workingCovariance controls treatment) by abel]
    rw [neg_dotProduct, hreverse]
    norm_num

/-- The paper's actual `CFC.sqrt truth` whitening transports the two
unwhitened directional first-order conditions into the two displayed
conditions in Appendix `lem:mean`. -/
theorem actual_whitening_transports_first_order_conditions
    {truth workingCovariance : Matrix I I ℝ} (htruth : truth.PosDef)
    (trueWeight workingWeight : I → ℝ)
    (htrue :
      (workingWeight - trueWeight) ⬝ᵥ (truth *ᵥ trueWeight) = 0)
    (hworking :
      (workingWeight - trueWeight) ⬝ᵥ (workingCovariance *ᵥ workingWeight) = 0) :
    let squareRoot := CFC.sqrt truth
    let inverseSquareRoot := squareRoot⁻¹
    let reference := squareRoot *ᵥ trueWeight
    let difference := squareRoot *ᵥ (workingWeight - trueWeight)
    let relativeError := inverseSquareRoot *
      (workingCovariance - truth) * inverseSquareRoot
    difference ⬝ᵥ reference = 0 ∧
      difference ⬝ᵥ ((1 + relativeError) *ᵥ (reference + difference)) = 0 := by
  let squareRoot : Matrix I I ℝ := CFC.sqrt truth
  let inverseSquareRoot : Matrix I I ℝ := squareRoot⁻¹
  change
    (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
        (squareRoot *ᵥ trueWeight) = 0 ∧
      (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
        ((1 + inverseSquareRoot * (workingCovariance - truth) * inverseSquareRoot) *ᵥ
          (squareRoot *ᵥ trueWeight +
            squareRoot *ᵥ (workingWeight - trueWeight))) = 0
  have hroot_psd : squareRoot.PosSemidef := by
    dsimp [squareRoot]
    exact (CFC.sqrt_nonneg truth).posSemidef
  have hroot_hermitian : squareRoot.IsHermitian := hroot_psd.isHermitian
  have hroot_transpose : squareRootᵀ = squareRoot := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hroot_hermitian.eq
  have hroot_unit : IsUnit squareRoot := by
    dsimp [squareRoot]
    exact CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr htruth.isStrictlyPositive
  have hroot_det : IsUnit squareRoot.det :=
    (Matrix.isUnit_iff_isUnit_det squareRoot).mp hroot_unit
  have hroot_square : squareRoot * squareRoot = truth := by
    dsimp [squareRoot]
    exact CFC.sqrt_mul_sqrt_self truth htruth.posSemidef.nonneg
  have hinverse_root_left : inverseSquareRoot * squareRoot = 1 := by
    dsimp [inverseSquareRoot]
    exact Matrix.nonsing_inv_mul squareRoot hroot_det
  have hinverse_root_right : squareRoot * inverseSquareRoot = 1 := by
    dsimp [inverseSquareRoot]
    exact Matrix.mul_nonsing_inv squareRoot hroot_det
  have hinverse_root_truth : inverseSquareRoot * truth = squareRoot := by
    calc
      inverseSquareRoot * truth = inverseSquareRoot *
          (squareRoot * squareRoot) := by rw [hroot_square]
      _ = (inverseSquareRoot * squareRoot) * squareRoot := by
          simp only [Matrix.mul_assoc]
      _ = squareRoot := by rw [hinverse_root_left, one_mul]
  have hfirst_coordinate :
      (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
        (squareRoot *ᵥ trueWeight) =
        (workingWeight - trueWeight) ⬝ᵥ (truth *ᵥ trueWeight) := by
    calc
      (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
          (squareRoot *ᵥ trueWeight) =
          (squareRoot *ᵥ trueWeight) ⬝ᵥ
            (squareRoot *ᵥ (workingWeight - trueWeight)) := dotProduct_comm _ _
      _ = (workingWeight - trueWeight) ⬝ᵥ
          (squareRootᵀ *ᵥ (squareRoot *ᵥ trueWeight)) :=
          (Matrix.dotProduct_transpose_mulVec squareRoot
            (workingWeight - trueWeight) (squareRoot *ᵥ trueWeight)).symm
      _ = (workingWeight - trueWeight) ⬝ᵥ
          ((squareRootᵀ * squareRoot) *ᵥ trueWeight) := by
          rw [Matrix.mulVec_mulVec]
      _ = (workingWeight - trueWeight) ⬝ᵥ (truth *ᵥ trueWeight) := by
          rw [hroot_transpose, hroot_square]
  have hsum_coordinate :
      squareRoot *ᵥ trueWeight +
          squareRoot *ᵥ (workingWeight - trueWeight) =
        squareRoot *ᵥ workingWeight := by
    calc
      squareRoot *ᵥ trueWeight +
          squareRoot *ᵥ (workingWeight - trueWeight) =
          squareRoot *ᵥ (trueWeight + (workingWeight - trueWeight)) :=
          (Matrix.mulVec_add squareRoot trueWeight (workingWeight - trueWeight)).symm
      _ = squareRoot *ᵥ workingWeight := by
          congr 1
          abel
  have hworking_coordinate_matrix :
      (1 + inverseSquareRoot * (workingCovariance - truth) * inverseSquareRoot) *
          squareRoot = inverseSquareRoot * workingCovariance := by
    calc
      (1 + inverseSquareRoot * (workingCovariance - truth) * inverseSquareRoot) *
          squareRoot =
          1 * squareRoot +
            (inverseSquareRoot * (workingCovariance - truth) * inverseSquareRoot) *
              squareRoot := by rw [Matrix.add_mul]
      _ = squareRoot + inverseSquareRoot * (workingCovariance - truth) *
          (inverseSquareRoot * squareRoot) := by
          simp only [Matrix.mul_assoc, one_mul]
      _ = squareRoot + inverseSquareRoot * (workingCovariance - truth) := by
          rw [hinverse_root_left, mul_one]
      _ = squareRoot +
          (inverseSquareRoot * workingCovariance - inverseSquareRoot * truth) := by
          rw [Matrix.mul_sub]
      _ = inverseSquareRoot * workingCovariance := by
          rw [hinverse_root_truth]
          abel
  have hworking_coordinate_vector :
      (1 + inverseSquareRoot * (workingCovariance - truth) * inverseSquareRoot) *ᵥ
          (squareRoot *ᵥ workingWeight) =
        inverseSquareRoot *ᵥ (workingCovariance *ᵥ workingWeight) := by
    calc
      (1 + inverseSquareRoot * (workingCovariance - truth) * inverseSquareRoot) *ᵥ
          (squareRoot *ᵥ workingWeight) =
          ((1 + inverseSquareRoot * (workingCovariance - truth) * inverseSquareRoot) *
            squareRoot) *ᵥ workingWeight := by
              rw [Matrix.mulVec_mulVec]
      _ = (inverseSquareRoot * workingCovariance) *ᵥ workingWeight := by
          rw [hworking_coordinate_matrix]
      _ = inverseSquareRoot *ᵥ (workingCovariance *ᵥ workingWeight) := by
          rw [Matrix.mulVec_mulVec]
  have hsecond_coordinate :
      (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
        (inverseSquareRoot *ᵥ (workingCovariance *ᵥ workingWeight)) =
        (workingWeight - trueWeight) ⬝ᵥ
          (workingCovariance *ᵥ workingWeight) := by
    calc
      (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
          (inverseSquareRoot *ᵥ (workingCovariance *ᵥ workingWeight)) =
          (inverseSquareRoot *ᵥ (workingCovariance *ᵥ workingWeight)) ⬝ᵥ
            (squareRoot *ᵥ (workingWeight - trueWeight)) := dotProduct_comm _ _
      _ = (workingWeight - trueWeight) ⬝ᵥ
          (squareRootᵀ *ᵥ (inverseSquareRoot *ᵥ
            (workingCovariance *ᵥ workingWeight))) :=
          (Matrix.dotProduct_transpose_mulVec squareRoot
            (workingWeight - trueWeight)
            (inverseSquareRoot *ᵥ (workingCovariance *ᵥ workingWeight))).symm
      _ = (workingWeight - trueWeight) ⬝ᵥ
          ((squareRootᵀ * inverseSquareRoot) *ᵥ
            (workingCovariance *ᵥ workingWeight)) := by
          rw [Matrix.mulVec_mulVec]
      _ = (workingWeight - trueWeight) ⬝ᵥ
          ((squareRoot * inverseSquareRoot) *ᵥ
            (workingCovariance *ᵥ workingWeight)) := by
          rw [hroot_transpose]
      _ = (workingWeight - trueWeight) ⬝ᵥ
          (workingCovariance *ᵥ workingWeight) := by
          rw [hinverse_root_right, Matrix.one_mulVec]
  constructor
  · calc
      (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
          (squareRoot *ᵥ trueWeight) =
          (workingWeight - trueWeight) ⬝ᵥ (truth *ᵥ trueWeight) :=
          hfirst_coordinate
      _ = 0 := htrue
  · calc
      (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
          ((1 + inverseSquareRoot * (workingCovariance - truth) * inverseSquareRoot) *ᵥ
            (squareRoot *ᵥ trueWeight +
              squareRoot *ᵥ (workingWeight - trueWeight))) =
          (squareRoot *ᵥ (workingWeight - trueWeight)) ⬝ᵥ
            (inverseSquareRoot *ᵥ (workingCovariance *ᵥ workingWeight)) := by
              rw [hsum_coordinate, hworking_coordinate_vector]
      _ = (workingWeight - trueWeight) ⬝ᵥ
          (workingCovariance *ᵥ workingWeight) := hsecond_coordinate
      _ = 0 := hworking

/-- The exact normalization of the paper's inverse square-root whitening,
derived from a positive-definite finite true covariance. -/
theorem actual_inverse_sqrt_normalizes_covariance
    {truth : Matrix I I ℝ} (htruth : truth.PosDef) :
    let inverseSquareRoot := (CFC.sqrt truth)⁻¹
    inverseSquareRootᵀ * truth * inverseSquareRoot = 1 := by
  dsimp
  let squareRoot : Matrix I I ℝ := CFC.sqrt truth
  have hroot_psd : squareRoot.PosSemidef := by
    dsimp [squareRoot]
    exact (CFC.sqrt_nonneg truth).posSemidef
  have hroot_hermitian : squareRoot.IsHermitian := hroot_psd.isHermitian
  have hroot_inverse_transpose : squareRoot⁻¹ᵀ = squareRoot⁻¹ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hroot_hermitian.inv.eq
  have hroot_unit : IsUnit squareRoot := by
    dsimp [squareRoot]
    exact CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr htruth.isStrictlyPositive
  have hroot_det : IsUnit squareRoot.det :=
    (Matrix.isUnit_iff_isUnit_det squareRoot).mp hroot_unit
  have hroot_square : squareRoot * squareRoot = truth := by
    dsimp [squareRoot]
    exact CFC.sqrt_mul_sqrt_self truth htruth.posSemidef.nonneg
  change squareRoot⁻¹ᵀ * truth * squareRoot⁻¹ = 1
  calc
    squareRoot⁻¹ᵀ * truth * squareRoot⁻¹ =
        squareRoot⁻¹ * (squareRoot * squareRoot) * squareRoot⁻¹ := by
          rw [hroot_inverse_transpose, hroot_square]
    _ = (squareRoot⁻¹ * squareRoot) * squareRoot * squareRoot⁻¹ := by
          simp only [Matrix.mul_assoc]
    _ = squareRoot * squareRoot⁻¹ := by
          rw [Matrix.nonsing_inv_mul squareRoot hroot_det, one_mul]
    _ = 1 := Matrix.mul_nonsing_inv squareRoot hroot_det

/-- For a real positive-definite covariance, the Mathlib principal inverse
square root is symmetric, so the paper's left and right `Sigma^{-1/2}` factors
agree with the congruence form used by the covariance-order lemmas. -/
theorem actual_inverse_sqrt_transpose
    {truth : Matrix I I ℝ} :
    ((CFC.sqrt truth)⁻¹)ᵀ = (CFC.sqrt truth)⁻¹ := by
  have hroot_psd : (CFC.sqrt truth).PosSemidef :=
    (CFC.sqrt_nonneg truth).posSemidef
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hroot_psd.isHermitian.inv.eq

/-- Scaling the working quadratic form by the manuscript's variance scale
does not change its zero directional score at the source-defined working
outcome weight. -/
theorem source_two_gls_weights_first_order_conditions_scaled
    (truth workingCovariance : Matrix I I ℝ)
    (htruth : truth.PosDef) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa ℝ) (treatment : I → ℝ)
    (htruthgram : IsUnit (controlGram (Inv.inv truth) controls).det)
    (hworkinggram : IsUnit (controlGram (Inv.inv workingCovariance) controls).det)
    (htruthresidual : Not (residualizeControls (Inv.inv truth) controls treatment = 0))
    (hworkingresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0))
    (varianceScale : ℝ) :
    let trueWeight := glsOutcomeWeight truth controls treatment
    let workingWeight := glsOutcomeWeight workingCovariance controls treatment
    (workingWeight - trueWeight) ⬝ᵥ (truth *ᵥ trueWeight) = 0 ∧
      (workingWeight - trueWeight) ⬝ᵥ
        ((varianceScale • workingCovariance) *ᵥ workingWeight) = 0 := by
  change
    (glsOutcomeWeight workingCovariance controls treatment -
        glsOutcomeWeight truth controls treatment) ⬝ᵥ
        (truth *ᵥ glsOutcomeWeight truth controls treatment) = 0 ∧
      (glsOutcomeWeight workingCovariance controls treatment -
        glsOutcomeWeight truth controls treatment) ⬝ᵥ
        ((varianceScale • workingCovariance) *ᵥ
          glsOutcomeWeight workingCovariance controls treatment) = 0
  have hbase := source_two_gls_weights_first_order_conditions
    truth workingCovariance htruth hworking controls treatment htruthgram hworkinggram
    htruthresidual hworkingresidual
  constructor
  · exact hbase.1
  · calc
      (glsOutcomeWeight workingCovariance controls treatment -
          glsOutcomeWeight truth controls treatment) ⬝ᵥ
          ((varianceScale • workingCovariance) *ᵥ
            glsOutcomeWeight workingCovariance controls treatment) =
          (glsOutcomeWeight workingCovariance controls treatment -
            glsOutcomeWeight truth controls treatment) ⬝ᵥ
            (varianceScale •
              (workingCovariance *ᵥ glsOutcomeWeight workingCovariance controls treatment)) := by
              rw [Matrix.smul_mulVec]
      _ = varianceScale *
          ((glsOutcomeWeight workingCovariance controls treatment -
            glsOutcomeWeight truth controls treatment) ⬝ᵥ
            (workingCovariance *ᵥ glsOutcomeWeight workingCovariance controls treatment)) := by
              rw [dotProduct_smul]
              rfl
      _ = 0 := by rw [hbase.2, mul_zero]

/-- The two exact first-order identities displayed in Appendix `lem:mean`,
with the paper's actual GLS weights at `truth` and `workingCovariance`, its
variance-scaled working matrix, and the actual CFC inverse-square-root
whitening. -/
theorem source_gls_weights_actual_whitened_first_order_conditions
    (truth workingCovariance : Matrix I I ℝ)
    (htruth : truth.PosDef) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa ℝ) (treatment : I → ℝ)
    (htruthgram : IsUnit (controlGram (Inv.inv truth) controls).det)
    (hworkinggram : IsUnit (controlGram (Inv.inv workingCovariance) controls).det)
    (htruthresidual : Not (residualizeControls (Inv.inv truth) controls treatment = 0))
    (hworkingresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0))
    (varianceScale : ℝ) :
    let trueWeight := glsOutcomeWeight truth controls treatment
    let workingWeight := glsOutcomeWeight workingCovariance controls treatment
    let squareRoot := CFC.sqrt truth
    let inverseSquareRoot := squareRoot⁻¹
    let reference := squareRoot *ᵥ trueWeight
    let difference := squareRoot *ᵥ (workingWeight - trueWeight)
    let relativeError := inverseSquareRoot *
      (varianceScale • workingCovariance - truth) * inverseSquareRoot
    difference ⬝ᵥ reference = 0 ∧
      difference ⬝ᵥ ((1 + relativeError) *ᵥ (reference + difference)) = 0 := by
  change
    let squareRoot := CFC.sqrt truth
    let inverseSquareRoot := squareRoot⁻¹
    let reference := squareRoot *ᵥ glsOutcomeWeight truth controls treatment
    let difference := squareRoot *ᵥ
      (glsOutcomeWeight workingCovariance controls treatment -
        glsOutcomeWeight truth controls treatment)
    let relativeError := inverseSquareRoot *
      (varianceScale • workingCovariance - truth) * inverseSquareRoot
    difference ⬝ᵥ reference = 0 ∧
      difference ⬝ᵥ ((1 + relativeError) *ᵥ (reference + difference)) = 0
  apply actual_whitening_transports_first_order_conditions htruth
    (glsOutcomeWeight truth controls treatment)
    (glsOutcomeWeight workingCovariance controls treatment)
  exact (source_two_gls_weights_first_order_conditions_scaled
    truth workingCovariance htruth hworking controls treatment htruthgram hworkinggram
    htruthresidual hworkingresidual varianceScale).1
  exact (source_two_gls_weights_first_order_conditions_scaled
    truth workingCovariance htruth hworking controls treatment htruthgram hworkinggram
    htruthresidual hworkingresidual varianceScale).2

/-- The same two source-derived first-order conditions with the relative error
written in the exact congruence notation used by the Loewner-sandwich bridge. -/
theorem source_gls_weights_actual_whitened_first_order_conditions_transpose
    (truth workingCovariance : Matrix I I ℝ)
    (htruth : truth.PosDef) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa ℝ) (treatment : I → ℝ)
    (htruthgram : IsUnit (controlGram (Inv.inv truth) controls).det)
    (hworkinggram : IsUnit (controlGram (Inv.inv workingCovariance) controls).det)
    (htruthresidual : Not (residualizeControls (Inv.inv truth) controls treatment = 0))
    (hworkingresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0))
    (varianceScale : ℝ) :
    let trueWeight := glsOutcomeWeight truth controls treatment
    let workingWeight := glsOutcomeWeight workingCovariance controls treatment
    let squareRoot := CFC.sqrt truth
    let inverseSquareRoot := squareRoot⁻¹
    let reference := squareRoot *ᵥ trueWeight
    let difference := squareRoot *ᵥ (workingWeight - trueWeight)
    let relativeError := inverseSquareRootᵀ *
      (varianceScale • workingCovariance - truth) * inverseSquareRoot
    difference ⬝ᵥ reference = 0 ∧
      difference ⬝ᵥ ((1 + relativeError) *ᵥ (reference + difference)) = 0 := by
  simpa only [actual_inverse_sqrt_transpose] using
    (source_gls_weights_actual_whitened_first_order_conditions
      truth workingCovariance htruth hworking controls treatment htruthgram hworkinggram
      htruthresidual hworkingresidual varianceScale)

/-- The Euclidean squared norm after the paper's true-covariance square-root
map is exactly the true-covariance quadratic form. -/
theorem actual_sqrt_dot_eq_quadraticForm
    {truth : Matrix I I ℝ} (htruth : truth.PosDef) (vector : I → ℝ) :
    (CFC.sqrt truth *ᵥ vector) ⬝ᵥ (CFC.sqrt truth *ᵥ vector) =
      quadraticForm truth vector := by
  have hroot_psd : (CFC.sqrt truth).PosSemidef :=
    (CFC.sqrt_nonneg truth).posSemidef
  have hroot_transpose : (CFC.sqrt truth)ᵀ = CFC.sqrt truth := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hroot_psd.isHermitian.eq
  have hroot_square : CFC.sqrt truth * CFC.sqrt truth = truth :=
    CFC.sqrt_mul_sqrt_self truth htruth.posSemidef.nonneg
  calc
    (CFC.sqrt truth *ᵥ vector) ⬝ᵥ (CFC.sqrt truth *ᵥ vector) =
        vector ⬝ᵥ ((CFC.sqrt truth)ᵀ *ᵥ (CFC.sqrt truth *ᵥ vector)) :=
        (Matrix.dotProduct_transpose_mulVec (CFC.sqrt truth) vector
          (CFC.sqrt truth *ᵥ vector)).symm
    _ = vector ⬝ᵥ (((CFC.sqrt truth)ᵀ * CFC.sqrt truth) *ᵥ vector) := by
        rw [Matrix.mulVec_mulVec]
    _ = vector ⬝ᵥ (truth *ᵥ vector) := by
        rw [hroot_transpose, hroot_square]
    _ = quadraticForm truth vector :=
        (quadraticForm_eq_dotProduct_mulVec truth vector).symm

/-- The exact finite source-defined counterpart of equation
`eq:working-weight-perturbation` in Appendix `lem:mean`.  The covariance
premises are precisely the finite form of `eq:proof-relative-order`, and the
conclusion retains the paper's `delta^2 / (1 - delta)^2` coefficient. -/
theorem source_gls_weight_perturbation_exact
    (truth workingCovariance : Matrix I I ℝ)
    (htruth : truth.PosDef) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa ℝ) (treatment : I → ℝ)
    (htruthgram : IsUnit (controlGram (Inv.inv truth) controls).det)
    (hworkinggram : IsUnit (controlGram (Inv.inv workingCovariance) controls).det)
    (htruthresidual : Not (residualizeControls (Inv.inv truth) controls treatment = 0))
    (hworkingresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0))
    (varianceScale delta : ℝ)
    (hdelta_nonneg : 0 ≤ delta) (hdelta_lt_one : delta < 1)
    (hlower :
      (varianceScale • workingCovariance - (1 - delta) • truth).PosSemidef)
    (hupper :
      ((1 + delta) • truth - varianceScale • workingCovariance).PosSemidef) :
    quadraticForm truth
      (glsOutcomeWeight workingCovariance controls treatment -
        glsOutcomeWeight truth controls treatment) ≤
      (delta ^ 2 / (1 - delta) ^ 2) *
        quadraticForm truth (glsOutcomeWeight truth controls treatment) := by
  have hnormalize : ((CFC.sqrt truth)⁻¹)ᵀ * truth * (CFC.sqrt truth)⁻¹ = 1 :=
    actual_inverse_sqrt_normalizes_covariance htruth
  have hrelative_lower :
      (delta • (1 : Matrix I I ℝ) +
        ((CFC.sqrt truth)⁻¹)ᵀ *
          (varianceScale • workingCovariance - truth) * (CFC.sqrt truth)⁻¹).PosSemidef :=
    relative_error_lower_sandwich_of_covariance_lower_sandwich hnormalize hlower
  have hrelative_upper :
      (delta • (1 : Matrix I I ℝ) -
        ((CFC.sqrt truth)⁻¹)ᵀ *
          (varianceScale • workingCovariance - truth) * (CFC.sqrt truth)⁻¹).PosSemidef :=
    relative_error_upper_sandwich_of_covariance_upper_sandwich hnormalize hupper
  have hfirst_order :=
    source_gls_weights_actual_whitened_first_order_conditions_transpose
      truth workingCovariance htruth hworking controls treatment htruthgram hworkinggram
      htruthresidual hworkingresidual varianceScale
  have hperturbation := relative_perturbation_bound_of_sandwich_and_stationarity
    hdelta_nonneg hdelta_lt_one hrelative_lower hrelative_upper
    (CFC.sqrt truth *ᵥ glsOutcomeWeight truth controls treatment)
    (CFC.sqrt truth *ᵥ
      (glsOutcomeWeight workingCovariance controls treatment -
        glsOutcomeWeight truth controls treatment))
    hfirst_order.1 hfirst_order.2
  calc
    quadraticForm truth
        (glsOutcomeWeight workingCovariance controls treatment -
          glsOutcomeWeight truth controls treatment) =
        (CFC.sqrt truth *ᵥ
          (glsOutcomeWeight workingCovariance controls treatment -
            glsOutcomeWeight truth controls treatment)) ⬝ᵥ
          (CFC.sqrt truth *ᵥ
            (glsOutcomeWeight workingCovariance controls treatment -
              glsOutcomeWeight truth controls treatment)) :=
        (actual_sqrt_dot_eq_quadraticForm htruth
          (glsOutcomeWeight workingCovariance controls treatment -
            glsOutcomeWeight truth controls treatment)).symm
    _ ≤ (delta ^ 2 / (1 - delta) ^ 2) *
          ((CFC.sqrt truth *ᵥ glsOutcomeWeight truth controls treatment) ⬝ᵥ
            (CFC.sqrt truth *ᵥ glsOutcomeWeight truth controls treatment)) :=
        hperturbation
    _ = (delta ^ 2 / (1 - delta) ^ 2) *
        quadraticForm truth (glsOutcomeWeight truth controls treatment) := by
        rw [actual_sqrt_dot_eq_quadraticForm htruth]

end InfillGLSLean.MeanWeightPerturbation
