module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import InfillGLSLean.GLSWeightIdentities

/-!
This module packaging and public-import boundary are visibility-only.  The
existing finite source/FWL bridge theorems retain their exact statements and
proof bodies; no manuscript assumption, proposition, dependency, or toolchain
is changed.
-/

public section

open Filter Matrix

namespace InfillGLSLean.L023

variable {I J : Type*} [Fintype J]

/-- A manuscript full-column-rank hypothesis makes the corresponding matrix
map injective.  This is the finite bridge from `rank [X W] = q + 1` to the
linear-algebra hypotheses used by the GLS FWL identities. -/
theorem fullColumnRank_mulVec_injective (A : Matrix I J ℝ)
    (hrank : A.rank = Fintype.card J) :
    Function.Injective A.mulVec := by
  have hnullity := A.mulVecLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (LinearMap.range A.mulVecLin) = Fintype.card J := by
    simpa [Matrix.rank] using hrank
  have hsource : Module.finrank ℝ (J → ℝ) = Fintype.card J := by
    exact Module.finrank_fintype_fun_eq_card ℝ
  rw [hrange, hsource] at hnullity
  have hker : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by
    omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

/-- The manuscript design `[X W]`: treatment in its first column and the
fixed control columns thereafter. -/
@[expose]
noncomputable def sourceDesign {q : ℕ} (treatment : I → ℝ)
    (controls : Matrix I (Fin q) ℝ) : Matrix I (Fin (q + 1)) ℝ :=
  fun i j => Fin.cases (treatment i) (fun k => controls i k) j

/-- Public definitional expansion of one existing source-design entry.  This
visibility-only `rfl` API supports the L-027 source-specification bridge. -/
@[simp]
theorem sourceDesign_apply {q : ℕ} (treatment : I → ℝ)
    (controls : Matrix I (Fin q) ℝ) (i : I) (j : Fin (q + 1)) :
    sourceDesign treatment controls i j =
      Fin.cases (treatment i) (fun k => controls i k) j :=
  rfl

@[simp]
theorem sourceDesign_mulVec_first_zero {q : ℕ} (treatment : I → ℝ)
    (controls : Matrix I (Fin q) ℝ) (coefficients : Fin q → ℝ) :
    (sourceDesign treatment controls).mulVec (Fin.cases 0 coefficients) =
      controls.mulVec coefficients := by
  ext i
  simp [sourceDesign, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem sourceDesign_controls_mulVec_injective {q : ℕ}
    (treatment : I → ℝ) (controls : Matrix I (Fin q) ℝ)
    (hdesign : Function.Injective (sourceDesign treatment controls).mulVec) :
    Function.Injective controls.mulVec := by
  intro left right heq
  let embed : (Fin q → ℝ) → Fin (q + 1) → ℝ := fun coefficients =>
    Fin.cases 0 coefficients
  have hdesignEq : (sourceDesign treatment controls).mulVec
      (embed left) =
      (sourceDesign treatment controls).mulVec
        (embed right) := by
    simpa only [embed, sourceDesign_mulVec_first_zero] using heq
  have hcoefficients : embed left = embed right := hdesign hdesignEq
  funext j
  simpa [embed] using congrFun hcoefficients j.succ

theorem sourceDesign_controlGram_posDef {q : ℕ}
    (treatment : I → ℝ) (controls : Matrix I (Fin q) ℝ)
    (precision : Matrix I I ℝ) (hprecision : precision.PosDef)
    [Fintype I] (hdesign : Function.Injective (sourceDesign treatment controls).mulVec) :
    (InfillGLSLean.controlGram precision controls).PosDef := by
  have hcontrols := sourceDesign_controls_mulVec_injective treatment controls hdesign
  unfold InfillGLSLean.controlGram
  simpa using hprecision.conjTranspose_mul_mul_same hcontrols

theorem sourceDesign_controlGram_det_isUnit {q : ℕ}
    (treatment : I → ℝ) (controls : Matrix I (Fin q) ℝ)
    (precision : Matrix I I ℝ) (hprecision : precision.PosDef)
    [Fintype I] (hdesign : Function.Injective (sourceDesign treatment controls).mulVec) :
    IsUnit (InfillGLSLean.controlGram precision controls).det := by
  have hgram := sourceDesign_controlGram_posDef treatment controls precision hprecision hdesign
  exact (Matrix.isUnit_iff_isUnit_det _).mp hgram.isUnit

@[simp]
theorem sourceDesign_mulVec_one_neg {q : ℕ} (treatment : I → ℝ)
    (controls : Matrix I (Fin q) ℝ) (coefficients : Fin q → ℝ) :
    (sourceDesign treatment controls).mulVec
      (Fin.cases 1 (fun j => -coefficients j)) =
        treatment - controls.mulVec coefficients := by
  ext i
  simp [sourceDesign, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem sourceDesign_residualizeControls_ne_zero {q : ℕ}
    (treatment : I → ℝ) (controls : Matrix I (Fin q) ℝ)
    (precision : Matrix I I ℝ) [Fintype I]
    (hdesign : Function.Injective (sourceDesign treatment controls).mulVec) :
    InfillGLSLean.residualizeControls precision controls treatment ≠ 0 := by
  intro hzero
  let coefficients : Fin q → ℝ :=
    (InfillGLSLean.controlGram precision controls)⁻¹ *ᵥ
      InfillGLSLean.controlScore precision controls treatment
  let embed : (Fin q → ℝ) → Fin (q + 1) → ℝ := fun values =>
    Fin.cases 1 (fun j => -values j)
  have hscore : (sourceDesign treatment controls).mulVec
      (embed coefficients) = 0 := by
    rw [show embed coefficients = Fin.cases 1 (fun j => -coefficients j) by rfl,
      sourceDesign_mulVec_one_neg]
    simpa [InfillGLSLean.residualizeControls, coefficients] using hzero
  have hcoefficients : embed coefficients = 0 := by
    apply hdesign
    simpa using hscore
  have hone : (1 : ℝ) = 0 := by
    simpa [embed] using congrFun hcoefficients 0
  norm_num at hone

/-- The eventual full-rank condition in `reg:maps`, at one fixed resolution,
supplies both finite hypotheses used by the multi-control FWL API. -/
theorem sourceDesign_fwl_nonsingularity_and_relevance_of_full_rank {q : ℕ}
    (treatment : I → ℝ) (controls : Matrix I (Fin q) ℝ)
    (precision : Matrix I I ℝ) [Fintype I]
    (hprecision : precision.PosDef)
    (hfull : (sourceDesign treatment controls).rank = q + 1) :
    IsUnit (InfillGLSLean.controlGram precision controls).det ∧
      InfillGLSLean.residualizeControls precision controls treatment ≠ 0 := by
  have hdesign : Function.Injective (sourceDesign treatment controls).mulVec := by
    apply fullColumnRank_mulVec_injective
    simpa using hfull
  exact ⟨sourceDesign_controlGram_det_isUnit treatment controls precision hprecision hdesign,
    sourceDesign_residualizeControls_ne_zero treatment controls precision hdesign⟩

/-- The literal attained-minimum predicate used for `Q_n` in the source-facing
specification.  It is definitionally the manuscript formula
`min_ell (x - W ell)' K⁻¹ (x - W ell)`. -/
@[expose]
def IsSourceTreatmentInformation {Kappa : Type*} [Fintype I] [Fintype Kappa]
    [DecidableEq I] (workingCovariance : Matrix I I ℝ)
    (treatment : I → ℝ) (controls : Matrix I Kappa ℝ) (Q : ℝ) : Prop :=
  (∃ coefficients : Kappa → ℝ,
    Q = InfillGLSLean.quadraticForm workingCovariance⁻¹
      (treatment - controls.mulVec coefficients)) ∧
    ∀ coefficients : Kappa → ℝ,
      Q ≤ InfillGLSLean.quadraticForm workingCovariance⁻¹
        (treatment - controls.mulVec coefficients)

/-- Public definitional expansion of the existing local source-information
predicate.  It changes no finite algebra or manuscript-facing statement. -/
theorem isSourceTreatmentInformation_iff {Kappa : Type*} [Fintype I]
    [Fintype Kappa] [DecidableEq I] (workingCovariance : Matrix I I ℝ)
    (treatment : I → ℝ) (controls : Matrix I Kappa ℝ) (Q : ℝ) :
    IsSourceTreatmentInformation workingCovariance treatment controls Q ↔
      (∃ coefficients : Kappa → ℝ,
        Q = InfillGLSLean.quadraticForm workingCovariance⁻¹
          (treatment - controls.mulVec coefficients)) ∧
        ∀ coefficients : Kappa → ℝ,
          Q ≤ InfillGLSLean.quadraticForm workingCovariance⁻¹
            (treatment - controls.mulVec coefficients) :=
  Iff.rfl

theorem quadraticForm_add_of_cross_terms_zero [Fintype I]
    (precision : Matrix I I ℝ) (left right : I → ℝ)
    (hleft : dotProduct left (precision.mulVec right) = 0)
    (hright : dotProduct right (precision.mulVec left) = 0) :
    InfillGLSLean.quadraticForm precision (left + right) =
      InfillGLSLean.quadraticForm precision left +
        InfillGLSLean.quadraticForm precision right := by
  have haddleft (first second third : I → ℝ) :
      dotProduct (first + second) third =
        dotProduct first third + dotProduct second third := by
    calc
      dotProduct (first + second) third = dotProduct third (first + second) :=
        dotProduct_comm _ _
      _ = dotProduct third first + dotProduct third second := dotProduct_add _ _ _
      _ = dotProduct first third + dotProduct second third := by
        rw [dotProduct_comm third first, dotProduct_comm third second]
  rw [InfillGLSLean.quadraticForm_eq_dotProduct_mulVec,
    InfillGLSLean.quadraticForm_eq_dotProduct_mulVec,
    InfillGLSLean.quadraticForm_eq_dotProduct_mulVec,
    Matrix.mulVec_add, dotProduct_add, haddleft, haddleft, hleft, hright]
  ring

theorem dotProduct_sub_left [Fintype I] (left middle right : I → ℝ) :
    dotProduct (left - middle) right =
      dotProduct left right - dotProduct middle right := by
  calc
    dotProduct (left - middle) right = dotProduct right (left - middle) :=
      dotProduct_comm _ _
    _ = dotProduct right left - dotProduct right middle := dotProduct_sub _ _ _
    _ = dotProduct left right - dotProduct middle right := by
      rw [dotProduct_comm right left, dotProduct_comm right middle]

theorem dotProduct_smul_left [Fintype I] (scalar : ℝ)
    (left right : I → ℝ) :
    dotProduct (scalar • left) right = scalar * dotProduct left right := by
  calc
    dotProduct (scalar • left) right = dotProduct right (scalar • left) :=
      dotProduct_comm _ _
    _ = scalar • dotProduct right left := dotProduct_smul scalar right left
    _ = scalar * dotProduct left right := by
      rw [smul_eq_mul, dotProduct_comm right left]

/-- Exact expansion of a symmetric quadratic form along a scalar direction. -/
theorem quadraticForm_sub_smul_of_symmetric [Fintype I]
    (precision : Matrix I I ℝ) (error direction : I → ℝ) (scalar : ℝ)
    (hsymm : precision.transpose = precision) :
    InfillGLSLean.quadraticForm precision (error - scalar • direction) =
      InfillGLSLean.quadraticForm precision error -
        2 * scalar * dotProduct direction (precision.mulVec error) +
          scalar ^ 2 * InfillGLSLean.quadraticForm precision direction := by
  have hcross : dotProduct error (precision.mulVec direction) =
      dotProduct direction (precision.mulVec error) := by
    calc
      dotProduct error (precision.mulVec direction) =
          dotProduct error (precision.transpose.mulVec direction) := by rw [hsymm]
      _ = dotProduct direction (precision.mulVec error) :=
        Matrix.dotProduct_transpose_mulVec precision error direction
  rw [InfillGLSLean.quadraticForm_eq_dotProduct_mulVec,
    InfillGLSLean.quadraticForm_eq_dotProduct_mulVec,
    InfillGLSLean.quadraticForm_eq_dotProduct_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    dotProduct_sub_left, dotProduct_sub_left, dotProduct_smul,
    dotProduct_smul_left, dotProduct_smul_left, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  rw [hcross]
  ring

/-- The FWL information is the literal attained minimum in manuscript
equation `eq:information`, not merely a replacement definition. -/
theorem controlInformation_isSourceTreatmentInformation
    {Kappa : Type*} [Fintype I] [DecidableEq I]
    [Fintype Kappa] [DecidableEq Kappa]
    (workingCovariance : Matrix I I ℝ) (hworking : workingCovariance.PosDef)
    (treatment : I → ℝ) (controls : Matrix I Kappa ℝ)
    (hgram : IsUnit
      (InfillGLSLean.controlGram workingCovariance⁻¹ controls).det) :
    IsSourceTreatmentInformation workingCovariance treatment controls
      (InfillGLSLean.controlInformation workingCovariance⁻¹ controls treatment) := by
  let precision : Matrix I I ℝ := workingCovariance⁻¹
  let residual : I → ℝ :=
    InfillGLSLean.residualizeControls precision controls treatment
  let minimizer : Kappa → ℝ :=
    (InfillGLSLean.controlGram precision controls)⁻¹ *ᵥ
      InfillGLSLean.controlScore precision controls treatment
  have hprecision : precision.PosDef := by
    dsimp [precision]
    exact hworking.inv
  have hsymm : precision.transpose = precision := by
    simpa using hprecision.isHermitian.eq
  have hgram' : IsUnit (InfillGLSLean.controlGram precision controls).det := by
    simpa [precision] using hgram
  unfold IsSourceTreatmentInformation
  constructor
  · refine ⟨minimizer, ?_⟩
    change InfillGLSLean.controlInformation precision controls treatment =
      InfillGLSLean.quadraticForm precision
        (treatment - controls.mulVec minimizer)
    change InfillGLSLean.quadraticForm precision residual =
      InfillGLSLean.quadraticForm precision
        (treatment - controls.mulVec minimizer)
    rfl
  · intro coefficients
    let difference : Kappa → ℝ := minimizer - coefficients
    have hdecomposition : treatment - controls.mulVec coefficients =
        residual + controls.mulVec difference := by
      dsimp [residual, difference, minimizer]
      unfold InfillGLSLean.residualizeControls
      rw [Matrix.mulVec_sub]
      abel
    have hleft : dotProduct residual
        (precision.mulVec (controls.mulVec difference)) = 0 :=
      InfillGLSLean.residualizedTreatment_precision_controls_zero precision controls treatment
        difference hsymm hgram'
    have hright : dotProduct (controls.mulVec difference)
        (precision.mulVec residual) = 0 := by
      calc
        dotProduct (controls.mulVec difference) (precision.mulVec residual) =
            dotProduct residual
              (precision.transpose.mulVec (controls.mulVec difference)) := by
                exact (Matrix.dotProduct_transpose_mulVec precision residual
                  (controls.mulVec difference)).symm
        _ = dotProduct residual
              (precision.mulVec (controls.mulVec difference)) := by rw [hsymm]
        _ = 0 := hleft
    have hnonnegative : 0 ≤ InfillGLSLean.quadraticForm precision
        (controls.mulVec difference) :=
      InfillGLSLean.quadraticForm_nonneg hprecision.posSemidef _
    have hquadratic : InfillGLSLean.quadraticForm precision
        (treatment - controls.mulVec coefficients) =
        InfillGLSLean.quadraticForm precision residual +
          InfillGLSLean.quadraticForm precision (controls.mulVec difference) := by
      rw [hdecomposition]
      exact quadraticForm_add_of_cross_terms_zero precision residual
        (controls.mulVec difference) hleft hright
    calc
      InfillGLSLean.controlInformation precision controls treatment =
          InfillGLSLean.quadraticForm precision residual := rfl
      _ ≤ InfillGLSLean.quadraticForm precision residual +
          InfillGLSLean.quadraticForm precision (controls.mulVec difference) :=
            le_add_of_nonneg_right hnonnegative
      _ = InfillGLSLean.quadraticForm precision
          (treatment - controls.mulVec coefficients) := hquadratic.symm

/-- Under the manuscript's finite SPD working matrix and full-rank design,
the residualized information is exactly the `Q_n` minimum in
`eq:information`. -/
theorem sourceInformation_of_full_rank
    {q : ℕ} [Fintype I] [DecidableEq I]
    (workingCovariance : Matrix I I ℝ) (hworking : workingCovariance.PosDef)
    (treatment : I → ℝ) (controls : Matrix I (Fin q) ℝ)
    (hfull : (sourceDesign treatment controls).rank = q + 1) :
    IsSourceTreatmentInformation workingCovariance treatment controls
      (InfillGLSLean.controlInformation workingCovariance⁻¹ controls treatment) := by
  have hprecision : workingCovariance⁻¹ |>.PosDef := hworking.inv
  have hfull' : (sourceDesign treatment controls).rank =
      Fintype.card (Fin (q + 1)) := by
    simpa using hfull
  have hdesign : Function.Injective (sourceDesign treatment controls).mulVec :=
    fullColumnRank_mulVec_injective _ hfull'
  have hgram : IsUnit
      (InfillGLSLean.controlGram workingCovariance⁻¹ controls).det :=
    sourceDesign_controlGram_det_isUnit treatment controls workingCovariance⁻¹
      hprecision hdesign
  exact controlInformation_isSourceTreatmentInformation workingCovariance hworking
    treatment controls hgram

/-- The literal GLS objective in manuscript equation `eq:estimator`. -/
@[expose]
noncomputable def sourceGLSObjective {Kappa : Type*} [Fintype I] [DecidableEq I]
    [Fintype Kappa] (workingCovariance : Matrix I I ℝ)
    (treatment : I → ℝ) (controls : Matrix I Kappa ℝ)
    (outcome : I → ℝ) (coefficient : ℝ) (controlCoefficients : Kappa → ℝ) : ℝ :=
  InfillGLSLean.quadraticForm workingCovariance⁻¹
    (outcome - coefficient • treatment - controls.mulVec controlCoefficients)

/-- Public definitional expansion of the existing local GLS objective.  This
is an API-only `rfl` bridge for exact minimizer translation. -/
@[simp]
theorem sourceGLSObjective_eq {Kappa : Type*} [Fintype I] [DecidableEq I]
    [Fintype Kappa] (workingCovariance : Matrix I I ℝ) (treatment : I → ℝ)
    (controls : Matrix I Kappa ℝ) (outcome : I → ℝ) (coefficient : ℝ)
    (controlCoefficients : Kappa → ℝ) :
    sourceGLSObjective workingCovariance treatment controls outcome coefficient
      controlCoefficients =
      InfillGLSLean.quadraticForm workingCovariance⁻¹
        (outcome - coefficient • treatment - controls.mulVec controlCoefficients) :=
  rfl

/-- A selected minimizer of the literal source GLS objective. -/
@[expose]
def IsSourceGLSMinimizer {Kappa : Type*} [Fintype I] [DecidableEq I]
    [Fintype Kappa] (workingCovariance : Matrix I I ℝ)
    (treatment : I → ℝ) (controls : Matrix I Kappa ℝ)
    (outcome : I → ℝ) (coefficient : ℝ) (controlCoefficients : Kappa → ℝ) : Prop :=
  ∀ coefficient' : ℝ, ∀ controlCoefficients' : Kappa → ℝ,
    sourceGLSObjective workingCovariance treatment controls outcome coefficient
      controlCoefficients ≤
      sourceGLSObjective workingCovariance treatment controls outcome coefficient'
        controlCoefficients'

/-- Public definitional expansion of the existing local selected-minimizer
predicate.  This API-only `rfl` bridge changes no statement or proof. -/
theorem isSourceGLSMinimizer_iff {Kappa : Type*} [Fintype I] [DecidableEq I]
    [Fintype Kappa] (workingCovariance : Matrix I I ℝ) (treatment : I → ℝ)
    (controls : Matrix I Kappa ℝ) (outcome : I → ℝ) (coefficient : ℝ)
    (controlCoefficients : Kappa → ℝ) :
    IsSourceGLSMinimizer workingCovariance treatment controls outcome coefficient
      controlCoefficients ↔
      ∀ coefficient' : ℝ, ∀ controlCoefficients' : Kappa → ℝ,
        sourceGLSObjective workingCovariance treatment controls outcome coefficient
          controlCoefficients ≤
          sourceGLSObjective workingCovariance treatment controls outcome coefficient'
            controlCoefficients' :=
  Iff.rfl

/-- Any selected minimizer of the literal GLS criterion has the treatment
coefficient in the exact multi-control FWL formula. -/
theorem sourceGLSMinimizer_beta_eq_fwl
    {Kappa : Type*} [Fintype I] [DecidableEq I]
    [Fintype Kappa] [DecidableEq Kappa]
    (workingCovariance : Matrix I I ℝ) (hworking : workingCovariance.PosDef)
    (treatment outcome : I → ℝ) (controls : Matrix I Kappa ℝ)
    (coefficient : ℝ) (controlCoefficients : Kappa → ℝ)
    (hgram : IsUnit
      (InfillGLSLean.controlGram workingCovariance⁻¹ controls).det)
    (hresidual : InfillGLSLean.residualizeControls workingCovariance⁻¹ controls treatment ≠ 0)
    (hmin : IsSourceGLSMinimizer workingCovariance treatment controls outcome
      coefficient controlCoefficients) :
    coefficient = InfillGLSLean.fwlEstimateControls workingCovariance⁻¹
      controls treatment outcome := by
  let precision : Matrix I I ℝ := workingCovariance⁻¹
  let residualTreatment : I → ℝ :=
    InfillGLSLean.residualizeControls precision controls treatment
  let treatmentFit : Kappa → ℝ :=
    (InfillGLSLean.controlGram precision controls)⁻¹ *ᵥ
      InfillGLSLean.controlScore precision controls treatment
  let estimationResidual : I → ℝ :=
    outcome - coefficient • treatment - controls.mulVec controlCoefficients
  let information : ℝ :=
    InfillGLSLean.controlInformation precision controls treatment
  let score : ℝ :=
    dotProduct residualTreatment (precision.mulVec estimationResidual)
  have hprecision : precision.PosDef := by
    dsimp [precision]
    exact hworking.inv
  have hsymm : precision.transpose = precision := by
    simpa using hprecision.isHermitian.eq
  have hgram' : IsUnit (InfillGLSLean.controlGram precision controls).det := by
    simpa [precision] using hgram
  have hresidual' : residualTreatment ≠ 0 := by
    simpa [precision, residualTreatment] using hresidual
  have hinformation_pos : 0 < information := by
    dsimp [information]
    exact InfillGLSLean.controlInformation_pos hprecision hresidual'
  have hinformation_ne : information ≠ 0 := ne_of_gt hinformation_pos
  have hperturb := hmin (coefficient + score / information)
    (controlCoefficients - (score / information) • treatmentFit)
  unfold IsSourceGLSMinimizer sourceGLSObjective at hperturb
  change InfillGLSLean.quadraticForm precision estimationResidual ≤
    InfillGLSLean.quadraticForm precision
      (outcome - (coefficient + score / information) • treatment -
        controls.mulVec (controlCoefficients - (score / information) • treatmentFit)) at hperturb
  have hperturbResidual :
      outcome - (coefficient + score / information) • treatment -
        controls.mulVec (controlCoefficients - (score / information) • treatmentFit) =
          estimationResidual - (score / information) • residualTreatment := by
    dsimp [estimationResidual, residualTreatment, treatmentFit]
    unfold InfillGLSLean.residualizeControls
    rw [add_smul, smul_sub, Matrix.mulVec_sub, Matrix.mulVec_smul]
    abel
  rw [hperturbResidual,
    quadraticForm_sub_smul_of_symmetric precision estimationResidual residualTreatment
      (score / information) hsymm] at hperturb
  have hquadratic_residual :
      InfillGLSLean.quadraticForm precision residualTreatment = information := rfl
  rw [hquadratic_residual] at hperturb
  have hscore_sq_over : score ^ 2 / information =
      2 * (score / information) * score - (score / information) ^ 2 * information := by
    field_simp [hinformation_ne]
    ring
  have hscore_sq_nonneg : 0 ≤ score ^ 2 / information :=
    div_nonneg (sq_nonneg score) (le_of_lt hinformation_pos)
  have hscore_sq_le_zero : score ^ 2 / information ≤ 0 := by
    rw [hscore_sq_over]
    linarith
  have hscore_sq_zero : score ^ 2 / information = 0 :=
    le_antisymm hscore_sq_le_zero hscore_sq_nonneg
  have hscore_sq : score ^ 2 = 0 := by
    calc
      score ^ 2 = (score ^ 2 / information) * information := by
        field_simp [hinformation_ne]
      _ = 0 := by rw [hscore_sq_zero, zero_mul]
  have hscore_zero : score = 0 := sq_eq_zero_iff.mp hscore_sq
  have hcontrols_zero : dotProduct residualTreatment
      (precision.mulVec (controls.mulVec controlCoefficients)) = 0 :=
    InfillGLSLean.residualizedTreatment_precision_controls_zero precision controls treatment
      controlCoefficients hsymm hgram'
  have htreatment_score : dotProduct residualTreatment (precision.mulVec treatment) =
      information := by
    dsimp [information]
    exact InfillGLSLean.residualizedTreatment_dot_precision_treatment_eq_information
      precision controls treatment hsymm hgram'
  have houtcome_score : dotProduct residualTreatment (precision.mulVec outcome) =
      dotProduct residualTreatment
        (precision.mulVec (InfillGLSLean.residualizeControls precision controls outcome)) := by
    symm
    exact InfillGLSLean.residualizedTreatment_dot_precision_residualize_eq_original
      precision controls treatment outcome hsymm hgram'
  have hscore_formula : score =
      dotProduct residualTreatment
        (precision.mulVec (InfillGLSLean.residualizeControls precision controls outcome)) -
          coefficient * information := by
    dsimp [score, estimationResidual]
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul,
      dotProduct_sub, dotProduct_sub, dotProduct_smul,
      htreatment_score, hcontrols_zero, houtcome_score, smul_eq_mul]
    ring
  have hcoefficient : coefficient =
      dotProduct residualTreatment
        (precision.mulVec (InfillGLSLean.residualizeControls precision controls outcome)) /
          information := by
    apply (eq_div_iff hinformation_ne).2
    linarith [hscore_formula, hscore_zero]
  change coefficient =
    dotProduct residualTreatment
      (precision.mulVec (InfillGLSLean.residualizeControls precision controls outcome)) /
        information
  exact hcoefficient

/-- Exact finite bridge for the source specification: at a resolution where
`rank [X W] = q + 1` and `K` is positive definite, the literal GLS minimizer
in `eq:estimator` has the FWL coefficient in `eq:FWL`. -/
theorem sourceGLSMinimizer_beta_eq_fwl_of_full_rank
    {q : ℕ} [Fintype I] [DecidableEq I]
    (workingCovariance : Matrix I I ℝ) (hworking : workingCovariance.PosDef)
    (treatment outcome : I → ℝ) (controls : Matrix I (Fin q) ℝ)
    (coefficient : ℝ) (controlCoefficients : Fin q → ℝ)
    (hfull : (sourceDesign treatment controls).rank = q + 1)
    (hmin : IsSourceGLSMinimizer workingCovariance treatment controls outcome
      coefficient controlCoefficients) :
    coefficient = InfillGLSLean.fwlEstimateControls workingCovariance⁻¹
      controls treatment outcome := by
  have hprecision : workingCovariance⁻¹ |>.PosDef := hworking.inv
  have hfull' : (sourceDesign treatment controls).rank = Fintype.card (Fin (q + 1)) := by
    simpa using hfull
  have hdesign : Function.Injective (sourceDesign treatment controls).mulVec :=
    fullColumnRank_mulVec_injective _ hfull'
  have hgram : IsUnit
      (InfillGLSLean.controlGram workingCovariance⁻¹ controls).det :=
    sourceDesign_controlGram_det_isUnit treatment controls workingCovariance⁻¹
      hprecision hdesign
  have hresidual : InfillGLSLean.residualizeControls workingCovariance⁻¹
      controls treatment ≠ 0 :=
    sourceDesign_residualizeControls_ne_zero treatment controls workingCovariance⁻¹ hdesign
  exact sourceGLSMinimizer_beta_eq_fwl workingCovariance hworking treatment outcome controls
    coefficient controlCoefficients hgram hresidual hmin

/-- Tail form of the exact source bridge.  This is the finite algebra content
of `estimatorHasFWLForm`: eventual full rank plus an SPD working matrix turn
the selected `eq:estimator` minimizer into the `eq:FWL` coefficient at every
sufficiently fine resolution. -/
theorem eventually_sourceGLSMinimizer_beta_eq_fwl
    {Ω : Type*} {q : ℕ} {N : ℕ → ℕ}
    (workingCovariance : (n : ℕ) → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (treatment : (n : ℕ) → Fin (N n) → ℝ)
    (controls : (n : ℕ) → Matrix (Fin (N n)) (Fin q) ℝ)
    (outcome : (n : ℕ) → Ω → Fin (N n) → ℝ)
    (betaHat : (n : ℕ) → Ω → ℝ)
    (gammaHat : (n : ℕ) → Ω → Fin q → ℝ)
    (hworking : ∀ n, (workingCovariance n).PosDef)
    (hfull : ∀ᶠ n in atTop,
      (sourceDesign (treatment n) (controls n)).rank = q + 1)
    (hmin : ∀ n ω, IsSourceGLSMinimizer (workingCovariance n)
      (treatment n) (controls n) (outcome n ω) (betaHat n ω) (gammaHat n ω)) :
    ∀ᶠ n in atTop, ∀ ω,
      betaHat n ω = InfillGLSLean.fwlEstimateControls (workingCovariance n)⁻¹
        (controls n) (treatment n) (outcome n ω) := by
  filter_upwards [hfull] with n hn
  intro ω
  exact sourceGLSMinimizer_beta_eq_fwl_of_full_rank (workingCovariance n)
    (hworking n) (treatment n) (outcome n ω) (controls n)
    (betaHat n ω) (gammaHat n ω) hn (hmin n ω)

end InfillGLSLean.L023
