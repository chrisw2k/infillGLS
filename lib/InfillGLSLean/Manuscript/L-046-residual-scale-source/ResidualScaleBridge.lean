module

public import ManuscriptSpecification
import «L-029-consistency-integration».Explore
import «L-034-normality-exact-integration».Explore
import «L-032-finite-wick-bridge».WickBridge
import «L-046-residual-scale-source».ScalarMomentBridge
import «L-035-variance-exact-integration».Explore
import «L-041-common-refinement-pd».CommonRefinementPD
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace InfillGLSLean.ManuscriptSpecification.L046

open Matrix
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators MatrixOrder

/-- The finite-dimensional residual projector associated with a full-column
rank real design.  This is only a local algebraic construction. -/
noncomputable def tailResidualProjection {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real) : Matrix ι ι Real :=
  1 - A * (Aᵀ * A)⁻¹ * Aᵀ

theorem gram_isSymm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ Real) : (Aᵀ * A).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem tailResidualProjection_transpose {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real) :
    (tailResidualProjection A)ᵀ = tailResidualProjection A := by
  unfold tailResidualProjection
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [(gram_isSymm A).inv.eq]
  simp only [← Matrix.mul_assoc]

theorem hatMatrix_idempotent {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real)
    (hgram : IsUnit (Aᵀ * A).det) :
    (A * (Aᵀ * A)⁻¹ * Aᵀ) * (A * (Aᵀ * A)⁻¹ * Aᵀ) =
      A * (Aᵀ * A)⁻¹ * Aᵀ := by
  let G : Matrix κ κ Real := Aᵀ * A
  change IsUnit G.det at hgram
  change (A * G⁻¹ * Aᵀ) * (A * G⁻¹ * Aᵀ) = A * G⁻¹ * Aᵀ
  calc
    (A * G⁻¹ * Aᵀ) * (A * G⁻¹ * Aᵀ) =
        A * G⁻¹ * G * G⁻¹ * Aᵀ := by
      simp only [G, Matrix.mul_assoc]
    _ = A * (G⁻¹ * G) * G⁻¹ * Aᵀ := by
      simp only [Matrix.mul_assoc]
    _ = A * (1 : Matrix κ κ Real) * G⁻¹ * Aᵀ := by
      rw [Matrix.nonsing_inv_mul G hgram]
    _ = A * G⁻¹ * Aᵀ := by simp

theorem tailResidualProjection_idempotent {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real)
    (hgram : IsUnit (Aᵀ * A).det) :
    tailResidualProjection A * tailResidualProjection A = tailResidualProjection A := by
  let H : Matrix ι ι Real := A * (Aᵀ * A)⁻¹ * Aᵀ
  have hH : H * H = H := by
    exact hatMatrix_idempotent A hgram
  change (1 - H) * (1 - H) = 1 - H
  calc
    (1 - H) * (1 - H) = 1 - H - H + H * H := by
      noncomm_ring
    _ = 1 - H := by rw [hH]; noncomm_ring

theorem tailResidualProjection_mul_design {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real)
    (hgram : IsUnit (Aᵀ * A).det) :
    tailResidualProjection A * A = 0 := by
  let G : Matrix κ κ Real := Aᵀ * A
  change IsUnit G.det at hgram
  unfold tailResidualProjection
  change (1 - A * G⁻¹ * Aᵀ) * A = 0
  calc
    (1 - A * G⁻¹ * Aᵀ) * A = A - A * G⁻¹ * G := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      simp only [G, Matrix.mul_assoc]
    _ = A - A * (G⁻¹ * G) := by
      rw [Matrix.mul_assoc]
    _ = A - A * (1 : Matrix κ κ Real) := by
      rw [Matrix.nonsing_inv_mul G hgram]
    _ = 0 := by simp

theorem trace_hatMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real)
    (hgram : IsUnit (Aᵀ * A).det) :
    (A * (Aᵀ * A)⁻¹ * Aᵀ).trace = (Fintype.card κ : Real) := by
  let G : Matrix κ κ Real := Aᵀ * A
  change IsUnit G.det at hgram
  change (A * G⁻¹ * Aᵀ).trace = (Fintype.card κ : Real)
  have hG : Aᵀ * A = G := rfl
  calc
    (A * G⁻¹ * Aᵀ).trace = (Aᵀ * A * G⁻¹).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle A G⁻¹ Aᵀ
    _ = (G * G⁻¹).trace := by rw [hG]
    _ = (1 : Matrix κ κ Real).trace := by rw [Matrix.mul_nonsing_inv G hgram]
    _ = (Fintype.card κ : Real) := Matrix.trace_one

theorem trace_tailResidualProjection {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real)
    (hgram : IsUnit (Aᵀ * A).det) :
    (tailResidualProjection A).trace =
      (Fintype.card ι : Real) - (Fintype.card κ : Real) := by
  unfold tailResidualProjection
  rw [Matrix.trace_sub, Matrix.trace_one, trace_hatMatrix A hgram]

theorem mulVec_injective_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι Real) (hS : IsUnit S) : Function.Injective S.mulVec := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  intro x y hxy
  have hleft := congrArg (fun z : ι → Real => S⁻¹ *ᵥ z) hxy
  calc
    x = (1 : Matrix ι ι Real) *ᵥ x := by simp
    _ = (S⁻¹ * S) *ᵥ x := by rw [Matrix.nonsing_inv_mul S hdet]
    _ = S⁻¹ *ᵥ (S *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = S⁻¹ *ᵥ (S *ᵥ y) := hleft
    _ = (S⁻¹ * S) *ᵥ y := by rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix ι ι Real) *ᵥ y := by rw [Matrix.nonsing_inv_mul S hdet]
    _ = y := by simp

theorem mulVec_injective_mul_of_isUnit {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (S : Matrix ι ι Real) (A : Matrix ι κ Real) (hS : IsUnit S)
    (hA : Function.Injective A.mulVec) : Function.Injective (S * A).mulVec := by
  intro x y hxy
  apply hA
  apply mulVec_injective_of_isUnit S hS
  simpa only [Matrix.mulVec_mulVec] using hxy

theorem mulVec_injective_mul_of_injective {ι κ : Type*} [Fintype ι]
    [Fintype κ] (S : Matrix ι ι Real) (A : Matrix ι κ Real)
    (hS : Function.Injective S.mulVec) (hA : Function.Injective A.mulVec) :
    Function.Injective (S * A).mulVec := by
  intro x y hxy
  apply hA
  apply hS
  simpa only [Matrix.mulVec_mulVec] using hxy

theorem gram_posDef_of_mulVec_injective {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (A : Matrix ι κ Real) (hA : Function.Injective A.mulVec) :
    (Aᵀ * A).PosDef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
    (Matrix.PosDef.one : (1 : Matrix ι ι Real).PosDef).conjTranspose_mul_mul_same hA

theorem gram_det_isUnit_of_mulVec_injective {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real) (hA : Function.Injective A.mulVec) :
    IsUnit (Aᵀ * A).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (gram_posDef_of_mulVec_injective A hA).isUnit

theorem mulVec_injective_of_rank_eq_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ Real) (hrank : A.rank = Fintype.card κ) :
    Function.Injective A.mulVec := by
  change Function.Injective A.mulVecLin
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.finrank_eq_zero.mp
  have hsum := A.mulVecLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank Real A.mulVecLin.range = Fintype.card κ := by
    simpa only [Matrix.rank] using hrank
  have hdomain : Module.finrank Real (κ → Real) = Fintype.card κ :=
    Module.finrank_fintype_fun_eq_card Real
  omega

theorem cfcSqrt_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι Real) (hK : K.PosDef) : IsUnit (CFC.sqrt K) := by
  apply (isUnit_pow_iff (by norm_num : (2 : Nat) ≠ 0)).mp
  rw [CFC.sq_sqrt K hK.posSemidef.nonneg]
  exact hK.isUnit

theorem cfcSqrt_det_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι Real) (hK : K.PosDef) : IsUnit (CFC.sqrt K).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (cfcSqrt_isUnit K hK)

theorem inverse_cfcSqrt_adjoint_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι Real) (hK : K.PosDef) :
    ((CFC.sqrt K)⁻¹)ᴴ * (CFC.sqrt K)⁻¹ = K⁻¹ := by
  let A : Matrix ι ι Real := CFC.sqrt K
  have hsq : A ^ 2 = K := by
    dsimp [A]
    exact CFC.sq_sqrt K hK.posSemidef.nonneg
  have hAunit : IsUnit A := by
    apply (isUnit_pow_iff (by norm_num : (2 : Nat) ≠ 0)).mp
    rw [hsq]
    exact hK.isUnit
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  have hKdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hAhermitian : A.IsHermitian := by
    dsimp [A]
    exact (CFC.sqrt_nonneg K).posSemidef.isHermitian
  have hright : (A⁻¹ * A⁻¹) * K = 1 := by
    rw [← hsq, pow_two]
    calc
      (A⁻¹ * A⁻¹) * (A * A) = A⁻¹ * (A⁻¹ * A) * A := by
        simp only [Matrix.mul_assoc]
      _ = A⁻¹ * 1 * A := by rw [Matrix.nonsing_inv_mul A hAdet]
      _ = A⁻¹ * A := by simp
      _ = 1 := Matrix.nonsing_inv_mul A hAdet
  change (A⁻¹)ᴴ * A⁻¹ = K⁻¹
  rw [hAhermitian.inv.eq]
  calc
    A⁻¹ * A⁻¹ = (A⁻¹ * A⁻¹) * 1 := (Matrix.mul_one _).symm
    _ = (A⁻¹ * A⁻¹) * (K * K⁻¹) := by rw [Matrix.mul_nonsing_inv K hKdet]
    _ = ((A⁻¹ * A⁻¹) * K) * K⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 1 * K⁻¹ := by rw [hright]
    _ = K⁻¹ := Matrix.one_mul _

/-- The real inverse CFC square root is symmetric.  This discharges the
transpose-orientation step before writing `S * Sigma * Sᵀ`. -/
theorem inverse_cfcSqrt_transpose_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι Real) (hK : K.PosDef) :
    ((CFC.sqrt K)⁻¹)ᵀ = (CFC.sqrt K)⁻¹ := by
  have hsqrt : (CFC.sqrt K).IsHermitian :=
    (CFC.sqrt_nonneg K).posSemidef.isHermitian
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsqrt.inv.eq

theorem inverse_cfcSqrt_whitens {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι Real) (hK : K.PosDef) :
    ((CFC.sqrt K)⁻¹)ᴴ * K * (CFC.sqrt K)⁻¹ = 1 := by
  let A : Matrix ι ι Real := CFC.sqrt K
  have hsq : A ^ 2 = K := by
    dsimp [A]
    exact CFC.sq_sqrt K hK.posSemidef.nonneg
  have hAunit : IsUnit A := by
    apply (isUnit_pow_iff (by norm_num : (2 : Nat) ≠ 0)).mp
    rw [hsq]
    exact hK.isUnit
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  have hAhermitian : A.IsHermitian := by
    dsimp [A]
    exact (CFC.sqrt_nonneg K).posSemidef.isHermitian
  change (A⁻¹)ᴴ * K * A⁻¹ = 1
  rw [hAhermitian.inv.eq, ← hsq, pow_two]
  calc
    A⁻¹ * (A * A) * A⁻¹ = (A⁻¹ * A) * (A * A⁻¹) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul A hAdet, Matrix.mul_nonsing_inv A hAdet]
      exact mul_one 1

theorem inverse_cfcSqrt_mulVec_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι Real) (hK : K.PosDef) :
    Function.Injective ((CFC.sqrt K)⁻¹).mulVec := by
  let A : Matrix ι ι Real := CFC.sqrt K
  have hdet : IsUnit A.det := by
    dsimp [A]
    exact cfcSqrt_det_isUnit K hK
  intro x y hxy
  have hleft := congrArg (fun z : ι → Real => A *ᵥ z) hxy
  change A *ᵥ (A⁻¹ *ᵥ x) = A *ᵥ (A⁻¹ *ᵥ y) at hleft
  calc
    x = (1 : Matrix ι ι Real) *ᵥ x := by simp
    _ = (A * A⁻¹) *ᵥ x := by rw [Matrix.mul_nonsing_inv A hdet]
    _ = A *ᵥ (A⁻¹ *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = A *ᵥ (A⁻¹ *ᵥ y) := hleft
    _ = (A * A⁻¹) *ᵥ y := by rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix ι ι Real) *ᵥ y := by rw [Matrix.mul_nonsing_inv A hdet]
    _ = y := by simp

open MeasureTheory ProbabilityTheory

variable {D : CompactEuclideanDomain}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable def sourceWhitenedDesign (E : FixedConditionalExperiment μ P) (n : Nat) :
    Matrix (Fin (E.maps.N n)) (Fin (E.q + 1)) Real :=
  (CFC.sqrt (E.kernel n))⁻¹ *
    regionalDesign μ E.maps E.treatment E.controls n

noncomputable def sourceTailResidualProjection (E : FixedConditionalExperiment μ P)
    (n : Nat) : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
  tailResidualProjection (sourceWhitenedDesign E n)

/-- The Appendix `app:scale` transformed covariance in its literal real
orientation, `Gamma_n = S_n * Sigma_n * S_nᵀ`. -/
noncomputable def sourceTransformedCovariance (E : FixedConditionalExperiment μ P)
    (n : Nat) : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
  (CFC.sqrt (E.kernel n))⁻¹ * trueCovariance E n * ((CFC.sqrt (E.kernel n))⁻¹)ᵀ

/-- The exact source covariance sandwich after whitening.  The proof first
uses `inverse_cfcSqrt_transpose_eq`; no covariance orientation is exchanged
silently. -/
theorem sourceTransformedCovariance_sandwich
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n) :
    (sourceTransformedCovariance E n -
        (covariance.sigmaSquared / (1 + covariance.delta n)) •
          (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real)).PosSemidef ∧
      ((covariance.sigmaSquared / (1 - covariance.delta n)) •
          (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real) -
        sourceTransformedCovariance E n).PosSemidef := by
  let S : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    (CFC.sqrt (E.kernel n))⁻¹
  have hStranspose : Sᵀ = S := by
    dsimp [S]
    exact inverse_cfcSqrt_transpose_eq (E.kernel n) (E.kernel_posDef n)
  have hwhite : Sᵀ * E.kernel n * S = 1 := by
    dsimp [S]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      inverse_cfcSqrt_whitens (E.kernel n) (E.kernel_posDef n)
  rcases covariance.sandwich n hn with ⟨_, _, hlower, hupper⟩
  have hlower' := hlower.conjTranspose_mul_mul_same S
  have hupper' := hupper.conjTranspose_mul_mul_same S
  have hlower'' :
      (Sᵀ * trueCovariance E n * S -
        (covariance.sigmaSquared / (1 + covariance.delta n)) •
          (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real)).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hwhite] using hlower'
  have hupper'' :
      ((covariance.sigmaSquared / (1 - covariance.delta n)) •
        (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real) -
          Sᵀ * trueCovariance E n * S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hwhite] using hupper'
  change
    (S * trueCovariance E n * Sᵀ -
        (covariance.sigmaSquared / (1 + covariance.delta n)) •
          (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real)).PosSemidef ∧
      ((covariance.sigmaSquared / (1 - covariance.delta n)) •
          (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real) -
        S * trueCovariance E n * Sᵀ).PosSemidef
  rw [hStranspose] at hlower'' hupper''
  rw [hStranspose]
  exact ⟨hlower'', hupper''⟩

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem sourceWhitenedDesign_gram_det_isUnit (E : FixedConditionalExperiment μ P)
    (n : Nat) (hrank :
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    IsUnit ((sourceWhitenedDesign E n)ᵀ * sourceWhitenedDesign E n).det := by
  apply gram_det_isUnit_of_mulVec_injective
  apply mulVec_injective_mul_of_injective
  · exact inverse_cfcSqrt_mulVec_injective (E.kernel n) (E.kernel_posDef n)
  · apply mulVec_injective_of_rank_eq_card
    simpa using hrank

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem sourceTailResidualProjection_transpose (E : FixedConditionalExperiment μ P)
    (n : Nat) :
    (sourceTailResidualProjection E n)ᵀ = sourceTailResidualProjection E n :=
  tailResidualProjection_transpose (sourceWhitenedDesign E n)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem sourceTailResidualProjection_idempotent (E : FixedConditionalExperiment μ P)
    (n : Nat) (hrank :
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    sourceTailResidualProjection E n * sourceTailResidualProjection E n =
      sourceTailResidualProjection E n :=
  tailResidualProjection_idempotent (sourceWhitenedDesign E n)
    (sourceWhitenedDesign_gram_det_isUnit E n hrank)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem sourceTailResidualProjection_mul_whitenedDesign
    (E : FixedConditionalExperiment μ P) (n : Nat) (hrank :
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    sourceTailResidualProjection E n * sourceWhitenedDesign E n = 0 :=
  tailResidualProjection_mul_design (sourceWhitenedDesign E n)
    (sourceWhitenedDesign_gram_det_isUnit E n hrank)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem trace_sourceTailResidualProjection (E : FixedConditionalExperiment μ P)
    (n : Nat) (hrank :
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (sourceTailResidualProjection E n).trace =
      (E.maps.N n : Real) - ((E.q + 1 : Nat) : Real) := by
  simpa only [sourceTailResidualProjection, Fintype.card_fin] using
    trace_tailResidualProjection (sourceWhitenedDesign E n)
      (sourceWhitenedDesign_gram_det_isUnit E n hrank)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem sourceTailResidualProjection_kills_controls
    (E : FixedConditionalExperiment μ P) (n : Nat) (hrank :
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹ *
      regionalControls μ E.maps E.controls n = 0 := by
  have hdesign : sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹ *
      regionalDesign μ E.maps E.treatment E.controls n = 0 := by
    simpa only [sourceWhitenedDesign, Matrix.mul_assoc] using
      sourceTailResidualProjection_mul_whitenedDesign E n hrank
  ext i j
  have hentry := congrFun (congrFun hdesign i) (Fin.succ j)
  simpa only [Matrix.mul_apply, regionalDesign_apply, Fin.cases_succ,
    Matrix.zero_apply] using hentry

theorem real_sub_card_eq_nat_sub (N q : Nat) (h : q + 1 ≤ N) :
    (N : Real) - ((q + 1 : Nat) : Real) = ((N - q - 1 : Nat) : Real) := by
  have hsum : N - q - 1 + (q + 1) = N := by omega
  have hsumR : ((N - q - 1 : Nat) : Real) + ((q + 1 : Nat) : Real) = (N : Real) := by
    exact_mod_cast hsum
  linarith

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem trace_sourceTailResidualProjection_eq_scale_divisor
    (E : FixedConditionalExperiment μ P) (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 ≤ E.maps.N n) :
    (sourceTailResidualProjection E n).trace =
      ((E.maps.N n - E.q - 1 : Nat) : Real) := by
  rw [trace_sourceTailResidualProjection E n hrank]
  exact real_sub_card_eq_nat_sub (E.maps.N n) E.q hdivisor

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem regionalDesign_mulVec_eq_model
    (E : FixedConditionalExperiment μ P) (n : Nat) (b : Real) (g : Fin E.q → Real) :
    regionalDesign μ E.maps E.treatment E.controls n *ᵥ Fin.cases b g =
      b • regionalValues μ E.maps E.treatment n +
        regionalControls μ E.maps E.controls n *ᵥ g := by
  ext i
  simp only [Matrix.mulVec, dotProduct, regionalDesign_apply, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Matrix.mulVec]
  change regionalValues μ E.maps E.treatment n i * b +
      ∑ x, regionalControls μ E.maps E.controls n i x * g x =
    b * regionalValues μ E.maps E.treatment n i +
      ∑ x, regionalControls μ E.maps E.controls n i x * g x
  ring

theorem dotProduct_add_of_orthogonal {ι : Type*} [Fintype ι]
    (u v : ι → Real) (huv : u ⬝ᵥ v = 0) :
    (u + v) ⬝ᵥ (u + v) = u ⬝ᵥ u + v ⬝ᵥ v := by
  calc
    (u + v) ⬝ᵥ (u + v) = (u + v) ⬝ᵥ u + (u + v) ⬝ᵥ v :=
      dotProduct_add (u + v) u v
    _ = u ⬝ᵥ (u + v) + v ⬝ᵥ (u + v) := by
      rw [dotProduct_comm (u + v) u, dotProduct_comm (u + v) v]
    _ = (u ⬝ᵥ u + u ⬝ᵥ v) + (v ⬝ᵥ u + v ⬝ᵥ v) := by
      rw [dotProduct_add, dotProduct_add]
    _ = u ⬝ᵥ u + v ⬝ᵥ v := by
      rw [huv, dotProduct_comm v u, huv]
      ring

theorem finiteWeightedScore_add {ι Ω : Type*} [Fintype ι]
    (u v : ι → Real) (X : ι → Ω → Real) :
    finiteWeightedScore (u + v) X =
      fun ω => finiteWeightedScore u X ω + finiteWeightedScore v X ω := by
  funext ω
  simp only [finiteWeightedScore_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem finiteWeightedScore_sub {ι Ω : Type*} [Fintype ι]
    (u v : ι → Real) (X : ι → Ω → Real) :
    finiteWeightedScore (u - v) X =
      fun ω => finiteWeightedScore u X ω - finiteWeightedScore v X ω := by
  funext ω
  simp only [finiteWeightedScore_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

noncomputable def normalCoefficient {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ Real) (y : ι → Real) : κ → Real :=
  (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ y)

theorem tailResidualProjection_mulVec_eq_residual {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ Real) (y : ι → Real) :
    tailResidualProjection A *ᵥ y = y - A *ᵥ normalCoefficient A y := by
  unfold tailResidualProjection normalCoefficient
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem tailResidualProjection_dot_design_eq_zero {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ Real) (hgram : IsUnit (Aᵀ * A).det)
    (y : ι → Real) (z : κ → Real) :
    (tailResidualProjection A *ᵥ y) ⬝ᵥ (A *ᵥ z) = 0 := by
  calc
    (tailResidualProjection A *ᵥ y) ⬝ᵥ (A *ᵥ z) =
        (A *ᵥ z) ⬝ᵥ (tailResidualProjection A *ᵥ y) :=
      dotProduct_comm _ _
    _ =
        y ⬝ᵥ (tailResidualProjection A)ᵀ *ᵥ (A *ᵥ z) :=
      (Matrix.dotProduct_transpose_mulVec (tailResidualProjection A) y (A *ᵥ z)).symm
    _ = y ⬝ᵥ tailResidualProjection A *ᵥ (A *ᵥ z) := by
      rw [tailResidualProjection_transpose]
    _ = y ⬝ᵥ (tailResidualProjection A * A) *ᵥ z := by
      rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [tailResidualProjection_mul_design A hgram, Matrix.zero_mulVec, dotProduct_zero]

theorem leastSquares_residual_eq_tailResidualProjection {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ Real) (y : ι → Real) (theta : κ → Real)
    (hgram : IsUnit (Aᵀ * A).det)
    (hmin : ∀ theta' : κ → Real,
      (y - A *ᵥ theta) ⬝ᵥ (y - A *ᵥ theta) ≤
        (y - A *ᵥ theta') ⬝ᵥ (y - A *ᵥ theta')) :
    y - A *ᵥ theta = tailResidualProjection A *ᵥ y := by
  let theta0 : κ → Real := normalCoefficient A y
  let u : ι → Real := tailResidualProjection A *ᵥ y
  let v : ι → Real := A *ᵥ (theta0 - theta)
  have hdecomposition : y - A *ᵥ theta = u + v := by
    change y - A *ᵥ theta = tailResidualProjection A *ᵥ y +
      A *ᵥ (theta0 - theta)
    rw [tailResidualProjection_mulVec_eq_residual]
    change y - A *ᵥ theta =
      y - A *ᵥ theta0 + A *ᵥ (theta0 - theta)
    rw [Matrix.mulVec_sub]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have huv : u ⬝ᵥ v = 0 := by
    exact tailResidualProjection_dot_design_eq_zero A hgram y (theta0 - theta)
  have hpythag :
      (y - A *ᵥ theta) ⬝ᵥ (y - A *ᵥ theta) = u ⬝ᵥ u + v ⬝ᵥ v := by
    rw [hdecomposition]
    exact dotProduct_add_of_orthogonal u v huv
  have hmin0 := hmin theta0
  have htarget : y - A *ᵥ theta0 = u := by
    change y - A *ᵥ normalCoefficient A y = tailResidualProjection A *ᵥ y
    exact (tailResidualProjection_mulVec_eq_residual A y).symm
  rw [htarget] at hmin0
  have hnonneg : 0 ≤ v ⬝ᵥ v := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => by simpa only [pow_two] using sq_nonneg (v i)
  have hvnorm : v ⬝ᵥ v = 0 := by linarith
  have hvzero : v = 0 := dotProduct_self_eq_zero.mp hvnorm
  rw [hdecomposition, hvzero, add_zero]

theorem quadraticForm_eq_whitened_dotProduct {ι : Type*} [Fintype ι]
    [DecidableEq ι] (K S : Matrix ι ι Real) (r : ι → Real)
    (hfactor : Sᵀ * S = K⁻¹) :
    quadraticForm K⁻¹ r = (S *ᵥ r) ⬝ᵥ (S *ᵥ r) := by
  calc
    quadraticForm K⁻¹ r = r ⬝ᵥ K⁻¹ *ᵥ r :=
      InfillGLSLean.quadraticForm_eq_dotProduct_mulVec K⁻¹ r
    _ = r ⬝ᵥ (Sᵀ * S) *ᵥ r := by rw [hfactor]
    _ = r ⬝ᵥ Sᵀ *ᵥ (S *ᵥ r) := by rw [Matrix.mulVec_mulVec]
    _ = (S *ᵥ r) ⬝ᵥ (S *ᵥ r) := Matrix.dotProduct_transpose_mulVec S r (S *ᵥ r)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem fittedResidual_eq_regionalDesign_residual
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω) :
    fittedResidual E n ω =
      (fun i => regionalRandomValues μ E.maps E.outcome n i ω) -
        regionalDesign μ E.maps E.treatment E.controls n *ᵥ
          Fin.cases (E.betaHat n ω) (E.gammaHat n ω) := by
  change
    (fun i => regionalRandomValues μ E.maps E.outcome n i ω) -
        (E.betaHat n ω) • regionalValues μ E.maps E.treatment n -
        regionalControls μ E.maps E.controls n *ᵥ E.gammaHat n ω =
      (fun i => regionalRandomValues μ E.maps E.outcome n i ω) -
        regionalDesign μ E.maps E.treatment E.controls n *ᵥ
          Fin.cases (E.betaHat n ω) (E.gammaHat n ω)
  rw [regionalDesign_mulVec_eq_model]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem source_fittedResidual_whitened_eq_tailResidualProjection
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (CFC.sqrt (E.kernel n))⁻¹ *ᵥ fittedResidual E n ω =
      sourceTailResidualProjection E n *ᵥ
        ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          (fun i => regionalRandomValues μ E.maps E.outcome n i ω)) := by
  let S : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    (CFC.sqrt (E.kernel n))⁻¹
  let Dn : Matrix (Fin (E.maps.N n)) (Fin (E.q + 1)) Real :=
    regionalDesign μ E.maps E.treatment E.controls n
  let A : Matrix (Fin (E.maps.N n)) (Fin (E.q + 1)) Real := sourceWhitenedDesign E n
  let y : Fin (E.maps.N n) → Real :=
    fun i => regionalRandomValues μ E.maps E.outcome n i ω
  let theta : Fin (E.q + 1) → Real := Fin.cases (E.betaHat n ω) (E.gammaHat n ω)
  have hA : A = S * Dn := by
    rfl
  have hfactor : Sᵀ * S = (E.kernel n)⁻¹ := by
    dsimp [S]
    exact inverse_cfcSqrt_adjoint_mul_self (E.kernel n) (E.kernel_posDef n)
  have hfit : fittedResidual E n ω = y - Dn *ᵥ theta := by
    dsimp [y, Dn, theta]
    exact fittedResidual_eq_regionalDesign_residual E n ω
  have hwhitened (theta' : Fin (E.q + 1) → Real) :
      S *ᵥ (y - Dn *ᵥ theta') = S *ᵥ y - A *ᵥ theta' := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hA]
  have hmin : ∀ theta' : Fin (E.q + 1) → Real,
      (S *ᵥ y - A *ᵥ theta) ⬝ᵥ (S *ᵥ y - A *ᵥ theta) ≤
        (S *ᵥ y - A *ᵥ theta') ⬝ᵥ (S *ᵥ y - A *ᵥ theta') := by
    intro theta'
    have hgls := (isGLSMinimizer_iff (E.kernel n)
      (regionalValues μ E.maps E.treatment n)
      (regionalControls μ E.maps E.controls n) y
      (E.betaHat n ω) (E.gammaHat n ω)).mp (E.estimator_minimizes n ω)
    specialize hgls (theta' 0) (fun j => theta' (Fin.succ j))
    rw [glsObjective_eq, glsObjective_eq] at hgls
    have hselected :
        y - (E.betaHat n ω) • regionalValues μ E.maps E.treatment n -
            regionalControls μ E.maps E.controls n *ᵥ E.gammaHat n ω =
          y - Dn *ᵥ theta := by
      dsimp [Dn, theta]
      rw [regionalDesign_mulVec_eq_model]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    have hcandidate :
        y - (theta' 0) • regionalValues μ E.maps E.treatment n -
            regionalControls μ E.maps E.controls n *ᵥ (fun j => theta' (Fin.succ j)) =
          y - Dn *ᵥ theta' := by
      have htheta' :
          Fin.cases (theta' 0) (fun j => theta' (Fin.succ j)) = theta' := by
        ext j
        refine Fin.cases ?_ ?_ j <;> simp
      calc
        y - (theta' 0) • regionalValues μ E.maps E.treatment n -
            regionalControls μ E.maps E.controls n *ᵥ (fun j => theta' (Fin.succ j)) =
            y - Dn *ᵥ Fin.cases (theta' 0) (fun j => theta' (Fin.succ j)) := by
          dsimp [Dn]
          rw [regionalDesign_mulVec_eq_model]
          ext i
          simp only [Pi.sub_apply, Pi.add_apply]
          ring
        _ = y - Dn *ᵥ theta' := by rw [htheta']
    rw [hselected, hcandidate] at hgls
    calc
      (S *ᵥ y - A *ᵥ theta) ⬝ᵥ (S *ᵥ y - A *ᵥ theta) =
          quadraticForm (E.kernel n)⁻¹ (y - Dn *ᵥ theta) := by
        rw [← hwhitened]
        exact (quadraticForm_eq_whitened_dotProduct (E.kernel n) S
          (y - Dn *ᵥ theta) hfactor).symm
      _ ≤ quadraticForm (E.kernel n)⁻¹ (y - Dn *ᵥ theta') := hgls
      _ = (S *ᵥ y - A *ᵥ theta') ⬝ᵥ (S *ᵥ y - A *ᵥ theta') := by
        rw [← hwhitened]
        exact quadraticForm_eq_whitened_dotProduct (E.kernel n) S
          (y - Dn *ᵥ theta') hfactor
  have hresidual : S *ᵥ y - A *ᵥ theta =
      tailResidualProjection A *ᵥ (S *ᵥ y) :=
    leastSquares_residual_eq_tailResidualProjection A (S *ᵥ y) theta
      (by simpa only [A] using sourceWhitenedDesign_gram_det_isUnit E n hrank) hmin
  calc
    (CFC.sqrt (E.kernel n))⁻¹ *ᵥ fittedResidual E n ω = S *ᵥ (y - Dn *ᵥ theta) := by
      rw [hfit]
    _ = S *ᵥ y - A *ᵥ theta := hwhitened theta
    _ = tailResidualProjection A *ᵥ (S *ᵥ y) := hresidual
    _ = sourceTailResidualProjection E n *ᵥ
        ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          (fun i => regionalRandomValues μ E.maps E.outcome n i ω)) := by
      rfl

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem fittedResidual_quadraticForm_eq_tailProjected_norm
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) =
      (sourceTailResidualProjection E n *ᵥ
        ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          (fun i => regionalRandomValues μ E.maps E.outcome n i ω))) ⬝ᵥ
        (sourceTailResidualProjection E n *ᵥ
          ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
            (fun i => regionalRandomValues μ E.maps E.outcome n i ω))) := by
  have hfactor :
      (((CFC.sqrt (E.kernel n))⁻¹)ᵀ * (CFC.sqrt (E.kernel n))⁻¹) =
        (E.kernel n)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      inverse_cfcSqrt_adjoint_mul_self (E.kernel n) (E.kernel_posDef n)
  rw [quadraticForm_eq_whitened_dotProduct (E.kernel n)
    ((CFC.sqrt (E.kernel n))⁻¹) (fittedResidual E n ω) hfactor]
  rw [source_fittedResidual_whitened_eq_tailResidualProjection E n ω hrank]

theorem regionalOutcomeVector_eq_design_add_error_ae
    (E : FixedConditionalExperiment μ P) (n : Nat) :
    ∀ᵐ ω ∂P,
      (fun i => regionalRandomValues μ E.maps E.outcome n i ω) =
        regionalDesign μ E.maps E.treatment E.controls n *ᵥ Fin.cases E.beta E.gamma +
          (fun i => regionalRandomValues μ E.maps E.error n i ω) := by
  filter_upwards [InfillGLSLean.ManuscriptSpecification.L029.regional_structural_model E n]
    with ω hmodel
  ext i
  rw [regionalDesign_mulVec_eq_model]
  have hi := hmodel i
  change regionalRandomValues μ E.maps E.outcome n i ω =
    E.beta * regionalValues μ E.maps E.treatment n i +
      (regionalControls μ E.maps E.controls n *ᵥ E.gamma) i +
        regionalRandomValues μ E.maps E.error n i ω
  simpa only [Matrix.mulVec, dotProduct, regionalControls_apply] using hi

theorem projected_whitened_design_add_eq {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (R S : Matrix ι ι Real) (D : Matrix ι κ Real)
    (hkill : R * S * D = 0) (theta : κ → Real) (e : ι → Real) :
    R *ᵥ (S *ᵥ (D *ᵥ theta + e)) = R *ᵥ (S *ᵥ e) := by
  calc
    R *ᵥ (S *ᵥ (D *ᵥ theta + e)) =
        R *ᵥ (S *ᵥ (D *ᵥ theta) + S *ᵥ e) := by
      rw [Matrix.mulVec_add]
    _ = R *ᵥ (S *ᵥ (D *ᵥ theta)) + R *ᵥ (S *ᵥ e) := by
      rw [Matrix.mulVec_add]
    _ = ((R * S) * D) *ᵥ theta + R *ᵥ (S *ᵥ e) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = R *ᵥ (S *ᵥ e) := by rw [hkill, Matrix.zero_mulVec, zero_add]

/-- Euclidean norm contraction for a symmetric idempotent finite projection. -/
theorem orthogonal_projection_dotProduct_contract {ι : Type*}
    [Fintype ι] [DecidableEq ι] (R : Matrix ι ι Real)
    (htranspose : Rᵀ = R) (hidempotent : R * R = R) (x : ι → Real) :
    (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ x ⬝ᵥ x := by
  have hprojected : (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ (R *ᵥ x) := by
    calc
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ Rᵀ *ᵥ (R *ᵥ x) :=
        (Matrix.dotProduct_transpose_mulVec R x (R *ᵥ x)).symm
      _ = x ⬝ᵥ R *ᵥ (R *ᵥ x) := by rw [htranspose]
      _ = x ⬝ᵥ (R * R) *ᵥ x := by rw [Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ (R *ᵥ x) := by rw [hidempotent]
  have hnonneg : 0 ≤ (x - R *ᵥ x) ⬝ᵥ (x - R *ᵥ x) := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => by
      simpa only [pow_two] using sq_nonneg ((x - R *ᵥ x) i)
  have hresidual_norm :
      (x - R *ᵥ x) ⬝ᵥ (x - R *ᵥ x) = x ⬝ᵥ x - x ⬝ᵥ (R *ᵥ x) := by
    rw [dotProduct_sub]
    rw [dotProduct_comm (x - R *ᵥ x) x,
      dotProduct_comm (x - R *ᵥ x) (R *ᵥ x)]
    simp only [dotProduct_sub]
    rw [dotProduct_comm (R *ᵥ x) x, hprojected]
    ring
  have hdecomposition :
      x ⬝ᵥ x - (R *ᵥ x) ⬝ᵥ (R *ᵥ x) =
        (x - R *ᵥ x) ⬝ᵥ (x - R *ᵥ x) := by
    rw [hprojected]
    exact hresidual_norm.symm
  linarith

theorem projected_mean_energy_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K R S : Matrix ι ι Real) (W : Matrix ι κ Real)
    (m : ι → Real) (c : κ → Real)
    (htranspose : Rᵀ = R) (hidempotent : R * R = R)
    (hfactor : Sᵀ * S = K⁻¹) (hcontrols : R * S * W = 0) :
    (R *ᵥ (S *ᵥ m)) ⬝ᵥ (R *ᵥ (S *ᵥ m)) ≤
      quadraticForm K⁻¹ (m - W *ᵥ c) := by
  let offset : ι → Real := m - W *ᵥ c
  have hcontrols_vec : (R * S) *ᵥ (W *ᵥ c) = 0 := by
    calc
      (R * S) *ᵥ (W *ᵥ c) = (R * S * W) *ᵥ c := by
        rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hcontrols, Matrix.zero_mulVec]
  have hprojected_mean : R *ᵥ (S *ᵥ m) = R *ᵥ (S *ᵥ offset) := by
    change R *ᵥ (S *ᵥ m) = R *ᵥ (S *ᵥ (m - W *ᵥ c))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_sub, hcontrols_vec, sub_zero]
  have henergy :
      (S *ᵥ offset) ⬝ᵥ (S *ᵥ offset) = quadraticForm K⁻¹ offset := by
    calc
      (S *ᵥ offset) ⬝ᵥ (S *ᵥ offset) =
          offset ⬝ᵥ Sᵀ *ᵥ (S *ᵥ offset) :=
        (Matrix.dotProduct_transpose_mulVec S offset (S *ᵥ offset)).symm
      _ = offset ⬝ᵥ (Sᵀ * S) *ᵥ offset := by rw [Matrix.mulVec_mulVec]
      _ = offset ⬝ᵥ K⁻¹ *ᵥ offset := by rw [hfactor]
      _ = quadraticForm K⁻¹ offset :=
        (InfillGLSLean.quadraticForm_eq_dotProduct_mulVec K⁻¹ offset).symm
  rw [hprojected_mean]
  calc
    (R *ᵥ (S *ᵥ offset)) ⬝ᵥ (R *ᵥ (S *ᵥ offset)) ≤
        (S *ᵥ offset) ⬝ᵥ (S *ᵥ offset) :=
      orthogonal_projection_dotProduct_contract R htranspose hidempotent (S *ᵥ offset)
    _ = quadraticForm K⁻¹ (m - W *ᵥ c) := by
      simpa only [offset] using henergy

/-- The exact fixed-mean energy bound for the literal complete-design
residual projection. -/
theorem source_tailProjected_mean_energy_le_meanEnergy
    (E : FixedConditionalExperiment μ P) (mean : FixedMeanAssumption E)
    (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
      regionalConditionalMean E.maps P E.error n)) ⬝ᵥ
        (sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          regionalConditionalMean E.maps P E.error n)) ≤ meanEnergy E mean.c n := by
  have hfactor : (((CFC.sqrt (E.kernel n))⁻¹)ᵀ * (CFC.sqrt (E.kernel n))⁻¹) =
      (E.kernel n)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      inverse_cfcSqrt_adjoint_mul_self (E.kernel n) (E.kernel_posDef n)
  have h := projected_mean_energy_le (E.kernel n) (sourceTailResidualProjection E n)
    ((CFC.sqrt (E.kernel n))⁻¹) (regionalControls μ E.maps E.controls n)
    (regionalConditionalMean E.maps P E.error n) mean.c
    (sourceTailResidualProjection_transpose E n)
    (sourceTailResidualProjection_idempotent E n hrank)
    hfactor (sourceTailResidualProjection_kills_controls E n hrank)
  simpa only [meanEnergy_eq, meanOffset] using h

/-- The deterministic projected conditional mean `b_n = P_n S_n m_n` from
Appendix `app:scale`. -/
noncomputable def sourceProjectedMean (E : FixedConditionalExperiment μ P)
    (n : Nat) : Fin (E.maps.N n) → Real :=
  sourceTailResidualProjection E n *ᵥ
    ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ regionalConditionalMean E.maps P E.error n)

/-- The exact finite noncentral quadratic statistic obtained by applying the
literal residual projection to the centered regional errors.  This is a
named intermediate object only; it is not a new residual-scale estimator. -/
noncomputable def sourceResidualQuadraticCore
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω) : Real :=
  InfillGLSLean.FiniteWickBridge.noncentralSquareSum
    (fun i =>
      InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
        E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i))
    (sourceProjectedMean E n) ω

/-- Coordinate identification of the projected centered error vector with the
deterministic row scores used by the scalar Wick bridge. -/
theorem source_tailProjectedCenteredError_eq_scores
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω) :
    sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
      (fun i => centeredFiniteError
        (regionalRandomValues μ E.maps E.error n)
        (regionalConditionalMean E.maps P E.error n) i ω)) =
      fun i =>
        InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
          E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω := by
  let X : Fin (E.maps.N n) → Real := fun i => centeredFiniteError
    (regionalRandomValues μ E.maps E.error n)
    (regionalConditionalMean E.maps P E.error n) i ω
  change sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ X) = _
  calc
    sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ X) =
        (sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) *ᵥ X :=
      Matrix.mulVec_mulVec X (sourceTailResidualProjection E n) ((CFC.sqrt (E.kernel n))⁻¹)
    _ = fun i =>
        InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
          E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω := by
      ext i
      rw [InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore_apply]
      simp only [X, finiteWeightedScore_apply, Matrix.mulVec, dotProduct]

theorem rawRegionalError_eq_mean_add_centered
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω) :
    (fun i => regionalRandomValues μ E.maps E.error n i ω) =
      regionalConditionalMean E.maps P E.error n +
        (fun i => centeredFiniteError
          (regionalRandomValues μ E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n) i ω) := by
  ext i
  simp only [Pi.add_apply, centeredFiniteError_apply]
  ring

/-- The source structural model, after applying the complete-design residual
projection and whitening.  It is deliberately an AE statement because the
regional structural model is only asserted under the fixed law almost
everywhere. -/
theorem source_tailProjectedOutcome_eq_tailProjectedError_ae
    (E : FixedConditionalExperiment μ P) (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    ∀ᵐ ω ∂P,
      sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
        (fun i => regionalRandomValues μ E.maps E.outcome n i ω)) =
      sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
        (fun i => regionalRandomValues μ E.maps E.error n i ω)) := by
  let R : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    sourceTailResidualProjection E n
  let S : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    (CFC.sqrt (E.kernel n))⁻¹
  let Dn : Matrix (Fin (E.maps.N n)) (Fin (E.q + 1)) Real :=
    regionalDesign μ E.maps E.treatment E.controls n
  let theta : Fin (E.q + 1) → Real := Fin.cases E.beta E.gamma
  let y : Ω → Fin (E.maps.N n) → Real :=
    fun ω i => regionalRandomValues μ E.maps E.outcome n i ω
  let e : Ω → Fin (E.maps.N n) → Real :=
    fun ω i => regionalRandomValues μ E.maps E.error n i ω
  change ∀ᵐ ω ∂P, R *ᵥ (S *ᵥ y ω) = R *ᵥ (S *ᵥ e ω)
  have hkill : R * S * Dn = 0 := by
    dsimp [R, S, Dn]
    simpa only [sourceWhitenedDesign, Matrix.mul_assoc] using
      sourceTailResidualProjection_mul_whitenedDesign E n hrank
  filter_upwards [regionalOutcomeVector_eq_design_add_error_ae E n] with ω hmodel
  have hmodel' : y ω = Dn *ᵥ theta + e ω := by
    dsimp [y, Dn, theta, e]
    exact hmodel
  rw [hmodel']
  exact projected_whitened_design_add_eq R S Dn hkill theta (e ω)

/-- Pointwise decomposition of the projected raw error into the projected
conditional mean and the literal centered row-score vector. -/
theorem source_tailProjectedError_eq_projectedMean_add_scores
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω) :
    sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
      (fun i => regionalRandomValues μ E.maps E.error n i ω)) =
      sourceProjectedMean E n +
        fun i =>
          InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
            E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω := by
  rw [rawRegionalError_eq_mean_add_centered E n ω]
  rw [Matrix.mulVec_add, Matrix.mulVec_add]
  rw [source_tailProjectedCenteredError_eq_scores]
  rfl

theorem noncentralSquareSum_eq_shifted_dotProduct
    {ι Ω : Type*} [Fintype ι] (X : ι → Ω → Real) (b : ι → Real) (ω : Ω) :
    InfillGLSLean.FiniteWickBridge.noncentralSquareSum X b ω =
      (b + fun i => X i ω) ⬝ᵥ (b + fun i => X i ω) := by
  unfold InfillGLSLean.FiniteWickBridge.noncentralSquareSum
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply]
  ring

/-- The source structural model and the literal centering identity combined at
the projected, whitened level.  The equality remains almost everywhere: the
fixed conditional experiment only supplies the regional structural model at
that scope. -/
theorem source_tailProjectedOutcome_eq_projectedMean_add_scores_ae
    (E : FixedConditionalExperiment μ P) (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    ∀ᵐ ω ∂P,
      sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
        (fun i => regionalRandomValues μ E.maps E.outcome n i ω)) =
      sourceProjectedMean E n +
        fun i =>
          InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
            E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω := by
  filter_upwards [source_tailProjectedOutcome_eq_tailProjectedError_ae E n hrank]
    with ω houtcome
  calc
    sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
        (fun i => regionalRandomValues μ E.maps E.outcome n i ω)) =
        sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          (fun i => regionalRandomValues μ E.maps E.error n i ω)) := houtcome
    _ = sourceProjectedMean E n +
        fun i =>
          InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
            E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω :=
      source_tailProjectedError_eq_projectedMean_add_scores E n ω

/-- Pointwise expansion of the exact source-facing noncentral quadratic core. -/
theorem sourceResidualQuadraticCore_eq_shifted_dotProduct
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω) :
    sourceResidualQuadraticCore E n ω =
      (sourceProjectedMean E n +
        fun i =>
          InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
            E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω) ⬝ᵥ
      (sourceProjectedMean E n +
        fun i =>
          InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
            E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω) := by
  unfold sourceResidualQuadraticCore
  exact noncentralSquareSum_eq_shifted_dotProduct _ _ _

/-- Exact source-facing identification of the fitted-residual quadratic form
with the row-score noncentral quadratic core.  This is an AE bridge, not a
replacement of the fitted residual or of the experiment's structural model. -/
theorem fittedResidual_quadraticForm_eq_sourceResidualQuadraticCore_ae
    (E : FixedConditionalExperiment μ P) (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    ∀ᵐ ω ∂P,
      quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) =
        sourceResidualQuadraticCore E n ω := by
  filter_upwards [source_tailProjectedOutcome_eq_projectedMean_add_scores_ae E n hrank]
    with ω hprojected
  calc
    quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) =
        (sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          (fun i => regionalRandomValues μ E.maps E.outcome n i ω))) ⬝ᵥ
        (sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          (fun i => regionalRandomValues μ E.maps E.outcome n i ω))) :=
      fittedResidual_quadraticForm_eq_tailProjected_norm E n ω hrank
    _ =
        (sourceProjectedMean E n +
          fun i =>
            InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
              E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω) ⬝ᵥ
        (sourceProjectedMean E n +
          fun i =>
            InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
              E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω) := by
      rw [hprojected]
    _ = sourceResidualQuadraticCore E n ω :=
      (sourceResidualQuadraticCore_eq_shifted_dotProduct E n ω).symm

/-- The covariance of the literal projected row scores is `P Γ P`, with the
transpose orientation made explicit before using symmetry of the residual
projection. -/
theorem source_rowScoreCovariance_eq
    (E : FixedConditionalExperiment μ P) (n : Nat) :
    (sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) *
        trueCovariance E n *
        (sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹)ᵀ =
      sourceTailResidualProjection E n * sourceTransformedCovariance E n *
        sourceTailResidualProjection E n := by
  unfold sourceTransformedCovariance
  rw [Matrix.transpose_mul, sourceTailResidualProjection_transpose E n]
  simp only [Matrix.mul_assoc]

/-- Trace simplification for an idempotent residual projection. -/
theorem source_trace_projectedCovariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R Gamma : Matrix ι ι Real) (hR : R * R = R) :
    (R * Gamma * R).trace = (R * Gamma).trace := by
  calc
    (R * Gamma * R).trace = ((R * Gamma) * R).trace := rfl
    _ = (R * (R * Gamma)).trace := Matrix.trace_mul_comm _ _
    _ = ((R * R) * Gamma).trace := by rw [Matrix.mul_assoc]
    _ = (R * Gamma).trace := by rw [hR]

/-- A lower Loewner sandwich transfers to the trace over an orthogonal
idempotent projection. -/
theorem trace_lower_of_projected_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R Gamma : Matrix ι ι Real) (htranspose : Rᵀ = R)
    (hidempotent : R * R = R) (a : Real)
    (hsandwich : (Gamma - a • (1 : Matrix ι ι Real)).PosSemidef) :
    a * R.trace ≤ (R * Gamma).trace := by
  have hprojected := hsandwich.conjTranspose_mul_mul_same R
  have hprojected' : (Rᵀ * (Gamma - a • (1 : Matrix ι ι Real)) * R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hprojected
  have hrewrite : Rᵀ * (Gamma - a • (1 : Matrix ι ι Real)) * R =
      R * Gamma * R - a • R := by
    calc
      Rᵀ * (Gamma - a • (1 : Matrix ι ι Real)) * R =
          R * (Gamma - a • (1 : Matrix ι ι Real)) * R := by rw [htranspose]
      _ = (R * Gamma - R * (a • (1 : Matrix ι ι Real))) * R := by
        rw [Matrix.mul_sub]
      _ = R * Gamma * R - (R * (a • (1 : Matrix ι ι Real)) * R) := by
        rw [Matrix.sub_mul]
      _ = R * Gamma * R - a • ((R * (1 : Matrix ι ι Real)) * R) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = R * Gamma * R - a • R := by
        rw [Matrix.mul_one, hidempotent]
  rw [hrewrite] at hprojected'
  have hnonneg : 0 ≤ (R * Gamma * R - a • R).trace := hprojected'.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul,
    source_trace_projectedCovariance R Gamma hidempotent] at hnonneg
  simp only [smul_eq_mul] at hnonneg
  linarith

/-- An upper Loewner sandwich transfers to the trace over an orthogonal
idempotent projection. -/
theorem trace_upper_of_projected_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R Gamma : Matrix ι ι Real) (htranspose : Rᵀ = R)
    (hidempotent : R * R = R) (a : Real)
    (hsandwich : (a • (1 : Matrix ι ι Real) - Gamma).PosSemidef) :
    (R * Gamma).trace ≤ a * R.trace := by
  have hprojected := hsandwich.conjTranspose_mul_mul_same R
  have hprojected' : (Rᵀ * (a • (1 : Matrix ι ι Real) - Gamma) * R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hprojected
  have hrewrite : Rᵀ * (a • (1 : Matrix ι ι Real) - Gamma) * R =
      a • R - R * Gamma * R := by
    calc
      Rᵀ * (a • (1 : Matrix ι ι Real) - Gamma) * R =
          R * (a • (1 : Matrix ι ι Real) - Gamma) * R := by rw [htranspose]
      _ = (R * (a • (1 : Matrix ι ι Real)) - R * Gamma) * R := by
        rw [Matrix.mul_sub]
      _ = R * (a • (1 : Matrix ι ι Real)) * R - R * Gamma * R := by
        rw [Matrix.sub_mul]
      _ = a • ((R * (1 : Matrix ι ι Real)) * R) - R * Gamma * R := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = a • R - R * Gamma * R := by
        rw [Matrix.mul_one, hidempotent]
  rw [hrewrite] at hprojected'
  have hnonneg : 0 ≤ (a • R - R * Gamma * R).trace := hprojected'.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul,
    source_trace_projectedCovariance R Gamma hidempotent] at hnonneg
  simp only [smul_eq_mul] at hnonneg
  linarith

/-- The transformed covariance sandwich gives the exact trace bounds used in
Appendix `app:scale`, after identifying the projection trace with the literal
residual divisor. -/
theorem sourceTransformedCovariance_projected_trace_bounds
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 ≤ E.maps.N n) :
    (covariance.sigmaSquared / (1 + covariance.delta n)) *
        ((E.maps.N n - E.q - 1 : Nat) : Real) ≤
      (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace ∧
    (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace ≤
      (covariance.sigmaSquared / (1 - covariance.delta n)) *
        ((E.maps.N n - E.q - 1 : Nat) : Real) := by
  rcases sourceTransformedCovariance_sandwich E covariance n hn with ⟨hlower, hupper⟩
  have htranspose : (sourceTailResidualProjection E n)ᵀ =
      sourceTailResidualProjection E n := sourceTailResidualProjection_transpose E n
  have hidempotent : sourceTailResidualProjection E n *
      sourceTailResidualProjection E n = sourceTailResidualProjection E n :=
    sourceTailResidualProjection_idempotent E n hrank
  have htrace : (sourceTailResidualProjection E n).trace =
      ((E.maps.N n - E.q - 1 : Nat) : Real) :=
    trace_sourceTailResidualProjection_eq_scale_divisor E n hrank hdivisor
  constructor
  · rw [← htrace]
    exact trace_lower_of_projected_sandwich (sourceTailResidualProjection E n)
      (sourceTransformedCovariance E n) htranspose hidempotent
      (covariance.sigmaSquared / (1 + covariance.delta n)) hlower
  · rw [← htrace]
    exact trace_upper_of_projected_sandwich (sourceTailResidualProjection E n)
      (sourceTransformedCovariance E n) htranspose hidempotent
      (covariance.sigmaSquared / (1 - covariance.delta n)) hupper

/-- An upper Loewner sandwich controls the quadratic form of any deterministic
vector. -/
theorem quadraticForm_upper_of_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Gamma : Matrix ι ι Real) (a : Real) (b : ι → Real)
    (hsandwich : (a • (1 : Matrix ι ι Real) - Gamma).PosSemidef) :
    quadraticForm Gamma b ≤ a * (b ⬝ᵥ b) := by
  have hnonneg : 0 ≤ b ⬝ᵥ ((a • (1 : Matrix ι ι Real) - Gamma) *ᵥ b) := by
    simpa using hsandwich.dotProduct_mulVec_nonneg b
  rw [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul] at hnonneg
  simp only [smul_eq_mul] at hnonneg
  rw [quadraticForm_eq_dotProduct_mulVec]
  linarith

/-- The projection of an upper Loewner sandwich remains positive
semidefinite in the exact `a P - P Γ P` orientation. -/
theorem projected_upper_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R Gamma : Matrix ι ι Real) (htranspose : Rᵀ = R)
    (hidempotent : R * R = R) (a : Real)
    (hsandwich : (a • (1 : Matrix ι ι Real) - Gamma).PosSemidef) :
    (a • R - R * Gamma * R).PosSemidef := by
  have hprojected := hsandwich.conjTranspose_mul_mul_same R
  have hprojected' : (Rᵀ * (a • (1 : Matrix ι ι Real) - Gamma) * R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hprojected
  have hrewrite : Rᵀ * (a • (1 : Matrix ι ι Real) - Gamma) * R =
      a • R - R * Gamma * R := by
    calc
      Rᵀ * (a • (1 : Matrix ι ι Real) - Gamma) * R =
          R * (a • (1 : Matrix ι ι Real) - Gamma) * R := by rw [htranspose]
      _ = (R * (a • (1 : Matrix ι ι Real)) - R * Gamma) * R := by
        rw [Matrix.mul_sub]
      _ = R * (a • (1 : Matrix ι ι Real)) * R - R * Gamma * R := by
        rw [Matrix.sub_mul]
      _ = a • ((R * (1 : Matrix ι ι Real)) * R) - R * Gamma * R := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = a • R - R * Gamma * R := by
        rw [Matrix.mul_one, hidempotent]
  rw [hrewrite] at hprojected'
  exact hprojected'

/-- The trace of a product of two finite real PSD matrices is nonnegative.
This local bridge uses the CFC square root of the second factor and does not
assume the two matrices commute. -/
theorem trace_mul_nonneg_of_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι Real) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let S : Matrix ι ι Real := CFC.sqrt B
  have hSsymm : Sᵀ = S := by
    dsimp [S]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hsq : S * S = B := by
    dsimp [S]
    simpa only [pow_two] using CFC.sq_sqrt B hB.nonneg
  have hcongruent : (S * A * Sᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.mul_mul_conjTranspose_same S
  calc
    0 ≤ (S * A * Sᵀ).trace := hcongruent.trace_nonneg
    _ = (A * Sᵀ * S).trace := (Matrix.trace_mul_cycle A Sᵀ S).symm
    _ = (A * (S * S)).trace := by rw [hSsymm, Matrix.mul_assoc]
    _ = (A * B).trace := by rw [hsq]

/-- The lower covariance sandwich, together with the positive working kernel,
implies positivity of the literal true regional covariance. -/
theorem trueCovariance_posSemidef_of_covariance
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n) :
    (trueCovariance E n).PosSemidef := by
  rcases covariance.sandwich n hn with ⟨hdelta_nonneg, hdelta_lt_one, hlower, _⟩
  let a : Real := covariance.sigmaSquared / (1 + covariance.delta n)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg covariance.sigmaSquared_pos.le (by linarith)
  have hscaled : (a • E.kernel n).PosSemidef :=
    (E.kernel_posDef n).posSemidef.smul ha
  have hsum := hlower.add hscaled
  change (trueCovariance E n - a • E.kernel n).PosSemidef at hlower
  simpa only [a, sub_add_cancel] using hsum

/-- Positivity of the transformed covariance in its explicit source
orientation `S Σ Sᵀ`. -/
theorem sourceTransformedCovariance_posSemidef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n) :
    (sourceTransformedCovariance E n).PosSemidef := by
  unfold sourceTransformedCovariance
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (trueCovariance_posSemidef_of_covariance E covariance n hn).mul_mul_conjTranspose_same
      ((CFC.sqrt (E.kernel n))⁻¹)

/-- The squared projected-covariance trace is bounded by the square of the
upper sandwich scale times the projection rank trace.  This is the finite
correlated-matrix calculation used in Appendix `app:scale`. -/
theorem trace_square_projectedCovariance_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R Gamma : Matrix ι ι Real) (htranspose : Rᵀ = R)
    (hidempotent : R * R = R) (a : Real) (ha : 0 ≤ a)
    (hGamma : Gamma.PosSemidef)
    (hupper : (a • (1 : Matrix ι ι Real) - Gamma).PosSemidef) :
    (R * Gamma * R * Gamma).trace ≤ a ^ 2 * R.trace := by
  let A : Matrix ι ι Real := R * Gamma * R
  have hA : A.PosSemidef := by
    have hcongruent := hGamma.conjTranspose_mul_mul_same R
    have hcongruent' : (Rᵀ * Gamma * R).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hcongruent
    rw [htranspose] at hcongruent'
    simpa only [A] using hcongruent'
  have hB : (a • R - A).PosSemidef := by
    simpa only [A] using
      projected_upper_sandwich R Gamma htranspose hidempotent a hupper
  have hRA : R * A = A := by
    dsimp [A]
    calc
      R * (R * Gamma * R) = (R * R) * Gamma * R := by
        simp only [Matrix.mul_assoc]
      _ = R * Gamma * R := by rw [hidempotent]
  have hproduct_nonneg : 0 ≤ ((a • R - A) * A).trace :=
    trace_mul_nonneg_of_posSemidef (a • R - A) A hB hA
  have hproduct : ((a • R - A) * A).trace =
      a * A.trace - (A * A).trace := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, hRA, Matrix.trace_smul]
    simp only [smul_eq_mul]
  have hfirst : (A * A).trace ≤ a * A.trace := by
    rw [hproduct] at hproduct_nonneg
    linarith
  have htraceA : A.trace ≤ a * R.trace := by
    calc
      A.trace = (R * Gamma).trace := by
        dsimp [A]
        exact source_trace_projectedCovariance R Gamma hidempotent
      _ ≤ a * R.trace :=
        trace_upper_of_projected_sandwich R Gamma htranspose hidempotent a hupper
  have hsecond : a * A.trace ≤ a * (a * R.trace) :=
    mul_le_mul_of_nonneg_left htraceA ha
  have htrace_square : ((R * Gamma * R) * (R * Gamma * R)).trace =
      (R * Gamma * R * Gamma).trace := by
    have hs : (R * Gamma * R) * (R * Gamma * R) =
        R * (Gamma * (R * (Gamma * R))) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R R, hidempotent]
    rw [hs]
    calc
      (R * (Gamma * (R * (Gamma * R)))).trace =
          ((R * (Gamma * (R * Gamma))) * R).trace := by
        simp only [Matrix.mul_assoc]
      _ = (R * (R * (Gamma * (R * Gamma)))).trace := Matrix.trace_mul_comm _ _
      _ = ((R * R) * (Gamma * (R * Gamma))).trace := by rw [Matrix.mul_assoc]
      _ = (R * (Gamma * (R * Gamma))).trace := by rw [hidempotent]
      _ = (R * Gamma * R * Gamma).trace := by simp only [Matrix.mul_assoc]
  calc
    (R * Gamma * R * Gamma).trace = (A * A).trace := by
      dsimp [A]
      exact htrace_square.symm
    _ ≤ a * A.trace := hfirst
    _ ≤ a * (a * R.trace) := hsecond
    _ = a ^ 2 * R.trace := by ring

/-- Source specialization of the correlated quadratic-trace bound, with the
projection trace replaced by the literal residual degrees of freedom. -/
theorem sourceTransformedCovariance_square_trace_upper
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 ≤ E.maps.N n) :
    (sourceTailResidualProjection E n * sourceTransformedCovariance E n *
      sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace ≤
      (covariance.sigmaSquared / (1 - covariance.delta n)) ^ 2 *
        ((E.maps.N n - E.q - 1 : Nat) : Real) := by
  rcases covariance.sandwich n hn with ⟨hdelta_nonneg, hdelta_lt_one, _, _⟩
  rcases sourceTransformedCovariance_sandwich E covariance n hn with ⟨_, hupper⟩
  have hscale_nonneg : 0 ≤ covariance.sigmaSquared / (1 - covariance.delta n) :=
    div_nonneg covariance.sigmaSquared_pos.le (by linarith)
  have htrace := trace_square_projectedCovariance_upper
    (sourceTailResidualProjection E n) (sourceTransformedCovariance E n)
    (sourceTailResidualProjection_transpose E n)
    (sourceTailResidualProjection_idempotent E n hrank)
    (covariance.sigmaSquared / (1 - covariance.delta n)) hscale_nonneg
    (sourceTransformedCovariance_posSemidef E covariance n hn) hupper
  rw [trace_sourceTailResidualProjection_eq_scale_divisor E n hrank hdivisor] at htrace
  exact htrace

/-- Strict positivity of the paper's literal residual degrees of freedom on
the tail selected by L-035. -/
theorem residual_divisor_pos
    (E : FixedConditionalExperiment μ P) (n : Nat)
    (hdivisor : E.q + 1 < E.maps.N n) :
    0 < ((E.maps.N n - E.q - 1 : Nat) : Real) := by
  have hnat : 0 < E.maps.N n - E.q - 1 := by omega
  exact_mod_cast hnat

/-- The public source expansion of the displayed residual-scale branch,
re-exported here only to keep the tail calculation named locally. -/
theorem residualScale_eq_literal_quotient
    (E : FixedConditionalExperiment μ P) (n : Nat) (ω : Ω)
    (hdivisor : E.q + 1 < E.maps.N n) :
    residualScale E n ω =
      quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) /
        ((E.maps.N n - E.q - 1 : Nat) : Real) :=
  residualScale_eq_quotient_of_divisor E n ω hdivisor

/-- The fixed-mean condition controls the noncentral quadratic-form term in
the exact residual-numerator variance formula. -/
theorem sourceProjectedMean_quadraticForm_upper
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    quadraticForm (sourceTransformedCovariance E n) (sourceProjectedMean E n) ≤
      (covariance.sigmaSquared / (1 - covariance.delta n)) * meanEnergy E mean.c n := by
  rcases covariance.sandwich n hn with ⟨hdelta_nonneg, hdelta_lt_one, _, _⟩
  rcases sourceTransformedCovariance_sandwich E covariance n hn with ⟨_, hupper⟩
  have hscale_nonneg : 0 ≤ covariance.sigmaSquared / (1 - covariance.delta n) :=
    div_nonneg covariance.sigmaSquared_pos.le (by linarith)
  calc
    quadraticForm (sourceTransformedCovariance E n) (sourceProjectedMean E n) ≤
        (covariance.sigmaSquared / (1 - covariance.delta n)) *
          (sourceProjectedMean E n ⬝ᵥ sourceProjectedMean E n) :=
      quadraticForm_upper_of_sandwich (sourceTransformedCovariance E n)
        (covariance.sigmaSquared / (1 - covariance.delta n))
        (sourceProjectedMean E n) hupper
    _ ≤ (covariance.sigmaSquared / (1 - covariance.delta n)) * meanEnergy E mean.c n :=
      mul_le_mul_of_nonneg_left
        (source_tailProjected_mean_energy_le_meanEnergy E mean n hrank) hscale_nonneg

/-- The projected conditional mean is fixed by the residual projection. -/
theorem sourceTailResidualProjection_mulVec_sourceProjectedMean
    (E : FixedConditionalExperiment μ P) (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    sourceTailResidualProjection E n *ᵥ sourceProjectedMean E n =
      sourceProjectedMean E n := by
  unfold sourceProjectedMean
  calc
    sourceTailResidualProjection E n *ᵥ
        (sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          regionalConditionalMean E.maps P E.error n)) =
        (sourceTailResidualProjection E n * sourceTailResidualProjection E n) *ᵥ
          ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
            regionalConditionalMean E.maps P E.error n) := by
      rw [Matrix.mulVec_mulVec]
    _ = sourceTailResidualProjection E n *ᵥ ((CFC.sqrt (E.kernel n))⁻¹ *ᵥ
          regionalConditionalMean E.maps P E.error n) := by
      rw [sourceTailResidualProjection_idempotent E n hrank]

/-- Exact finite expectation of the projected source quadratic core.  This
is the first displayed numerator identity in Appendix `app:scale`, still
expressed before division by its literal residual degrees of freedom. -/
theorem sourceResidualQuadraticCore_integral
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (∫ ω, sourceResidualQuadraticCore E n ω ∂P) =
      (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        sourceProjectedMean E n ⬝ᵥ sourceProjectedMean E n := by
  let R : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    sourceTailResidualProjection E n
  let S : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    (CFC.sqrt (E.kernel n))⁻¹
  let b : Fin (E.maps.N n) → Real := sourceProjectedMean E n
  let Gamma : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    sourceTransformedCovariance E n
  have hraw :=
    InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.rowScore_noncentralSquareSum_integral
      E covariance n hn (R * S) b
  have hcov :
      (R * S) * trueCovariance E n * (R * S)ᵀ = R * Gamma * R := by
    dsimp [R, S, Gamma]
    exact source_rowScoreCovariance_eq E n
  have htrace : (R * Gamma * R).trace = (R * Gamma).trace :=
    source_trace_projectedCovariance R Gamma
      (by
        dsimp [R]
        exact sourceTailResidualProjection_idempotent E n hrank)
  change (∫ ω, InfillGLSLean.FiniteWickBridge.noncentralSquareSum
    (fun i =>
      InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
        E n ((R * S) i)) b ω ∂P) = (R * Gamma).trace + b ⬝ᵥ b
  calc
    (∫ ω, InfillGLSLean.FiniteWickBridge.noncentralSquareSum
        (fun i =>
          InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
            E n ((R * S) i)) b ω ∂P) =
        ((R * S) * trueCovariance E n * (R * S)ᵀ).trace + b ⬝ᵥ b := hraw
    _ = (R * Gamma * R).trace + b ⬝ᵥ b := by rw [hcov]
    _ = (R * Gamma).trace + b ⬝ᵥ b := by rw [htrace]

/-- Square-trace simplification for an idempotent residual projection. -/
theorem source_trace_square_projectedCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R Gamma : Matrix ι ι Real) (hR : R * R = R) :
    ((R * Gamma * R) * (R * Gamma * R)).trace =
      (R * Gamma * R * Gamma).trace := by
  have hs : (R * Gamma * R) * (R * Gamma * R) =
      R * (Gamma * (R * (Gamma * R))) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R, hR]
  rw [hs]
  calc
    (R * (Gamma * (R * (Gamma * R)))).trace =
        ((R * (Gamma * (R * Gamma))) * R).trace := by
      simp only [Matrix.mul_assoc]
    _ = (R * (R * (Gamma * (R * Gamma)))).trace := Matrix.trace_mul_comm _ _
    _ = ((R * R) * (Gamma * (R * Gamma))).trace := by rw [Matrix.mul_assoc]
    _ = (R * (Gamma * (R * Gamma))).trace := by rw [hR]
    _ = (R * Gamma * R * Gamma).trace := by simp only [Matrix.mul_assoc]

/-- Quadratic-form simplification for a mean vector already in the image of a
symmetric residual projection. -/
theorem source_quadraticForm_projectedCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R Gamma : Matrix ι ι Real) (hR : R.IsSymm) (b : ι → Real)
    (hb : R *ᵥ b = b) :
    quadraticForm (R * Gamma * R) b = quadraticForm Gamma b := by
  rw [quadraticForm_eq_dotProduct_mulVec, quadraticForm_eq_dotProduct_mulVec]
  calc
    b ⬝ᵥ (R * Gamma * R) *ᵥ b = b ⬝ᵥ R *ᵥ (Gamma *ᵥ (R *ᵥ b)) := by
      congr 1
      rw [← Matrix.mulVec_mulVec b (R * Gamma) R,
        ← Matrix.mulVec_mulVec (R *ᵥ b) R Gamma]
    _ = b ⬝ᵥ R *ᵥ (Gamma *ᵥ b) := by rw [hb]
    _ = (Gamma *ᵥ b) ⬝ᵥ (R *ᵥ b) := hR.dotProduct_mulVec_comm
    _ = (R *ᵥ b) ⬝ᵥ (Gamma *ᵥ b) := dotProduct_comm _ _
    _ = b ⬝ᵥ (Gamma *ᵥ b) := by rw [hb]

/-- Exact finite variance of the projected source quadratic core.  This is
the second displayed numerator identity in Appendix `app:scale`; it retains
the correlated `P Γ P Γ` term rather than introducing coordinate
independence. -/
theorem sourceResidualQuadraticCore_variance
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    Var[sourceResidualQuadraticCore E n; P] =
      2 * (sourceTailResidualProjection E n * sourceTransformedCovariance E n *
        sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        4 * quadraticForm (sourceTransformedCovariance E n) (sourceProjectedMean E n) := by
  let R : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    sourceTailResidualProjection E n
  let S : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    (CFC.sqrt (E.kernel n))⁻¹
  let b : Fin (E.maps.N n) → Real := sourceProjectedMean E n
  let Gamma : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    sourceTransformedCovariance E n
  have hraw :=
    InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.rowScore_noncentralSquareSum_variance
      E covariance n hn (R * S) b
  have hcov :
      (R * S) * trueCovariance E n * (R * S)ᵀ = R * Gamma * R := by
    dsimp [R, S, Gamma]
    exact source_rowScoreCovariance_eq E n
  have hR : R * R = R := by
    dsimp [R]
    exact sourceTailResidualProjection_idempotent E n hrank
  have hsymmetric : R.IsSymm := by
    dsimp [R]
    exact sourceTailResidualProjection_transpose E n
  have hb : R *ᵥ b = b := by
    dsimp [R, b]
    exact sourceTailResidualProjection_mulVec_sourceProjectedMean E n hrank
  change Var[InfillGLSLean.FiniteWickBridge.noncentralSquareSum
    (fun i =>
      InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
        E n ((R * S) i)) b; P] =
      2 * (R * Gamma * R * Gamma).trace + 4 * quadraticForm Gamma b
  calc
    Var[InfillGLSLean.FiniteWickBridge.noncentralSquareSum
        (fun i =>
          InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
            E n ((R * S) i)) b; P] =
        2 * (((R * S) * trueCovariance E n * (R * S)ᵀ) *
          ((R * S) * trueCovariance E n * (R * S)ᵀ)).trace +
            4 * quadraticForm ((R * S) * trueCovariance E n * (R * S)ᵀ) b := hraw
    _ = 2 * ((R * Gamma * R) * (R * Gamma * R)).trace +
          4 * quadraticForm (R * Gamma * R) b := by rw [hcov]
    _ = 2 * (R * Gamma * R * Gamma).trace + 4 * quadraticForm Gamma b := by
      rw [source_trace_square_projectedCovariance R Gamma hR,
        source_quadraticForm_projectedCovariance R Gamma hsymmetric b hb]

/-- Exact finite expectation of the literal fitted-residual numerator.  The
only probabilistic substitution is the explicitly recorded AE structural
bridge above. -/
theorem fittedResidual_quadraticForm_integral
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (∫ ω, quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) ∂P) =
      (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        sourceProjectedMean E n ⬝ᵥ sourceProjectedMean E n := by
  calc
    (∫ ω, quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) ∂P) =
        ∫ ω, sourceResidualQuadraticCore E n ω ∂P :=
      MeasureTheory.integral_congr_ae
        (fittedResidual_quadraticForm_eq_sourceResidualQuadraticCore_ae E n hrank)
    _ = (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        sourceProjectedMean E n ⬝ᵥ sourceProjectedMean E n :=
      sourceResidualQuadraticCore_integral E covariance n hn hrank

/-- Exact finite variance of the literal fitted-residual numerator.  The
formula is the source's `2 tr(P Γ P Γ) + 4 bᵀ Γ b`, with neither independence
nor a replacement residual statistic assumed. -/
theorem fittedResidual_quadraticForm_variance
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    Var[(fun ω => quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω)); P] =
      2 * (sourceTailResidualProjection E n * sourceTransformedCovariance E n *
        sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        4 * quadraticForm (sourceTransformedCovariance E n) (sourceProjectedMean E n) := by
  calc
    Var[(fun ω => quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω)); P] =
        Var[sourceResidualQuadraticCore E n; P] :=
      ProbabilityTheory.variance_congr
        (fittedResidual_quadraticForm_eq_sourceResidualQuadraticCore_ae E n hrank)
    _ = 2 * (sourceTailResidualProjection E n * sourceTransformedCovariance E n *
        sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        4 * quadraticForm (sourceTransformedCovariance E n) (sourceProjectedMean E n) :=
      sourceResidualQuadraticCore_variance E covariance n hn hrank

/-- Exact finite expectation of the literal residual-scale statistic on the
positive-divisor tail. -/
theorem residualScale_integral
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    (∫ ω, residualScale E n ω ∂P) =
      ((sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        sourceProjectedMean E n ⬝ᵥ sourceProjectedMean E n) /
        ((E.maps.N n - E.q - 1 : Nat) : Real) := by
  calc
    (∫ ω, residualScale E n ω ∂P) =
        ∫ ω, quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) /
          ((E.maps.N n - E.q - 1 : Nat) : Real) ∂P := by
      congr 1
      funext ω
      exact residualScale_eq_literal_quotient E n ω hdivisor
    _ = (∫ ω, quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) ∂P) /
          ((E.maps.N n - E.q - 1 : Nat) : Real) :=
      MeasureTheory.integral_div ((E.maps.N n - E.q - 1 : Nat) : Real) _
    _ = ((sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        sourceProjectedMean E n ⬝ᵥ sourceProjectedMean E n) /
          ((E.maps.N n - E.q - 1 : Nat) : Real) := by
      rw [fittedResidual_quadraticForm_integral E covariance n hn hrank]

/-- Exact finite variance of the literal residual-scale statistic on the
positive-divisor tail. -/
theorem residualScale_variance
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    Var[residualScale E n; P] =
      (((((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) ^ 2) *
        (2 * (sourceTailResidualProjection E n * sourceTransformedCovariance E n *
          sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
          4 * quadraticForm (sourceTransformedCovariance E n)
            (sourceProjectedMean E n))) := by
  have hfun : residualScale E n = fun ω =>
      (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) *
        quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) := by
    funext ω
    calc
      residualScale E n ω = quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) /
          ((E.maps.N n - E.q - 1 : Nat) : Real) :=
        residualScale_eq_literal_quotient E n ω hdivisor
      _ = (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) *
          quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) := by
        rw [div_eq_mul_inv, mul_comm]
  rw [hfun, ProbabilityTheory.variance_const_mul,
    fittedResidual_quadraticForm_variance E covariance n hn hrank]

/-- The bounded-energy source assumption supplies one finite, nonnegative
constant valid at every resolution. -/
theorem fixedMean_exists_nonneg_energy_upperBound
    (E : FixedConditionalExperiment μ P) (mean : FixedMeanAssumption E) :
    ∃ C : Real, 0 ≤ C ∧ ∀ n : Nat, meanEnergy E mean.c n ≤ C := by
  rcases mean.bounded_energy with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro n
  exact (hC ⟨n, rfl⟩).trans (le_max_left _ _)

/-- The source projected mean energy is uniformly bounded by any constant
witnessing `FixedMeanAssumption.bounded_energy`. -/
theorem sourceProjectedMean_dotProduct_upper
    (E : FixedConditionalExperiment μ P) (mean : FixedMeanAssumption E)
    (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    {C : Real} (hC : meanEnergy E mean.c n ≤ C) :
    sourceProjectedMean E n ⬝ᵥ sourceProjectedMean E n ≤ C :=
  (source_tailProjected_mean_energy_le_meanEnergy E mean n hrank).trans hC

/-- Finite conditional variance bound for the literal residual-scale
statistic.  This is the paper's correlated quadratic-form bound before any
asymptotic notation is introduced. -/
theorem residualScale_variance_le
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) {C : Real}
    (hC : meanEnergy E mean.c n ≤ C) :
    Var[residualScale E n; P] ≤
      (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) ^ 2 *
        (2 * ((covariance.sigmaSquared / (1 - covariance.delta n)) ^ 2 *
          ((E.maps.N n - E.q - 1 : Nat) : Real)) +
          4 * ((covariance.sigmaSquared / (1 - covariance.delta n)) * C)) := by
  rcases covariance.sandwich n hn with ⟨hdelta_nonneg, hdelta_lt_one, _, _⟩
  have hscale_nonneg : 0 ≤ covariance.sigmaSquared / (1 - covariance.delta n) :=
    div_nonneg covariance.sigmaSquared_pos.le (by linarith)
  have htrace := sourceTransformedCovariance_square_trace_upper E covariance n hn hrank
    (Nat.le_of_lt hdivisor)
  have hmean := sourceProjectedMean_quadraticForm_upper E covariance mean n hn hrank
  have hmeanC : quadraticForm (sourceTransformedCovariance E n) (sourceProjectedMean E n) ≤
      (covariance.sigmaSquared / (1 - covariance.delta n)) * C :=
    hmean.trans (mul_le_mul_of_nonneg_left hC hscale_nonneg)
  have hinside :
      2 * (sourceTailResidualProjection E n * sourceTransformedCovariance E n *
        sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace +
        4 * quadraticForm (sourceTransformedCovariance E n) (sourceProjectedMean E n) ≤
      2 * ((covariance.sigmaSquared / (1 - covariance.delta n)) ^ 2 *
        ((E.maps.N n - E.q - 1 : Nat) : Real)) +
        4 * ((covariance.sigmaSquared / (1 - covariance.delta n)) * C) := by
    linarith
  rw [residualScale_variance E covariance n hn hrank hdivisor]
  exact mul_le_mul_of_nonneg_left hinside (sq_nonneg _)

/-- Finite expectation bounds for the literal residual scale.  These retain
the two sides of the transformed covariance sandwich and the exact residual
degrees-of-freedom denominator. -/
theorem residualScale_integral_bounds
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) {C : Real}
    (hC : meanEnergy E mean.c n ≤ C) :
    covariance.sigmaSquared / (1 + covariance.delta n) ≤
      (∫ ω, residualScale E n ω ∂P) ∧
    (∫ ω, residualScale E n ω ∂P) ≤
      covariance.sigmaSquared / (1 - covariance.delta n) +
        C / ((E.maps.N n - E.q - 1 : Nat) : Real) := by
  have hD : 0 < ((E.maps.N n - E.q - 1 : Nat) : Real) :=
    residual_divisor_pos E n hdivisor
  have htrace := sourceTransformedCovariance_projected_trace_bounds E covariance n hn hrank
    (Nat.le_of_lt hdivisor)
  have hmean_nonneg : 0 ≤ sourceProjectedMean E n ⬝ᵥ sourceProjectedMean E n := by
    simpa using dotProduct_star_self_nonneg (sourceProjectedMean E n)
  have hmeanC := sourceProjectedMean_dotProduct_upper E mean n hrank hC
  have hscale := residualScale_integral E covariance n hn hrank hdivisor
  constructor
  · rw [hscale]
    apply (le_div_iff₀ hD).2
    linarith [htrace.1]
  · rw [hscale]
    apply (div_le_iff₀ hD).2
    rw [add_mul]
    have hcancel :
        (C / ((E.maps.N n - E.q - 1 : Nat) : Real)) *
          ((E.maps.N n - E.q - 1 : Nat) : Real) = C := by
      field_simp
    rw [hcancel]
    linarith [htrace.2]

/-! ## Integrability of the literal residual scale

The finite Wick module deliberately keeps its square-sum integrability helper
private.  The following local copy is only the elementary finite-sum `L⁴` to
`L²` argument needed to apply the already-established literal moment formulas
to the source statistic.  It adds no distributional or independence premise.
-/

private theorem noncentralSquareSum_memLp_two_of_memLp_four
    {I Ω : Type*} [Fintype I] [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : I → Ω → Real}
    (b : I → Real) (hX : ∀ i, MemLp (X i) 4 P) :
    MemLp (InfillGLSLean.FiniteWickBridge.noncentralSquareSum X b) 2 P := by
  let squareSum : Ω → Real := fun ω => ∑ i, X i ω ^ 2
  let linearSum : Ω → Real := fun ω => ∑ i, b i * X i ω
  have hsquare : MemLp squareSum 2 P := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    have hpow := (hX i).norm_rpow_div (2 : ENNReal)
    have hfour_div_two : (4 : ENNReal) / 2 = 2 := by
      calc
        (4 : ENNReal) / 2 = (2 * 2) / 2 := by norm_num
        _ = 2 := ENNReal.mul_div_cancel_right (by norm_num) ENNReal.ofNat_ne_top
    rw [hfour_div_two] at hpow
    simpa [Real.norm_eq_abs, sq_abs] using hpow
  have hlinear : MemLp linearSum 2 P := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    exact ((hX i).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ (4 : ENNReal))).const_mul (b i)
  have hdecomposition :
      InfillGLSLean.FiniteWickBridge.noncentralSquareSum X b =
        fun ω => squareSum ω + 2 * linearSum ω + ∑ i, b i ^ 2 := by
    funext ω
    simp only [InfillGLSLean.FiniteWickBridge.noncentralSquareSum, squareSum, linearSum]
    simp_rw [add_pow_two]
    simp_rw [Finset.sum_add_distrib]
    have hlinear' : (∑ i, 2 * X i ω * b i) = 2 * (∑ i, b i * X i ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hlinear']
  rw [hdecomposition]
  convert hsquare.add ((hlinear.const_mul 2).add (memLp_const (∑ i, b i ^ 2))) using 1
  ext ω
  simp only [Pi.add_apply]
  ring

/-- The exact row-score noncentral quadratic core is square-integrable.  This
uses only the scalar L-034 Gaussian laws already aggregated by L-032. -/
private theorem sourceResidualQuadraticCore_memLp_two
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) : MemLp (sourceResidualQuadraticCore E n) 2 P := by
  unfold sourceResidualQuadraticCore
  apply noncentralSquareSum_memLp_two_of_memLp_four
  intro i
  exact
    InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore_memLp_four
      E covariance n
      ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i)

/-- On the full-rank tail, the literal fitted-residual numerator inherits the
square integrability of its AE-identical row-score quadratic core. -/
private theorem fittedResidual_quadraticForm_memLp_two
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    MemLp (fun ω => quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω)) 2 P := by
  apply (sourceResidualQuadraticCore_memLp_two E covariance n).ae_eq
  filter_upwards [fittedResidual_quadraticForm_eq_sourceResidualQuadraticCore_ae E n hrank]
    with ω hω
  exact hω.symm

/-- On the positive-divisor tail, the literal `residualScale` definition is
square-integrable.  The proof expands only its existing displayed branch. -/
private theorem residualScale_memLp_two_of_divisor
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    MemLp (residualScale E n) 2 P := by
  have hnum := fittedResidual_quadraticForm_memLp_two E covariance n hrank
  have hfun : residualScale E n = fun ω =>
      (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) *
        quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) := by
    funext ω
    calc
      residualScale E n ω = quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) /
          ((E.maps.N n - E.q - 1 : Nat) : Real) :=
        residualScale_eq_literal_quotient E n ω hdivisor
      _ = (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) *
          quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) := by
        rw [div_eq_mul_inv, mul_comm]
  rw [hfun]
  exact hnum.const_mul _

/-! ## Deterministic tail limits

These are the deterministic inputs to the paper's final Chebyshev step.  In
particular, the residual degrees-of-freedom denominator is not replaced by
`N_n`: its literal finite difference is shown to diverge. -/

private theorem residual_divisor_tendsto_atTop
    (E : FixedConditionalExperiment μ P) :
    Tendsto (fun n => ((E.maps.N n - E.q - 1 : Nat) : Real)) atTop atTop := by
  rw [tendsto_natCast_atTop_iff]
  apply tendsto_atTop.2
  intro B
  filter_upwards [E.maps.cell_count_tendsto.eventually
    (eventually_ge_atTop (B + E.q + 1))] with n hn
  omega

private theorem residual_divisor_inv_tendsto_zero
    (E : FixedConditionalExperiment μ P) :
    Tendsto (fun n => ((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹)
      atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (residual_divisor_tendsto_atTop E)

private theorem covariance_upper_scale_tendsto
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    Tendsto (fun n => covariance.sigmaSquared / (1 - covariance.delta n))
      atTop (nhds covariance.sigmaSquared) := by
  have hdenom : Tendsto (fun n => (1 : Real) - covariance.delta n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub covariance.delta_tendsto_zero)
  have hconst : Tendsto (fun _ : Nat => covariance.sigmaSquared)
      atTop (nhds covariance.sigmaSquared) := tendsto_const_nhds
  have hdiv := hconst.div hdenom one_ne_zero
  have hfun : ((fun _ : Nat => covariance.sigmaSquared) /
      fun n => (1 : Real) - covariance.delta n) =
        fun n => covariance.sigmaSquared / (1 - covariance.delta n) := by
    funext n
    simp only [Pi.div_apply]
  rw [hfun] at hdiv
  simpa using hdiv

private theorem covariance_lower_scale_tendsto
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    Tendsto (fun n => covariance.sigmaSquared / (1 + covariance.delta n))
      atTop (nhds covariance.sigmaSquared) := by
  have hdenom : Tendsto (fun n => (1 : Real) + covariance.delta n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add covariance.delta_tendsto_zero)
  have hconst : Tendsto (fun _ : Nat => covariance.sigmaSquared)
      atTop (nhds covariance.sigmaSquared) := tendsto_const_nhds
  have hdiv := hconst.div hdenom one_ne_zero
  have hfun : ((fun _ : Nat => covariance.sigmaSquared) /
      fun n => (1 : Real) + covariance.delta n) =
        fun n => covariance.sigmaSquared / (1 + covariance.delta n) := by
    funext n
    simp only [Pi.div_apply]
  rw [hfun] at hdiv
  simpa using hdiv

/-- Algebraic form of the paper's variance envelope after cancelling the
literal positive residual divisor.  This is only a rewrite of the finite
correlated-matrix bound above. -/
private theorem residualScale_variance_le_simplified
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) {C : Real}
    (hC : meanEnergy E mean.c n ≤ C) :
    Var[residualScale E n; P] ≤
      2 * (covariance.sigmaSquared / (1 - covariance.delta n)) ^ 2 *
          ((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹ +
        4 * (covariance.sigmaSquared / (1 - covariance.delta n)) * C *
          (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) ^ 2 := by
  let d : Real := ((E.maps.N n - E.q - 1 : Nat) : Real)
  let u : Real := covariance.sigmaSquared / (1 - covariance.delta n)
  have hd : 0 < d := by
    dsimp [d]
    exact residual_divisor_pos E n hdivisor
  have hraw := residualScale_variance_le E covariance mean n hn hrank hdivisor hC
  change Var[residualScale E n; P] ≤ d⁻¹ ^ 2 *
    (2 * (u ^ 2 * d) + 4 * (u * C)) at hraw
  calc
    Var[residualScale E n; P] ≤ d⁻¹ ^ 2 *
        (2 * (u ^ 2 * d) + 4 * (u * C)) := hraw
    _ = 2 * u ^ 2 * d⁻¹ + 4 * u * C * (d⁻¹) ^ 2 := by
      field_simp [hd.ne']

/-- The deterministic envelope from the finite residual-scale variance bound
vanishes: the covariance scale has a finite limit while the exact residual
degrees-of-freedom reciprocal tends to zero. -/
private theorem residualScale_variance_envelope_tendsto_zero
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (C : Real) :
    Tendsto (fun n =>
      2 * (covariance.sigmaSquared / (1 - covariance.delta n)) ^ 2 *
          ((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹ +
        4 * (covariance.sigmaSquared / (1 - covariance.delta n)) * C *
          (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) ^ 2)
      atTop (nhds 0) := by
  have hu := covariance_upper_scale_tendsto E covariance
  have hd := residual_divisor_inv_tendsto_zero E
  have htwo : Tendsto (fun _ : Nat => (2 : Real)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hfour : Tendsto (fun _ : Nat => (4 : Real)) atTop (nhds 4) :=
    tendsto_const_nhds
  have hC : Tendsto (fun _ : Nat => C) atTop (nhds C) :=
    tendsto_const_nhds
  have hfirst : Tendsto (fun n =>
      2 * (covariance.sigmaSquared / (1 - covariance.delta n)) ^ 2 *
        ((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) atTop (nhds 0) := by
    simpa using (htwo.mul (hu.pow 2)).mul hd
  have hsecond : Tendsto (fun n =>
      4 * (covariance.sigmaSquared / (1 - covariance.delta n)) * C *
        (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) ^ 2) atTop (nhds 0) := by
    simpa using ((hfour.mul hu).mul hC).mul (hd.pow 2)
  simpa using hfirst.add hsecond

/-- The trace term in the exact residual-scale expectation converges to the
source variance scale.  This applies the existing scalar covariance-sandwich
limit to the literal projected trace and literal residual divisor. -/
private theorem projected_trace_over_residual_divisor_tendsto
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    Tendsto (fun n =>
      (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace /
        ((E.maps.N n - E.q - 1 : Nat) : Real))
      atTop (nhds covariance.sigmaSquared) := by
  let traceOver : Nat → Real := fun n =>
    (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace /
      ((E.maps.N n - E.q - 1 : Nat) : Real)
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  have hstart : ∀ᶠ n in atTop, covariance.start ≤ n :=
    eventually_ge_atTop covariance.start
  have hfull : ∀ᶠ n in atTop,
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1 := by
    filter_upwards [eventually_ge_atTop nRank] with n hn
    exact hRank n hn
  have hdivisor : ∀ᶠ n in atTop, E.q + 1 < E.maps.N n :=
    InfillGLSLean.ManuscriptSpecification.L035.eventually_residual_divisor_positive E
  have hdelta_nonneg : ∀ᶠ n in atTop, 0 ≤ covariance.delta n := by
    filter_upwards [hstart] with n hn
    exact (covariance.sandwich n hn).1
  have hdelta_lt_one : ∀ᶠ n in atTop, covariance.delta n < 1 := by
    filter_upwards [hstart] with n hn
    exact (covariance.sandwich n hn).2.1
  have hsandwich : ∀ᶠ n in atTop,
      covariance.sigmaSquared / (1 + covariance.delta n) ≤ traceOver n ∧
        traceOver n ≤ covariance.sigmaSquared / (1 - covariance.delta n) := by
    filter_upwards [hstart, hfull, hdivisor] with n hn hfulln hdivn
    have hd : 0 < ((E.maps.N n - E.q - 1 : Nat) : Real) :=
      residual_divisor_pos E n hdivn
    have htrace := sourceTransformedCovariance_projected_trace_bounds E covariance n hn hfulln
      (Nat.le_of_lt hdivn)
    constructor
    · change covariance.sigmaSquared / (1 + covariance.delta n) ≤
        (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace /
          ((E.maps.N n - E.q - 1 : Nat) : Real)
      exact (le_div_iff₀ hd).2 htrace.1
    · change (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace /
        ((E.maps.N n - E.q - 1 : Nat) : Real) ≤
          covariance.sigmaSquared / (1 - covariance.delta n)
      exact (div_le_iff₀ hd).2 htrace.2
  have hnormalized : Tendsto (fun n => traceOver n / covariance.sigmaSquared)
      atTop (nhds 1) :=
    InfillGLSLean.normalizedVariance_tendsto_one_of_eventually_covariance_sandwich
      covariance.sigmaSquared_pos hdelta_nonneg hdelta_lt_one
      covariance.delta_tendsto_zero hsandwich
  have hscale : Tendsto (fun _ : Nat => covariance.sigmaSquared)
      atTop (nhds covariance.sigmaSquared) := tendsto_const_nhds
  have hproduct := hnormalized.mul hscale
  have hcancel : (fun n =>
      (traceOver n / covariance.sigmaSquared) * covariance.sigmaSquared) = traceOver := by
    funext n
    field_simp [covariance.sigmaSquared_pos.ne']
  rw [hcancel] at hproduct
  simpa only [traceOver, one_mul] using hproduct

/-- The projected fixed-mean contribution in the exact expectation formula
vanishes after division by the literal residual degrees of freedom. -/
private theorem projectedMean_energy_over_residual_divisor_tendsto_zero
    (E : FixedConditionalExperiment μ P) (mean : FixedMeanAssumption E)
    {C : Real} (hCnonneg : 0 ≤ C)
    (hC : ∀ n : Nat, meanEnergy E mean.c n ≤ C) :
    Tendsto (fun n =>
      dotProduct (sourceProjectedMean E n) (sourceProjectedMean E n) /
        ((E.maps.N n - E.q - 1 : Nat) : Real))
      atTop (nhds 0) := by
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  have hfull : ∀ᶠ n in atTop,
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1 := by
    filter_upwards [eventually_ge_atTop nRank] with n hn
    exact hRank n hn
  have hdivisor : ∀ᶠ n in atTop, E.q + 1 < E.maps.N n :=
    InfillGLSLean.ManuscriptSpecification.L035.eventually_residual_divisor_positive E
  have hnonneg : ∀ᶠ n in atTop, 0 ≤
      dotProduct (sourceProjectedMean E n) (sourceProjectedMean E n) /
        ((E.maps.N n - E.q - 1 : Nat) : Real) := by
    filter_upwards [hdivisor] with n hdivn
    exact div_nonneg
      (by simpa using dotProduct_star_self_nonneg (sourceProjectedMean E n))
      (le_of_lt (residual_divisor_pos E n hdivn))
  have hupper : ∀ᶠ n in atTop,
      dotProduct (sourceProjectedMean E n) (sourceProjectedMean E n) /
        ((E.maps.N n - E.q - 1 : Nat) : Real) ≤
          C * ((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹ := by
    filter_upwards [hfull, hdivisor] with n hfulln hdivn
    have hd : 0 < ((E.maps.N n - E.q - 1 : Nat) : Real) :=
      residual_divisor_pos E n hdivn
    have henergy := sourceProjectedMean_dotProduct_upper E mean n hfulln (hC n)
    have hdiv := div_le_div_of_nonneg_right henergy hd.le
    simpa only [div_eq_mul_inv] using hdiv
  have hd := residual_divisor_inv_tendsto_zero E
  have hCconst : Tendsto (fun _ : Nat => C) atTop (nhds C) :=
    tendsto_const_nhds
  have henvelope : Tendsto (fun n => C *
      ((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) atTop (nhds 0) := by
    simpa using hCconst.mul hd
  exact squeeze_zero' hnonneg hupper henvelope

/-- The exact conditional expectation of the literal residual scale converges
to `sigmaSquared`.  The proof combines the projected-trace sandwich with the
bounded fixed-mean remainder; it leaves the selected finite-prefix fallback
untouched. -/
private theorem residualScale_integral_tendsto
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    Tendsto (fun n => ∫ ω, residualScale E n ω ∂P)
      atTop (nhds covariance.sigmaSquared) := by
  rcases fixedMean_exists_nonneg_energy_upperBound E mean with ⟨C, hCnonneg, hC⟩
  have htrace := projected_trace_over_residual_divisor_tendsto E covariance
  have hmean := projectedMean_energy_over_residual_divisor_tendsto_zero E mean hCnonneg hC
  have hsum := htrace.add hmean
  have hsum' : Tendsto (fun n =>
      (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace /
        ((E.maps.N n - E.q - 1 : Nat) : Real) +
      dotProduct (sourceProjectedMean E n) (sourceProjectedMean E n) /
        ((E.maps.N n - E.q - 1 : Nat) : Real))
      atTop (nhds covariance.sigmaSquared) := by
    simpa using hsum
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  have hstart : ∀ᶠ n in atTop, covariance.start ≤ n :=
    eventually_ge_atTop covariance.start
  have hfull : ∀ᶠ n in atTop,
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1 := by
    filter_upwards [eventually_ge_atTop nRank] with n hn
    exact hRank n hn
  have hdivisor : ∀ᶠ n in atTop, E.q + 1 < E.maps.N n :=
    InfillGLSLean.ManuscriptSpecification.L035.eventually_residual_divisor_positive E
  apply hsum'.congr'
  filter_upwards [hstart, hfull, hdivisor] with n hn hfulln hdivn
  rw [← add_div]
  exact (residualScale_integral E covariance n hn hfulln hdivn).symm

/-- The exact finite variance formula and correlated trace bound imply that
the literal residual-scale variance tends to zero. -/
private theorem residualScale_variance_tendsto_zero
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    Tendsto (fun n => Var[residualScale E n; P]) atTop (nhds 0) := by
  rcases fixedMean_exists_nonneg_energy_upperBound E mean with ⟨C, hCnonneg, hC⟩
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  have hstart : ∀ᶠ n in atTop, covariance.start ≤ n :=
    eventually_ge_atTop covariance.start
  have hfull : ∀ᶠ n in atTop,
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1 := by
    filter_upwards [eventually_ge_atTop nRank] with n hn
    exact hRank n hn
  have hdivisor : ∀ᶠ n in atTop, E.q + 1 < E.maps.N n :=
    InfillGLSLean.ManuscriptSpecification.L035.eventually_residual_divisor_positive E
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ Var[residualScale E n; P] := by
    filter_upwards [] with n
    exact ProbabilityTheory.variance_nonneg _ _
  have hupper : ∀ᶠ n in atTop, Var[residualScale E n; P] ≤
      2 * (covariance.sigmaSquared / (1 - covariance.delta n)) ^ 2 *
          ((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹ +
        4 * (covariance.sigmaSquared / (1 - covariance.delta n)) * C *
          (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) ^ 2 := by
    filter_upwards [hstart, hfull, hdivisor] with n hn hfulln hdivn
    exact residualScale_variance_le_simplified E covariance mean n hn hfulln hdivn (hC n)
  exact squeeze_zero' hnonneg hupper
    (residualScale_variance_envelope_tendsto_zero E covariance C)

/- This narrow public boundary exports only the exact convergence consequence.
All supporting algebra and tail constructions remain task-local. -/
public section

/-- Exact convergence-in-probability endpoint for the source's literal
residual scale.  A finite-prefix constant patch is used only internally to
meet Mathlib's all-index `MemLp` interface; it is eventually equal to the
unchanged `residualScale` definition, including its source fallback. -/
theorem residualScale_tendstoInMeasure
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    TendstoInMeasure P (residualScale E) atTop
      (fun _ => covariance.sigmaSquared) := by
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  rcases eventually_atTop.1
    (InfillGLSLean.ManuscriptSpecification.L035.eventually_residual_divisor_positive E) with
    ⟨nDivisor, hDivisor⟩
  let N : Nat := max (max covariance.start nRank) nDivisor
  have hstartN : covariance.start ≤ N := by
    dsimp [N]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hfullN : nRank ≤ N := by
    dsimp [N]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hdivisorN : nDivisor ≤ N := by
    dsimp [N]
    exact le_max_right _ _
  let F : Nat → Ω → Real := fun n ω =>
    if N ≤ n then residualScale E n ω else covariance.sigmaSquared
  have hFmem : ∀ n, MemLp (F n) 2 P := by
    intro n
    by_cases hn : N ≤ n
    · have hstart : covariance.start ≤ n := hstartN.trans hn
      have hfull :
          (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1 :=
        hRank n (hfullN.trans hn)
      have hdivisor : E.q + 1 < E.maps.N n :=
        hDivisor n (hdivisorN.trans hn)
      simpa [F, hn] using residualScale_memLp_two_of_divisor E covariance n hfull hdivisor
    · have hFconst : F n = fun _ : Ω => covariance.sigmaSquared := by
        funext ω
        simp [F, hn]
      rw [hFconst]
      exact memLp_const _
  have hFintegral : Tendsto (fun n => ∫ ω, F n ω ∂P)
      atTop (nhds covariance.sigmaSquared) := by
    apply (residualScale_integral_tendsto E covariance mean).congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [F, hn]
  have hFvariance : Tendsto (fun n => Var[F n; P]) atTop (nhds 0) := by
    apply (residualScale_variance_tendsto_zero E covariance mean).congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [F, hn]
  have hconst : Tendsto (fun _ : Nat => covariance.sigmaSquared)
      atTop (nhds covariance.sigmaSquared) := tendsto_const_nhds
  have hFbias : Tendsto (fun n =>
      (∫ ω, F n ω ∂P - covariance.sigmaSquared) ^ 2) atTop (nhds 0) := by
    simpa using (hFintegral.sub hconst).pow 2
  have hFconverges : TendstoInMeasure P F atTop
      (fun _ => covariance.sigmaSquared) :=
    InfillGLSLean.residualScale_tendstoInMeasure_of_variance_and_bias_bounds
      (statistic := F)
      (varianceBound := fun n => Var[F n; P])
      (biasBound := fun n => (∫ ω, F n ω ∂P - covariance.sigmaSquared) ^ 2)
      covariance.sigmaSquared hFmem
      (by intro n; exact le_rfl)
      (by intro n; exact le_rfl)
      hFvariance hFbias
  apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hFconverges
  filter_upwards [eventually_ge_atTop N] with n hn
  filter_upwards [] with ω
  simp [F, hn]

/-- A scalar centered regional score with strictly positive Gaussian variance
does not equal any fixed real value almost everywhere.  This is only the
scalar L-034 law plus the non-atomic positive-variance Gaussian measure; it
does not introduce a finite-vector Gaussian law. -/
private theorem centeredRegionalScore_ne_ae_of_variance_pos
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (weight : Fin (E.maps.N n) → Real)
    (hvariance : 0 < quadraticForm (trueCovariance E n) weight) (c : Real) :
    ∀ᵐ ω ∂P,
      InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
        E n weight ω ≠ c := by
  let v : NNReal := (quadraticForm (trueCovariance E n) weight).toNNReal
  have hvpos : 0 < v := by
    dsimp [v]
    exact Real.toNNReal_pos.mpr hvariance
  have hv : v ≠ 0 := ne_of_gt hvpos
  letI : NullSingletonClass (gaussianReal 0 v) :=
    nullSingletonClass_gaussianReal hv
  have hlaw : HasLaw
      (InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
        E n weight)
      (gaussianReal 0 v) P := by
    dsimp [v]
    exact InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore_hasLaw
      E covariance n weight
  have hmeas : Measurable (fun x : Real => x ≠ c) :=
    (measurable_id'.eq_const c).not
  exact (hlaw.ae_iff (p := fun x : Real => x ≠ c) hmeas).2
    (Measure.ae_ne (gaussianReal 0 v) c)

/-- A noncentral finite sum of squares is strictly positive whenever one
coordinate avoids the unique cancelling value almost everywhere. -/
private theorem noncentralSquareSum_pos_ae_of_coordinate_ne
    {I : Type*} [Fintype I] (X : I → Ω → Real) (b : I → Real) (i : I)
    (h : ∀ᵐ ω ∂P, X i ω ≠ -b i) :
    ∀ᵐ ω ∂P, 0 < InfillGLSLean.FiniteWickBridge.noncentralSquareSum X b ω := by
  filter_upwards [h] with ω hω
  rw [InfillGLSLean.FiniteWickBridge.noncentralSquareSum]
  let v : I → Real := fun j => X j ω + b j
  have hvi : v i ≠ 0 := by
    intro hz
    apply hω
    dsimp [v] at hz
    linarith
  have hv : v ≠ 0 := by
    intro hz
    exact hvi (congrFun hz i)
  have hdot : 0 < v ⬝ᵥ v := by
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hv)
  rw [dotProduct] at hdot
  simpa only [v, pow_two] using hdot

/-- Full rank and a positive residual divisor leave a nonzero row in the
literal residual projection after the invertible CFC whitening factor. -/
private theorem sourceProjectedScoreRow_exists_nonzero
    (E : FixedConditionalExperiment μ P) (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    ∃ i,
      (sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i ≠ 0 := by
  let R : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    sourceTailResidualProjection E n
  let A : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
    CFC.sqrt (E.kernel n)
  let W : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real := R * A⁻¹
  have hdet : IsUnit A.det := by
    dsimp [A]
    exact cfcSqrt_det_isUnit (E.kernel n) (E.kernel_posDef n)
  have htrace : R.trace = ((E.maps.N n - E.q - 1 : Nat) : Real) := by
    dsimp [R]
    exact trace_sourceTailResidualProjection_eq_scale_divisor E n hrank
      (Nat.le_of_lt hdivisor)
  have htrace_ne : R.trace ≠ 0 := by
    rw [htrace]
    exact ne_of_gt (residual_divisor_pos E n hdivisor)
  have hmatrix : W ≠ 0 := by
    intro hzero
    have hRzero : R = 0 := by
      calc
        R = R * 1 := (Matrix.mul_one _).symm
        _ = R * (A⁻¹ * A) := by rw [Matrix.nonsing_inv_mul A hdet]
        _ = (R * A⁻¹) * A := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [show R * A⁻¹ = W by rfl, hzero]; simp
    apply htrace_ne
    rw [hRzero]
    simp
  have hrow : ∃ i, W i ≠ 0 := by
    by_contra hrows
    push Not at hrows
    apply hmatrix
    ext i j
    exact congrFun (hrows i) j
  simpa only [W, R, A] using hrow

/-- On the full-rank, positive-divisor branch, the exact noncentral
row-score representation of the source residual quadratic form is positive
almost everywhere.  Strict score variance comes from L-041's derivation of
positive definiteness of the literal true covariance under `ass:covariance`. -/
private theorem sourceResidualQuadraticCore_pos_ae
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    ∀ᵐ ω ∂P, 0 < sourceResidualQuadraticCore E n ω := by
  obtain ⟨i, hi⟩ := sourceProjectedScoreRow_exists_nonzero E n hrank hdivisor
  let weight : Fin (E.maps.N n) → Real :=
    (sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i
  have hweight : weight ≠ 0 := by
    simpa only [weight] using hi
  have hvariance : 0 < quadraticForm (trueCovariance E n) weight := by
    simpa only [quadraticForm_eq_dotProduct_mulVec, star_trivial] using
      (InfillGLSLean.ManuscriptSpecification.L041.trueCovariance_posDef
        E covariance n).dotProduct_mulVec_pos hweight
  have hscore := centeredRegionalScore_ne_ae_of_variance_pos E covariance n
    weight hvariance (-(sourceProjectedMean E n i))
  have hscore' : ∀ᵐ ω ∂P,
      InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
        E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) i) ω ≠
          -(sourceProjectedMean E n i) := by
    simpa only [weight] using hscore
  unfold sourceResidualQuadraticCore
  exact noncentralSquareSum_pos_ae_of_coordinate_ne
    (fun j =>
      InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge.centeredRegionalScore
        E n ((sourceTailResidualProjection E n * (CFC.sqrt (E.kernel n))⁻¹) j))
    (sourceProjectedMean E n) i hscore'

/-- Exact fixed-resolution formalization of the paper's prose after
`eq:scale`: on the existing covariance, full-rank, and positive-divisor
branch, the unchanged literal residual scale is strictly positive almost
everywhere. -/
theorem residualScale_pos_ae_of_covariance_full_rank_divisor
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    ∀ᵐ ω ∂P, 0 < residualScale E n ω := by
  have hcore := sourceResidualQuadraticCore_pos_ae E covariance n hrank hdivisor
  have hresidual := fittedResidual_quadraticForm_eq_sourceResidualQuadraticCore_ae
    E n hrank
  have hdenominator : 0 < ((E.maps.N n - E.q - 1 : Nat) : Real) :=
    residual_divisor_pos E n hdivisor
  filter_upwards [hresidual, hcore] with ω hresidualω hcoreω
  rw [residualScale_eq_literal_quotient E n ω hdivisor, hresidualω]
  exact div_pos hcoreω hdenominator

/-- Eventual form of the same source prose.  The static covariance assumption
supplies strict covariance at every resolution through L-041; full rank and
the literal residual divisor are the only eventual facts used here. -/
theorem eventually_ae_residualScale_pos
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∀ᶠ n in atTop, ∀ᵐ ω ∂P, 0 < residualScale E n ω := by
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  have hdivisor : ∀ᶠ n in atTop, E.q + 1 < E.maps.N n :=
    InfillGLSLean.ManuscriptSpecification.L035.eventually_residual_divisor_positive E
  filter_upwards [eventually_ge_atTop nRank, hdivisor] with n hnRank hnDivisor
  exact residualScale_pos_ae_of_covariance_full_rank_divisor E covariance n
    (hRank n hnRank) hnDivisor

/-! ## Public finite rate interface

The preceding public endpoints deliberately exposed only the consistency and
positivity consequences of Appendix `lem:scale`.  The displayed rate in that
same source lemma needs the exact finite trace/mean decomposition and variance
envelope below.  These declarations only re-export calculations already proved
above.  They retain the literal `residualScale`, residual divisor, covariance
assumption, and fixed-mean assumption; they do not revise a manuscript target
or introduce an additional premise.

The two named deterministic summands are kept opaque to downstream modules.
Their public equations and bounds are the source-faithful interface required to
formalize the standard meaning of the paper's `O(delta_n)+O_p(N_n^{-1/2})`
display in a separate rate lane.
-/

/-- The covariance-trace summand in the exact finite expectation of the
literal residual-scale statistic.  This is the first term in the Appendix
`lem:scale` expectation calculation, divided by its unchanged residual
degrees-of-freedom denominator. -/
noncomputable def residualScaleTraceTerm
    (E : FixedConditionalExperiment μ P) (n : Nat) : Real :=
  (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace /
    ((E.maps.N n - E.q - 1 : Nat) : Real)

/-- The projected-mean summand in the exact finite expectation of the literal
residual-scale statistic, with the same unchanged denominator. -/
noncomputable def residualScaleMeanTerm
    (E : FixedConditionalExperiment μ P) (n : Nat) : Real :=
  dotProduct (sourceProjectedMean E n) (sourceProjectedMean E n) /
    ((E.maps.N n - E.q - 1 : Nat) : Real)

/-- Exact finite expectation decomposition of the literal residual scale into
the covariance-trace and projected-mean summands. -/
theorem residualScale_integral_eq_traceTerm_add_meanTerm
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    (∫ ω, residualScale E n ω ∂P) =
      residualScaleTraceTerm E n + residualScaleMeanTerm E n := by
  rw [residualScale_integral E covariance n hn hrank hdivisor]
  simp only [residualScaleTraceTerm, residualScaleMeanTerm, add_div]

/-- The covariance sandwich bounds the literal trace summand itself, before
the projected mean is added.  This is the deterministic `O(delta_n)` source
of the paper's displayed residual-scale rate. -/
theorem residualScaleTraceTerm_bounds
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    covariance.sigmaSquared / (1 + covariance.delta n) ≤ residualScaleTraceTerm E n ∧
      residualScaleTraceTerm E n ≤ covariance.sigmaSquared / (1 - covariance.delta n) := by
  have hdenominator : 0 < ((E.maps.N n - E.q - 1 : Nat) : Real) :=
    residual_divisor_pos E n hdivisor
  have htrace := sourceTransformedCovariance_projected_trace_bounds E covariance n hn hrank
    (Nat.le_of_lt hdivisor)
  constructor
  · change covariance.sigmaSquared / (1 + covariance.delta n) ≤
      (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace /
        ((E.maps.N n - E.q - 1 : Nat) : Real)
    exact (le_div_iff₀ hdenominator).2 htrace.1
  · change (sourceTailResidualProjection E n * sourceTransformedCovariance E n).trace /
      ((E.maps.N n - E.q - 1 : Nat) : Real) ≤
        covariance.sigmaSquared / (1 - covariance.delta n)
    exact (div_le_iff₀ hdenominator).2 htrace.2

/-- The projected-mean summand is nonnegative on the literal positive-divisor
branch. -/
theorem residualScaleMeanTerm_nonneg
    (E : FixedConditionalExperiment μ P) (n : Nat)
    (hdivisor : E.q + 1 < E.maps.N n) :
    0 ≤ residualScaleMeanTerm E n := by
  unfold residualScaleMeanTerm
  exact div_nonneg
    (by simpa using dotProduct_star_self_nonneg (sourceProjectedMean E n))
    (le_of_lt (residual_divisor_pos E n hdivisor))

/-- A fixed-mean energy envelope bounds the exact projected-mean summand by
the reciprocal of the unchanged residual divisor. -/
theorem residualScaleMeanTerm_le
    (E : FixedConditionalExperiment μ P) (mean : FixedMeanAssumption E)
    (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) {C : Real}
    (hC : meanEnergy E mean.c n ≤ C) :
    residualScaleMeanTerm E n ≤ C /
      ((E.maps.N n - E.q - 1 : Nat) : Real) := by
  unfold residualScaleMeanTerm
  exact div_le_div_of_nonneg_right
    (sourceProjectedMean_dotProduct_upper E mean n hrank hC)
    (le_of_lt (residual_divisor_pos E n hdivisor))

/-- The already-proved finite correlated variance envelope for the literal
residual-scale statistic.  Its right side is exactly the simplified form of
the Appendix `lem:scale` quadratic-form bound. -/
theorem residualScale_variance_le_rate_envelope
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) (n : Nat) (hn : covariance.start ≤ n)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) {C : Real}
    (hC : meanEnergy E mean.c n ≤ C) :
    Var[residualScale E n; P] ≤
      2 * (covariance.sigmaSquared / (1 - covariance.delta n)) ^ 2 *
          ((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹ +
        4 * (covariance.sigmaSquared / (1 - covariance.delta n)) * C *
          (((E.maps.N n - E.q - 1 : Nat) : Real)⁻¹) ^ 2 :=
  residualScale_variance_le_simplified E covariance mean n hn hrank hdivisor hC

/-- Square integrability of the unchanged literal residual scale on the
full-rank positive-divisor branch, re-exported for Chebyshev's finite rate
argument. -/
theorem residualScale_memLp_two_on_tail
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : Nat)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hdivisor : E.q + 1 < E.maps.N n) :
    MemLp (residualScale E n) 2 P :=
  residualScale_memLp_two_of_divisor E covariance n hrank hdivisor

end

end InfillGLSLean.ManuscriptSpecification.L046
