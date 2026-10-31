module

public import ManuscriptSpecification
import «L-034-normality-exact-integration».Explore
public import InfillGLSLean.FiniteConditionalError
public import «L-032-finite-wick-bridge».WickBridge
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

namespace InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory MatrixOrder

variable {D : CompactEuclideanDomain}
variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure (Point D)} [IsProbabilityMeasure mu]
variable {P : Measure Omega} [IsProbabilityMeasure P]

/-- The source covariance sandwich implies positivity of the literal regional
covariance on its stated tail.  This is a derived fact, not an added premise. -/
theorem trueCovariance_posSemidef_of_sandwich
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n) :
    (trueCovariance E n).PosSemidef := by
  rcases covariance.sandwich n hn with ⟨hdelta_nonneg, _, hlower, _⟩
  have hdenom_pos : 0 < 1 + covariance.delta n := by linarith
  have hscale_nonneg : 0 ≤ covariance.sigmaSquared / (1 + covariance.delta n) :=
    le_of_lt (div_pos covariance.sigmaSquared_pos hdenom_pos)
  have hworking :
      ((covariance.sigmaSquared / (1 + covariance.delta n)) • E.kernel n).PosSemidef :=
    (E.kernel_posDef n).posSemidef.smul hscale_nonneg
  have hsum := hlower.add hworking
  convert hsum using 1 <;> noncomm_ring

/-- The inverse principal square root of a real positive-definite matrix is
symmetric.  This is the orientation bridge required before treating the
whitened covariance as `S * Σ * Sᵀ`. -/
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

/-- The paper's transformed covariance `Γ_n`, in the literal `S * Σ * Sᵀ`
orientation. -/
noncomputable def sourceTransformedCovariance
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real :=
  (CFC.sqrt (E.kernel n))⁻¹ * trueCovariance E n * ((CFC.sqrt (E.kernel n))⁻¹)ᵀ

/-- Exact covariance sandwich for `Γ_n`.  The proof first identifies the
real symmetry `Sᵀ = S`, so it does not silently exchange `SᵀΣS` and
`SΣSᵀ`. -/
theorem sourceTransformedCovariance_sandwich
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
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

/-! ## Public scalar regional-score interface

These are exact consequences of the paper's Gaussian-field assumption and
the L-032 scalar Wick identities.  They do not assert a finite-vector
Gaussian law or any residual-scale conclusion. -/

public section

/-- The centered finite error vector used in the literal Gaussian-score
bridge.  This abbreviation only names the existing source expression. -/
@[expose]
noncomputable def centeredRegionalError
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    Fin (E.maps.N n) → Omega → Real :=
  centeredFiniteError (regionalRandomValues mu E.maps E.error n)
    (regionalConditionalMean E.maps P E.error n)

/-- A deterministic score of the centered regional error vector. -/
@[expose]
noncomputable def centeredRegionalScore
    (E : FixedConditionalExperiment mu P) (n : Nat)
    (weight : Fin (E.maps.N n) → Real) : Omega → Real :=
  finiteWeightedScore weight (centeredRegionalError E n)

/-- Public pointwise expansion of the literal centered regional score.  This
is an API-only `rfl` bridge; it changes neither the score nor its Gaussian
law. -/
@[simp]
theorem centeredRegionalScore_apply
    (E : FixedConditionalExperiment mu P) (n : Nat)
    (weight : Fin (E.maps.N n) → Real) (ω : Omega) :
    centeredRegionalScore E n weight ω =
      finiteWeightedScore weight
        (centeredFiniteError (regionalRandomValues mu E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n)) ω := rfl

theorem centeredRegionalScore_hasLaw
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (weight : Fin (E.maps.N n) → Real) :
    HasLaw (centeredRegionalScore E n weight)
      (gaussianReal 0 (quadraticForm (trueCovariance E n) weight).toNNReal) P := by
  simpa only [centeredRegionalScore, centeredRegionalError] using
    InfillGLSLean.ManuscriptSpecification.L034.centered_regional_score_hasLaw
      E covariance n weight

theorem centeredRegionalScore_memLp_four
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (weight : Fin (E.maps.N n) → Real) :
    MemLp (centeredRegionalScore E n weight) 4 P := by
  exact (centeredRegionalScore_hasLaw E covariance n weight).memLp
    (memLp_id_gaussianReal' 4 (by norm_num))

theorem centeredRegionalScore_integral_zero
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (weight : Fin (E.maps.N n) → Real) :
    (∫ ω, centeredRegionalScore E n weight ω ∂P) = 0 := by
  calc
    (∫ ω, centeredRegionalScore E n weight ω ∂P) =
        ∫ x, x ∂gaussianReal 0 (quadraticForm (trueCovariance E n) weight).toNNReal :=
      (centeredRegionalScore_hasLaw E covariance n weight).integral_eq
    _ = 0 := by simp

theorem centeredRegionalScore_variance
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n) (weight : Fin (E.maps.N n) → Real) :
    Var[centeredRegionalScore E n weight; P] = quadraticForm (trueCovariance E n) weight := by
  calc
    Var[centeredRegionalScore E n weight; P] =
        Var[id; gaussianReal 0 (quadraticForm (trueCovariance E n) weight).toNNReal] :=
      (centeredRegionalScore_hasLaw E covariance n weight).variance_eq
    _ = ((quadraticForm (trueCovariance E n) weight).toNNReal : Real) := by simp
    _ = quadraticForm (trueCovariance E n) weight :=
      InfillGLSLean.finiteGaussianScore_varianceParameter_coe
        (trueCovariance_posSemidef_of_sandwich E covariance n hn)

end

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

theorem quadraticForm_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι Real) (v : ι → Real) :
    quadraticForm C (-v) = quadraticForm C v := by
  simp [quadraticForm_eq_dotProduct_mulVec, dotProduct, Matrix.mulVec]

theorem scoreBilinear_neg_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι Real) (u v : ι → Real) :
    InfillGLSLean.FiniteWickBridge.scoreBilinear C u (-v) =
      -InfillGLSLean.FiniteWickBridge.scoreBilinear C u v := by
  unfold InfillGLSLean.FiniteWickBridge.scoreBilinear
  rw [Matrix.mulVec_neg, dotProduct_neg]

theorem quadraticForm_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι Real} (hC : C.IsHermitian) (u v : ι → Real) :
    quadraticForm C (u - v) =
      quadraticForm C u + quadraticForm C v -
        2 * InfillGLSLean.FiniteWickBridge.scoreBilinear C u v := by
  rw [sub_eq_add_neg, InfillGLSLean.FiniteWickBridge.quadraticForm_add hC u (-v),
    quadraticForm_neg, scoreBilinear_neg_right]
  ring

/-- The covariance bilinear form of two row weights is the corresponding
entry of the literal matrix product `W * Σ * Wᵀ`. -/
theorem scoreBilinear_rows_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W Sigma : Matrix ι ι Real) (i j : ι) :
    InfillGLSLean.FiniteWickBridge.scoreBilinear Sigma (W i) (W j) =
      (W * Sigma * Wᵀ) i j := by
  unfold InfillGLSLean.FiniteWickBridge.scoreBilinear
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply]
  calc
    (∑ a, W i a * ∑ b, Sigma a b * W j b) =
        ∑ a, ∑ b, W i a * (Sigma a b * W j b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
    _ = ∑ b, ∑ a, W i a * (Sigma a b * W j b) := Finset.sum_comm
    _ = ∑ b, (∑ a, W i a * Sigma a b) * W j b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          ring

public section

theorem centeredRegionalScore_second_integral
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (u v : Fin (E.maps.N n) → Real) :
    (∫ ω, centeredRegionalScore E n u ω * centeredRegionalScore E n v ω ∂P) =
      InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) u v := by
  let X := centeredRegionalScore E n u
  let Y := centeredRegionalScore E n v
  have hX2 : MemLp X 2 P := by
    simpa only [X] using (centeredRegionalScore_memLp_four E covariance n u).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ 4)
  have hY2 : MemLp Y 2 P := by
    simpa only [Y] using (centeredRegionalScore_memLp_four E covariance n v).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ 4)
  have hvarX : Var[X; P] = quadraticForm (trueCovariance E n) u := by
    simpa only [X] using centeredRegionalScore_variance E covariance n hn u
  have hvarY : Var[Y; P] = quadraticForm (trueCovariance E n) v := by
    simpa only [Y] using centeredRegionalScore_variance E covariance n hn v
  have hvarPlus : Var[X + Y; P] = quadraticForm (trueCovariance E n) (u + v) := by
    change Var[(fun ω => X ω + Y ω); P] = quadraticForm (trueCovariance E n) (u + v)
    rw [← show centeredRegionalScore E n (u + v) = fun ω => X ω + Y ω by
      simpa only [X, Y, centeredRegionalScore, centeredRegionalError] using
        finiteWeightedScore_add u v (centeredRegionalError E n)]
    exact centeredRegionalScore_variance E covariance n hn (u + v)
  have hprojection := variance_add hX2 hY2
  have hquadratic := InfillGLSLean.FiniteWickBridge.quadraticForm_add
    (trueCovariance_posSemidef_of_sandwich E covariance n hn).isHermitian u v
  have hcov : cov[X, Y; P] =
      InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) u v := by
    rw [hvarX, hvarY, hvarPlus, hquadratic] at hprojection
    linarith
  have hmeanX : (∫ ω, X ω ∂P) = 0 := by
    simpa only [X] using centeredRegionalScore_integral_zero E covariance n u
  have hmeanY : (∫ ω, Y ω ∂P) = 0 := by
    simpa only [Y] using centeredRegionalScore_integral_zero E covariance n v
  have hproduct : cov[X, Y; P] = ∫ ω, X ω * Y ω ∂P := by
    rw [covariance_eq_sub hX2 hY2, hmeanX, hmeanY]
    simp
  simpa only [X, Y] using hproduct.symm.trans hcov

theorem centeredRegionalScore_third_integral_zero
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (u v : Fin (E.maps.N n) → Real) :
    (∫ ω, centeredRegionalScore E n u ω ^ 2 * centeredRegionalScore E n v ω ∂P) = 0 := by
  have hU := centeredRegionalScore_hasLaw E covariance n u
  have hV := centeredRegionalScore_hasLaw E covariance n v
  have hPlus0 := centeredRegionalScore_hasLaw E covariance n (u + v)
  have hMinus0 := centeredRegionalScore_hasLaw E covariance n (u - v)
  have hPlus : HasLaw
      (fun ω => centeredRegionalScore E n u ω + centeredRegionalScore E n v ω)
      (gaussianReal 0 (quadraticForm (trueCovariance E n) (u + v)).toNNReal) P := by
    rw [← show centeredRegionalScore E n (u + v) =
        fun ω => centeredRegionalScore E n u ω + centeredRegionalScore E n v ω by
      simpa only [centeredRegionalScore, centeredRegionalError] using
        finiteWeightedScore_add u v (centeredRegionalError E n)]
    exact hPlus0
  have hMinus : HasLaw
      (fun ω => centeredRegionalScore E n u ω - centeredRegionalScore E n v ω)
      (gaussianReal 0 (quadraticForm (trueCovariance E n) (u - v)).toNNReal) P := by
    rw [← show centeredRegionalScore E n (u - v) =
        fun ω => centeredRegionalScore E n u ω - centeredRegionalScore E n v ω by
      simpa only [centeredRegionalScore, centeredRegionalError] using
        finiteWeightedScore_sub u v (centeredRegionalError E n)]
    exact hMinus0
  exact InfillGLSLean.FiniteWickBridge.centered_gaussian_square_mul_integral_zero
    hPlus hMinus hV

theorem centeredRegionalScore_fourth_integral
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (u v : Fin (E.maps.N n) → Real) :
    (∫ ω, centeredRegionalScore E n u ω ^ 2 * centeredRegionalScore E n v ω ^ 2 ∂P) =
      InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) u u *
        InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) v v +
          2 * InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) u v ^ 2 := by
  have hU := centeredRegionalScore_hasLaw E covariance n u
  have hV := centeredRegionalScore_hasLaw E covariance n v
  have hPlus0 := centeredRegionalScore_hasLaw E covariance n (u + v)
  have hMinus0 := centeredRegionalScore_hasLaw E covariance n (u - v)
  have hPlus : HasLaw
      (fun ω => centeredRegionalScore E n u ω + centeredRegionalScore E n v ω)
      (gaussianReal 0 (quadraticForm (trueCovariance E n) (u + v)).toNNReal) P := by
    rw [← show centeredRegionalScore E n (u + v) =
        fun ω => centeredRegionalScore E n u ω + centeredRegionalScore E n v ω by
      simpa only [centeredRegionalScore, centeredRegionalError] using
        finiteWeightedScore_add u v (centeredRegionalError E n)]
    exact hPlus0
  have hMinus : HasLaw
      (fun ω => centeredRegionalScore E n u ω - centeredRegionalScore E n v ω)
      (gaussianReal 0 (quadraticForm (trueCovariance E n) (u - v)).toNNReal) P := by
    rw [← show centeredRegionalScore E n (u - v) =
        fun ω => centeredRegionalScore E n u ω - centeredRegionalScore E n v ω by
      simpa only [centeredRegionalScore, centeredRegionalError] using
        finiteWeightedScore_sub u v (centeredRegionalError E n)]
    exact hMinus0
  let C := trueCovariance E n
  have hC : C.PosSemidef := trueCovariance_posSemidef_of_sandwich E covariance n hn
  have hplusVar : ((quadraticForm C (u + v)).toNNReal : Real) =
      ((quadraticForm C u).toNNReal : Real) +
        ((quadraticForm C v).toNNReal : Real) +
          2 * InfillGLSLean.FiniteWickBridge.scoreBilinear C u v := by
    simpa only [InfillGLSLean.finiteGaussianScore_varianceParameter_coe hC] using
      InfillGLSLean.FiniteWickBridge.quadraticForm_add hC.isHermitian u v
  have hminusVar : ((quadraticForm C (u - v)).toNNReal : Real) =
      ((quadraticForm C u).toNNReal : Real) +
        ((quadraticForm C v).toNNReal : Real) -
          2 * InfillGLSLean.FiniteWickBridge.scoreBilinear C u v := by
    simpa only [InfillGLSLean.finiteGaussianScore_varianceParameter_coe hC] using
      quadraticForm_sub hC.isHermitian u v
  have hwick := InfillGLSLean.FiniteWickBridge.centered_gaussian_pair_wick_fourth
    hU hV hPlus hMinus hplusVar hminusVar
  have hUvar : ((quadraticForm C u).toNNReal : Real) =
      InfillGLSLean.FiniteWickBridge.scoreBilinear C u u := by
    rw [InfillGLSLean.finiteGaussianScore_varianceParameter_coe hC]
    rfl
  have hVvar : ((quadraticForm C v).toNNReal : Real) =
      InfillGLSLean.FiniteWickBridge.scoreBilinear C v v := by
    rw [InfillGLSLean.finiteGaussianScore_varianceParameter_coe hC]
    rfl
  rw [hUvar, hVvar] at hwick
  simpa only [C] using hwick

/-- Congruence preserves positive semidefiniteness in the exact orientation
used by the transformed row-score covariance. -/
theorem rowScoreCovariance_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W Sigma : Matrix ι ι Real) (hSigma : Sigma.PosSemidef) :
    (W * Sigma * Wᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hSigma.mul_mul_conjTranspose_same W

theorem rowScore_noncentralSquareSum_integral
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (W : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real)
    (b : Fin (E.maps.N n) → Real) :
    (∫ ω, InfillGLSLean.FiniteWickBridge.noncentralSquareSum
      (fun i => centeredRegionalScore E n (W i)) b ω ∂P) =
        (W * trueCovariance E n * Wᵀ).trace + b ⬝ᵥ b := by
  apply InfillGLSLean.FiniteWickBridge.noncentralSquareSum_integral_trace
    (C := W * trueCovariance E n * Wᵀ) b
  · intro i
    exact centeredRegionalScore_memLp_four E covariance n (W i)
  · intro i
    exact centeredRegionalScore_integral_zero E covariance n (W i)
  · intro i j
    calc
      (∫ ω, centeredRegionalScore E n (W i) ω *
          centeredRegionalScore E n (W j) ω ∂P) =
          InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) (W i) (W j) :=
        centeredRegionalScore_second_integral E covariance n hn (W i) (W j)
      _ = (W * trueCovariance E n * Wᵀ) i j :=
        scoreBilinear_rows_eq_mul W (trueCovariance E n) i j

theorem rowScore_noncentralSquareSum_variance
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (W : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real)
    (b : Fin (E.maps.N n) → Real) :
    Var[InfillGLSLean.FiniteWickBridge.noncentralSquareSum
      (fun i => centeredRegionalScore E n (W i)) b; P] =
      2 * ((W * trueCovariance E n * Wᵀ) *
        (W * trueCovariance E n * Wᵀ)).trace +
          4 * quadraticForm (W * trueCovariance E n * Wᵀ) b := by
  apply InfillGLSLean.FiniteWickBridge.noncentralSquareSum_variance_trace
    (C := W * trueCovariance E n * Wᵀ) b
  · exact (rowScoreCovariance_posSemidef W (trueCovariance E n)
      (trueCovariance_posSemidef_of_sandwich E covariance n hn)).isHermitian
  · intro i
    exact centeredRegionalScore_memLp_four E covariance n (W i)
  · intro i
    exact centeredRegionalScore_integral_zero E covariance n (W i)
  · intro i j
    calc
      (∫ ω, centeredRegionalScore E n (W i) ω *
          centeredRegionalScore E n (W j) ω ∂P) =
          InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) (W i) (W j) :=
        centeredRegionalScore_second_integral E covariance n hn (W i) (W j)
      _ = (W * trueCovariance E n * Wᵀ) i j :=
        scoreBilinear_rows_eq_mul W (trueCovariance E n) i j
  · intro i j
    exact centeredRegionalScore_third_integral_zero E covariance n (W i) (W j)
  · intro i j
    calc
      (∫ ω, centeredRegionalScore E n (W i) ω ^ 2 *
          centeredRegionalScore E n (W j) ω ^ 2 ∂P) =
          InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) (W i) (W i) *
            InfillGLSLean.FiniteWickBridge.scoreBilinear (trueCovariance E n) (W j) (W j) +
              2 * InfillGLSLean.FiniteWickBridge.scoreBilinear
                (trueCovariance E n) (W i) (W j) ^ 2 :=
        centeredRegionalScore_fourth_integral E covariance n hn (W i) (W j)
      _ = (W * trueCovariance E n * Wᵀ) i i *
          (W * trueCovariance E n * Wᵀ) j j +
            2 * (W * trueCovariance E n * Wᵀ) i j ^ 2 := by
        rw [scoreBilinear_rows_eq_mul W (trueCovariance E n) i i,
          scoreBilinear_rows_eq_mul W (trueCovariance E n) j j,
          scoreBilinear_rows_eq_mul W (trueCovariance E n) i j]

end

/-- Row-score covariance after a symmetric projection, with the transpose
orientation retained explicitly. -/
theorem projected_rowScoreCovariance_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P S Sigma : Matrix ι ι Real) (hP : Pᵀ = P) :
    (P * S) * Sigma * (P * S)ᵀ = P * (S * Sigma * Sᵀ) * P := by
  rw [Matrix.transpose_mul, hP]
  simp only [Matrix.mul_assoc]

theorem trace_projectedCovariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Gamma : Matrix ι ι Real) (hP : P * P = P) :
    (P * Gamma * P).trace = (P * Gamma).trace := by
  calc
    (P * Gamma * P).trace = ((P * Gamma) * P).trace := rfl
    _ = (P * (P * Gamma)).trace := Matrix.trace_mul_comm _ _
    _ = ((P * P) * Gamma).trace := by rw [Matrix.mul_assoc]
    _ = (P * Gamma).trace := by rw [hP]

theorem trace_square_projectedCovariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Gamma : Matrix ι ι Real) (hP : P * P = P) :
    ((P * Gamma * P) * (P * Gamma * P)).trace = (P * Gamma * P * Gamma).trace := by
  have hs : (P * Gamma * P) * (P * Gamma * P) = P * (Gamma * (P * (Gamma * P))) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hP]
  rw [hs]
  calc
    (P * (Gamma * (P * (Gamma * P)))).trace =
        ((P * (Gamma * (P * Gamma))) * P).trace := by simp only [Matrix.mul_assoc]
    _ = (P * (P * (Gamma * (P * Gamma)))).trace := Matrix.trace_mul_comm _ _
    _ = ((P * P) * (Gamma * (P * Gamma))).trace := by rw [Matrix.mul_assoc]
    _ = (P * (Gamma * (P * Gamma))).trace := by rw [hP]
    _ = (P * Gamma * P * Gamma).trace := by simp only [Matrix.mul_assoc]

theorem quadraticForm_projectedCovariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Gamma : Matrix ι ι Real) (hP : P.IsSymm) (b : ι → Real)
    (hb : P *ᵥ b = b) :
    quadraticForm (P * Gamma * P) b = quadraticForm Gamma b := by
  rw [quadraticForm_eq_dotProduct_mulVec, quadraticForm_eq_dotProduct_mulVec]
  calc
    b ⬝ᵥ (P * Gamma * P) *ᵥ b = b ⬝ᵥ P *ᵥ (Gamma *ᵥ (P *ᵥ b)) := by
      congr 1
      rw [← Matrix.mulVec_mulVec b (P * Gamma) P,
        ← Matrix.mulVec_mulVec (P *ᵥ b) P Gamma]
    _ = b ⬝ᵥ P *ᵥ (Gamma *ᵥ b) := by rw [hb]
    _ = (Gamma *ᵥ b) ⬝ᵥ (P *ᵥ b) := hP.dotProduct_mulVec_comm
    _ = (P *ᵥ b) ⬝ᵥ (Gamma *ᵥ b) := dotProduct_comm _ _
    _ = b ⬝ᵥ (Gamma *ᵥ b) := by rw [hb]

/-- The exact finite centered-error quadratic statistic after an arbitrary
deterministic projection and whitening map. -/
noncomputable def projectedCenteredQuadratic
    (E : FixedConditionalExperiment mu P) (n : Nat)
    (projection whitening : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real)
    (mean : Fin (E.maps.N n) → Real) : Omega → Real :=
  InfillGLSLean.FiniteWickBridge.noncentralSquareSum
    (fun i => centeredRegionalScore E n ((projection * whitening) i))
    (projection *ᵥ (whitening *ᵥ mean))

theorem projection_mulVec_projectedMean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (projection whitening : Matrix ι ι Real) (mean : ι → Real)
    (hidempotent : projection * projection = projection) :
    projection *ᵥ (projection *ᵥ (whitening *ᵥ mean)) =
      projection *ᵥ (whitening *ᵥ mean) := by
  calc
    projection *ᵥ (projection *ᵥ (whitening *ᵥ mean)) =
        (projection * projection) *ᵥ (whitening *ᵥ mean) := by
          rw [Matrix.mulVec_mulVec]
    _ = projection *ᵥ (whitening *ᵥ mean) := by rw [hidempotent]

theorem projectedCenteredQuadratic_integral
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (projection whitening : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real)
    (mean : Fin (E.maps.N n) → Real)
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection) :
    (∫ ω, projectedCenteredQuadratic E n projection whitening mean ω ∂P) =
      (projection * (whitening * trueCovariance E n * whiteningᵀ)).trace +
        (projection *ᵥ (whitening *ᵥ mean)) ⬝ᵥ
          (projection *ᵥ (whitening *ᵥ mean)) := by
  let b : Fin (E.maps.N n) → Real := projection *ᵥ (whitening *ᵥ mean)
  have hraw := rowScore_noncentralSquareSum_integral E covariance n hn
    (projection * whitening) b
  have hcov := projected_rowScoreCovariance_eq projection whitening
    (trueCovariance E n) hsymmetric
  change (∫ ω, InfillGLSLean.FiniteWickBridge.noncentralSquareSum
    (fun i => centeredRegionalScore E n ((projection * whitening) i)) b ω ∂P) = _
  calc
    (∫ ω, InfillGLSLean.FiniteWickBridge.noncentralSquareSum
        (fun i => centeredRegionalScore E n ((projection * whitening) i)) b ω ∂P) =
        ((projection * whitening) * trueCovariance E n *
          (projection * whitening)ᵀ).trace + b ⬝ᵥ b := hraw
    _ = (projection * (whitening * trueCovariance E n * whiteningᵀ) * projection).trace +
        b ⬝ᵥ b := by rw [hcov]
    _ = (projection * (whitening * trueCovariance E n * whiteningᵀ)).trace + b ⬝ᵥ b := by
      rw [trace_projectedCovariance projection
        (whitening * trueCovariance E n * whiteningᵀ) hidempotent]

theorem projectedCenteredQuadratic_variance
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hn : covariance.start ≤ n)
    (projection whitening : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) Real)
    (mean : Fin (E.maps.N n) → Real)
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection) :
    Var[projectedCenteredQuadratic E n projection whitening mean; P] =
      2 * (projection * (whitening * trueCovariance E n * whiteningᵀ) *
        projection *
        (whitening * trueCovariance E n * whiteningᵀ)).trace +
        4 * quadraticForm (whitening * trueCovariance E n * whiteningᵀ)
          (projection *ᵥ (whitening *ᵥ mean)) := by
  let b : Fin (E.maps.N n) → Real := projection *ᵥ (whitening *ᵥ mean)
  have hraw := rowScore_noncentralSquareSum_variance E covariance n hn
    (projection * whitening) b
  have hcov := projected_rowScoreCovariance_eq projection whitening
    (trueCovariance E n) hsymmetric
  have hb : projection *ᵥ b = b := by
    simpa only [b] using projection_mulVec_projectedMean projection whitening mean hidempotent
  have hsymmetric' : projection.IsSymm := by
    exact hsymmetric
  change Var[InfillGLSLean.FiniteWickBridge.noncentralSquareSum
    (fun i => centeredRegionalScore E n ((projection * whitening) i)) b; P] = _
  calc
    Var[InfillGLSLean.FiniteWickBridge.noncentralSquareSum
        (fun i => centeredRegionalScore E n ((projection * whitening) i)) b; P] =
        2 * (((projection * whitening) * trueCovariance E n *
          (projection * whitening)ᵀ) * ((projection * whitening) *
            trueCovariance E n * (projection * whitening)ᵀ)).trace +
          4 * quadraticForm ((projection * whitening) * trueCovariance E n *
            (projection * whitening)ᵀ) b := hraw
    _ = 2 * ((projection * (whitening * trueCovariance E n * whiteningᵀ) * projection) *
          (projection * (whitening * trueCovariance E n * whiteningᵀ) * projection)).trace +
          4 * quadraticForm (projection * (whitening * trueCovariance E n * whiteningᵀ) *
            projection) b := by rw [hcov]
    _ = 2 * (projection * (whitening * trueCovariance E n * whiteningᵀ) *
          projection * (whitening * trueCovariance E n * whiteningᵀ)).trace +
          4 * quadraticForm (whitening * trueCovariance E n * whiteningᵀ) b := by
      rw [trace_square_projectedCovariance projection
        (whitening * trueCovariance E n * whiteningᵀ) hidempotent,
        quadraticForm_projectedCovariance projection
          (whitening * trueCovariance E n * whiteningᵀ) hsymmetric' b hb]
    _ = 2 * (projection * (whitening * trueCovariance E n * whiteningᵀ) *
          projection * (whitening * trueCovariance E n * whiteningᵀ)).trace +
          4 * quadraticForm (whitening * trueCovariance E n * whiteningᵀ)
            (projection *ᵥ (whitening *ᵥ mean)) := by rfl

end InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge

