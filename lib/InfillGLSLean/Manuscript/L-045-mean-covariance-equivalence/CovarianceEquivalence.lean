module

public import «L-036-mean-hilbert-riesz».MeanHilbertRiesz
public import «L-041-common-refinement-pd».CommonRefinementPD
public import Mathlib.Tactic

/-!
# Converse covariance-function-space implication for Appendix `lem:mean`

This module keeps the paper's terms literal: a single outcome-L2 representer
whose covariance pairing equals the one fixed spatial residual yields a
uniform bound for the source's literal regional `meanOffset` vectors.  It is
not a replacement statement and does not add a refinement, rate, or
regularity assumption.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L045

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace
open InfillGLSLean.MeanHilbertRiesz
open InfillGLSLean.ManuscriptSpecification.L041

universe u

section Source

variable {D : CompactEuclideanDomain} {Ω : Type u}
  [MeasurableSpace Ω] {μ : Measure (Point D)} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The source-faithful finite Cauchy--Schwarz inequality behind the converse
of Appendix `lem:mean`.  The representer equality is exactly L-036's
spatial-L2 rendering of `f(s) = E[u(s)V]`; a regional weight is tested
against the literal normalized cell-average test, so no limiting or nesting
argument is being used here. -/
theorem meanOffset_score_sq_le_representer_mul_trueQuadratic
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : Lp ℝ 2 P)
    (hrepresentation : centeredErrorPairingL2 E V = spatialMeanOffsetL2 E c)
    (n : ℕ) (weight : Fin (E.maps.N n) → ℝ) :
    (meanOffset E c n ⬝ᵥ weight) ^ 2 ≤
      ‖V‖ ^ 2 * quadraticForm (trueCovariance E n) weight := by
  let test := weightedRegionalCellTestLp E n weight
  let score := centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight)
  have hscore : meanOffset E c n ⬝ᵥ weight = inner ℝ V score := by
    calc
      meanOffset E c n ⬝ᵥ weight = spatialMeanOffsetFunctional E c test :=
        (spatialMeanOffsetFunctional_weightedRegionalCellTest E c n weight).symm
      _ = inner ℝ (spatialMeanOffsetL2 E c) test := by
        exact spatialMeanOffsetFunctional_eq_inner E c test
      _ = inner ℝ (centeredErrorPairingL2 E V) test := by
        rw [hrepresentation]
      _ = inner ℝ V (centeredTestIntegralLp E cov test) :=
        inner_centeredErrorPairingL2_eq_inner_centeredTestIntegralLp E cov test V
      _ = inner ℝ V score := by
        rw [centeredTestIntegralLp_weightedRegionalCellTestLp]
  have hnorm : ‖score‖ ^ 2 = quadraticForm (trueCovariance E n) weight := by
    simpa only [score] using
      weightedRegionalCellTest_centeredIntegral_norm_sq_eq_trueQuadratic E cov n weight
  calc
    (meanOffset E c n ⬝ᵥ weight) ^ 2 = |inner ℝ V score| ^ 2 := by
      rw [hscore, sq_abs]
    _ ≤ (‖V‖ * ‖score‖) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (abs_real_inner_le_norm V score)
    _ = ‖V‖ ^ 2 * ‖score‖ ^ 2 := by ring
    _ = ‖V‖ ^ 2 * quadraticForm (trueCovariance E n) weight := by rw [hnorm]

/-- At one literal regional resolution, the covariance-function-space
representer bounds the inverse-*true*-covariance energy of the mean vector.
This is the finite Gram/projection inequality stated in the converse proof of
Appendix `lem:mean`; positive definiteness is derived from the existing
strict-variance source clause by L-041. -/
theorem meanOffset_truePrecisionEnergy_le_representer_norm_sq
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : Lp ℝ 2 P)
    (hrepresentation : centeredErrorPairingL2 E V = spatialMeanOffsetL2 E c)
    (n : ℕ) :
    quadraticForm
      ((trueCovariance E n)⁻¹ : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) ℝ)
      (meanOffset E c n) ≤ ‖V‖ ^ 2 := by
  classical
  let Sigma := trueCovariance E n
  let f := meanOffset E c n
  let w := Sigma⁻¹ *ᵥ f
  let q := quadraticForm Sigma⁻¹ f
  have hSigma : Sigma.PosDef := trueCovariance_posDef E cov n
  have hdet : IsUnit Sigma.det :=
    Sigma.isUnit_iff_isUnit_det.mp hSigma.isUnit
  have hSigmaw : Sigma *ᵥ w = f := by
    calc
      Sigma *ᵥ w = (Sigma * Sigma⁻¹) *ᵥ f := by
        simp only [w, Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) ℝ) *ᵥ f := by
        rw [Matrix.mul_nonsing_inv Sigma hdet]
      _ = f := by simp
  have hscore_eq : f ⬝ᵥ w = q := by
    simp only [q, w, quadraticForm_eq_dotProduct_mulVec]
  have hquadratic_eq : quadraticForm Sigma w = q := by
    rw [← InfillGLSLean.quadraticForm_inverse_working_mulVec_eq hSigma w, hSigmaw]
  have hfinite := meanOffset_score_sq_le_representer_mul_trueQuadratic
    E cov c V hrepresentation n w
  have hq_sq : q ^ 2 ≤ ‖V‖ ^ 2 * q := by
    simpa only [Sigma, f, hscore_eq, hquadratic_eq] using hfinite
  have hq_nonneg : 0 ≤ q := by
    change 0 ≤ quadraticForm Sigma⁻¹ f
    exact quadraticForm_nonneg hSigma.inv.posSemidef f
  have hq_le : q ≤ ‖V‖ ^ 2 := by
    by_cases hq_zero : q = 0
    · rw [hq_zero]
      positivity
    · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_zero)
      apply le_of_mul_le_mul_right
      · simpa only [pow_two] using hq_sq
      · exact hq_pos
  simpa only [Sigma, f, q] using hq_le

/-- The upper half of the manuscript covariance sandwich transfers the exact
finite representer bound from `Σ_n` to the inverse working covariance.  This
uses the same literal `meanOffset E c n` and one fixed representer; it adds
neither a comparison rate nor a refinement requirement. -/
theorem meanEnergy_le_representer_norm_sq_of_upperSandwich
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : Lp ℝ 2 P)
    (hrepresentation : centeredErrorPairingL2 E V = spatialMeanOffsetL2 E c)
    (n : ℕ) (hn : cov.start ≤ n) :
    meanEnergy E c n ≤
      (cov.sigmaSquared / (1 - cov.delta n)) * ‖V‖ ^ 2 := by
  classical
  obtain ⟨_hdelta_nonneg, _hdelta_lt_one, _hlower, hupper⟩ := cov.sandwich n hn
  let K := E.kernel n
  let f := meanOffset E c n
  let w := K⁻¹ *ᵥ f
  let a := cov.sigmaSquared / (1 - cov.delta n)
  let q := meanEnergy E c n
  have hK : K.PosDef := E.kernel_posDef n
  have hdet : IsUnit K.det := K.isUnit_iff_isUnit_det.mp hK.isUnit
  have hKw : K *ᵥ w = f := by
    calc
      K *ᵥ w = (K * K⁻¹) *ᵥ f := by
        simp only [w, Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) ℝ) *ᵥ f := by
        rw [Matrix.mul_nonsing_inv K hdet]
      _ = f := by simp
  have hscore_eq : f ⬝ᵥ w = q := by
    simp only [q, meanEnergy_eq, K, f, w, quadraticForm_eq_dotProduct_mulVec]
  have hworking_quadratic_eq : quadraticForm K w = q := by
    rw [← InfillGLSLean.quadraticForm_inverse_working_mulVec_eq hK w, hKw]
    simp only [q, meanEnergy_eq, K, f]
  have hupper' : (a • K - trueCovariance E n).PosSemidef := by
    simpa only [a, K] using hupper
  have htrue_quadratic_le : quadraticForm (trueCovariance E n) w ≤
      a * quadraticForm K w := by
    calc
      quadraticForm (trueCovariance E n) w ≤ quadraticForm (a • K) w :=
        quadraticForm_mono_of_posSemidef_sub hupper' w
      _ = a * quadraticForm K w := quadraticForm_smul a K w
  have hfinite := meanOffset_score_sq_le_representer_mul_trueQuadratic
    E cov c V hrepresentation n w
  have hq_sq : q ^ 2 ≤ (a * ‖V‖ ^ 2) * q := by
    calc
      q ^ 2 = (meanOffset E c n ⬝ᵥ w) ^ 2 := by
        simp only [f] at hscore_eq
        rw [hscore_eq]
      _ ≤ ‖V‖ ^ 2 * quadraticForm (trueCovariance E n) w := hfinite
      _ ≤ ‖V‖ ^ 2 * (a * quadraticForm K w) :=
        mul_le_mul_of_nonneg_left htrue_quadratic_le (sq_nonneg ‖V‖)
      _ = (a * ‖V‖ ^ 2) * q := by rw [hworking_quadratic_eq]; ring
  have hq_nonneg : 0 ≤ q := by
    change 0 ≤ meanEnergy E c n
    rw [meanEnergy_eq]
    exact quadraticForm_nonneg hK.inv.posSemidef f
  have hq_le : q ≤ a * ‖V‖ ^ 2 := by
    by_cases hq_zero : q = 0
    · rw [hq_zero]
      exact mul_nonneg (by
        dsimp [a]
        exact div_nonneg cov.sigmaSquared_pos.le (by linarith)) (sq_nonneg ‖V‖)
    · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_zero)
      apply le_of_mul_le_mul_right
      · simpa only [pow_two] using hq_sq
      · exact hq_pos
  simpa only [q, a] using hq_le

/-- Because the source's already-stated `δ_n → 0` makes the upper sandwich
factor eventually at most `2 σ²`, the representer gives one uniform tail
bound for the literal working-covariance energy. -/
theorem eventually_meanEnergy_le_two_sigmaSquared_mul_representer_norm_sq
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : Lp ℝ 2 P)
    (hrepresentation : centeredErrorPairingL2 E V = spatialMeanOffsetL2 E c) :
    ∀ᶠ n in atTop, meanEnergy E c n ≤
      (2 * cov.sigmaSquared) * ‖V‖ ^ 2 := by
  have hdelta_small : ∀ᶠ n in atTop, cov.delta n < (1 / 2 : ℝ) :=
    (tendsto_order.mp cov.delta_tendsto_zero).2 (1 / 2 : ℝ) (by norm_num)
  filter_upwards [eventually_ge_atTop cov.start, hdelta_small] with n hn hdelta
  have henergy := meanEnergy_le_representer_norm_sq_of_upperSandwich
    E cov c V hrepresentation n hn
  have hdenom : 0 < 1 - cov.delta n := by linarith
  have hfactor : cov.sigmaSquared / (1 - cov.delta n) ≤
      2 * cov.sigmaSquared := by
    apply (div_le_iff₀ hdenom).2
    nlinarith [cov.sigmaSquared_pos]
  calc
    meanEnergy E c n ≤ (cov.sigmaSquared / (1 - cov.delta n)) * ‖V‖ ^ 2 := henergy
    _ ≤ (2 * cov.sigmaSquared) * ‖V‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hfactor (sq_nonneg ‖V‖)

/-- An eventual real upper bound controls the whole sequence: the only
remaining values form a literal finite prefix.  This elementary lemma is
kept explicit so the converse proof does not silently discard early regional
resolutions. -/
theorem bddAbove_range_of_eventually_le
    {g : ℕ → ℝ} {B : ℝ} (htail : ∀ᶠ n in atTop, g n ≤ B) :
    BddAbove (Set.range g) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let prefixSet : Finset ℝ := (Finset.range (N + 1)).image g
  have hprefix_nonempty : prefixSet.Nonempty := by
    refine ⟨g 0, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨0, Finset.mem_range.mpr ?_, rfl⟩
    exact Nat.succ_pos N
  rw [bddAbove_def]
  refine ⟨max B (prefixSet.max' hprefix_nonempty), ?_⟩
  intro y hy
  obtain ⟨n, rfl⟩ := hy
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_max_left _ _)
  · have hn_lt : n < N := Nat.lt_of_not_ge hn
    have hn_mem : n ∈ Finset.range (N + 1) := by
      apply Finset.mem_range.mpr
      omega
    have hgn_mem : g n ∈ prefixSet := Finset.mem_image.mpr ⟨n, hn_mem, rfl⟩
    exact (Finset.le_max' prefixSet (g n) hgn_mem).trans (le_max_right _ _)

/-- A spatial covariance-pairing representer controls the complete (not only
eventual) range of the source inverse-working-covariance energy.  The bound
is obtained from the tail result above plus the literal finite prefix. -/
theorem bddAbove_meanEnergy_of_spatial_representer
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : Lp ℝ 2 P)
    (hrepresentation : centeredErrorPairingL2 E V = spatialMeanOffsetL2 E c) :
    BddAbove (Set.range (fun n => meanEnergy E c n)) :=
  bddAbove_range_of_eventually_le
    (eventually_meanEnergy_le_two_sigmaSquared_mul_representer_norm_sq
      E cov c V hrepresentation)

/-- The exact paper-facing converse: an L-036 covariance-Hilbert
representer for the fixed spatial residual supplies an existing
`FixedMeanAssumption`, with the same fixed coefficient vector `c`. -/
theorem exists_fixedMeanAssumption_of_covarianceHilbert_spatial_representer
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : covarianceHilbertSpace E cov)
    (hrepresentation :
      centeredErrorPairingL2 E (V : Lp ℝ 2 P) = spatialMeanOffsetL2 E c) :
    ∃ mean : FixedMeanAssumption E, mean.c = c := by
  refine ⟨⟨c, ?_⟩, rfl⟩
  exact bddAbove_meanEnergy_of_spatial_representer E cov c (V : Lp ℝ 2 P)
    hrepresentation

/-- Exact source-level form of the covariance-function-space equivalence in
Appendix `lem:mean`, for one fixed coefficient vector.  The left side is the
paper's displayed uniform inverse-working-covariance energy condition; the
right side is precisely L-036's covariance-Hilbert representer language.
No rate, nesting, or replacement residual is introduced. -/
theorem bddAbove_meanEnergy_iff_exists_covarianceHilbert_spatial_representer
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (c : Fin E.q → ℝ) :
    BddAbove (Set.range (fun n => meanEnergy E c n)) ↔
      ∃ V : covarianceHilbertSpace E cov,
        centeredErrorPairingL2 E (V : Lp ℝ 2 P) = spatialMeanOffsetL2 E c := by
  constructor
  · intro hbounded
    exact exists_covarianceHilbert_spatial_representer_of_fixedMeanAssumption E cov
      ⟨c, hbounded⟩
  · rintro ⟨V, hrepresentation⟩
    exact bddAbove_meanEnergy_of_spatial_representer E cov c (V : Lp ℝ 2 P)
      hrepresentation

end Source

end InfillGLSLean.ManuscriptSpecification.L045
