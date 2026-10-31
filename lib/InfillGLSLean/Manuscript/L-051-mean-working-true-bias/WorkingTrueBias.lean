module

public import «L-038-mean-weight-perturbation».SourceBridges
public import «L-045-mean-covariance-equivalence».CovarianceEquivalence
public import «L-048-mean-treatment-variance-sandwich».TreatmentVarianceSandwich
public import Mathlib.Tactic

/-!
# Working-versus-true bias transfer for Appendix `lem:mean`

This module is limited to the paragraph headed “Transfer to the working
weights” in `the source manuscript`.  It retains the paper's literal true
GLS row and working FWL row and builds their exact tail comparison; it neither
changes nor attempts to prove `manuscriptNormality`.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L051

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal MatrixOrder RealInnerProductSpace

open InfillGLSLean
open InfillGLSLean.MeanWeightPerturbation
open InfillGLSLean.MeanHilbertRiesz
open InfillGLSLean.ManuscriptSpecification.L037
open InfillGLSLean.ManuscriptSpecification.L041
open InfillGLSLean.ManuscriptSpecification.L042
open InfillGLSLean.ManuscriptSpecification.L045
open InfillGLSLean.ManuscriptSpecification.L047
open InfillGLSLean.ManuscriptSpecification.L048

universe u v

/-- The literal true-GLS treatment row has zero true-covariance score in the
direction from itself to any other complete-design feasible treatment row.
This is the unwhitened true first-order condition used in the paper's
working-weight transfer paragraph. -/
theorem observedTrueGLSOutcomeWeight_true_normal_condition
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ⬝ᵥ
        (trueCovariance E n *ᵥ observedTrueGLSOutcomeWeight E n) = 0 := by
  classical
  let design := regionalDesign μ E.maps E.treatment E.controls n
  let trueWeight := observedTrueGLSOutcomeWeight E n
  let workingWeight := observedWorkingGLSOutcomeWeight E n
  let Sigma := trueCovariance E n
  let B := trueGLSCoefficientCovariance Sigma design
  have hSigma : Sigma.PosDef := trueCovariance_posDef E covariance n
  have hgram : (trueGLSGram Sigma design).PosDef :=
    trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E hSigma hfull
  have htrue : Matrix.transpose design *ᵥ trueWeight =
      Pi.single (0 : Fin (E.q + 1)) 1 := by
    simpa only [design, trueWeight] using
      transpose_regionalDesign_mulVec_observedTrueGLSOutcomeWeight_eq_first
        E covariance n hfull
  have hworking : Matrix.transpose design *ᵥ workingWeight =
      Pi.single (0 : Fin (E.q + 1)) 1 := by
    rw [show workingWeight = observedWorkingGLSOutcomeWeight E n by rfl,
      show design = regionalDesign μ E.maps E.treatment E.controls n by rfl,
      transpose_regionalDesign_mulVec_observedWorkingGLSOutcomeWeight_eq_first E n hfull]
    ext j
    by_cases hj : j = 0
    · subst j
      simp
    · simp [hj]
  have hdifference : Matrix.transpose design *ᵥ (workingWeight - trueWeight) = 0 := by
    rw [Matrix.mulVec_sub, hworking, htrue]
    simp
  have hmap_covariance := trueGLSCoefficientMap_mul_covariance Sigma design hSigma
  have hsymm : ∀ i j, Sigma i j = Sigma j i := by
    intro i j
    exact (hSigma.isHermitian.isSymm.apply i j).symm
  have hnormal_vector : Sigma *ᵥ trueWeight = design *ᵥ (fun j => B 0 j) := by
    ext i
    have hentry := congrFun (congrFun hmap_covariance 0) i
    change (∑ j, Sigma i j * trueGLSCoefficientMap Sigma design 0 j) =
      ∑ j, design i j * B 0 j
    calc
      (∑ j, Sigma i j * trueGLSCoefficientMap Sigma design 0 j) =
          ∑ j, trueGLSCoefficientMap Sigma design 0 j * Sigma j i := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hsymm i j]
            ring
      _ = ∑ j, B 0 j * design i j := by
            simpa only [Matrix.mul_apply, Matrix.transpose_apply, B] using hentry
      _ = ∑ j, design i j * B 0 j := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
  change (workingWeight - trueWeight) ⬝ᵥ (Sigma *ᵥ trueWeight) = 0
  calc
    (workingWeight - trueWeight) ⬝ᵥ (Sigma *ᵥ trueWeight) =
        (workingWeight - trueWeight) ⬝ᵥ (design *ᵥ (fun j => B 0 j)) := by
          rw [hnormal_vector]
    _ = (fun j => B 0 j) ⬝ᵥ
        (Matrix.transpose design *ᵥ (workingWeight - trueWeight)) := by
          exact (Matrix.dotProduct_transpose_mulVec design (fun j => B 0 j)
            (workingWeight - trueWeight)).symm
    _ = 0 := by rw [hdifference]; simp

/-- The working FWL row has zero scaled-working-covariance score in the
direction from the literal true-GLS row.  This is the other unwhitened
first-order condition used by the transfer paragraph; full rank supplies the
already-existing finite FWL nonsingularity and relevance facts. -/
theorem observedWorkingGLSOutcomeWeight_working_normal_condition
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ⬝ᵥ
        ((covariance.sigmaSquared • E.kernel n) *ᵥ observedWorkingGLSOutcomeWeight E n) = 0 := by
  classical
  let controls := regionalControls μ E.maps E.controls n
  let treatment := regionalValues μ E.maps E.treatment n
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign treatment controls).rank = E.q + 1 := by
    change (InfillGLSLean.L023.sourceDesign
      (regionalValues μ E.maps E.treatment n)
      (regionalControls μ E.maps E.controls n)).rank = E.q + 1 at hfull
    exact hfull
  have hprecision : (E.kernel n)⁻¹ |>.PosDef := (E.kernel_posDef n).inv
  rcases InfillGLSLean.L023.sourceDesign_fwl_nonsingularity_and_relevance_of_full_rank
    treatment controls (E.kernel n)⁻¹ hprecision hfull_source with ⟨hgram, hresidual⟩
  have hfeasible :=
    observedTrueGLSOutcomeWeight_treatment_control_feasible E covariance n hfull
  have hbase :
      (observedTrueGLSOutcomeWeight E n - observedWorkingGLSOutcomeWeight E n) ⬝ᵥ
        (E.kernel n *ᵥ observedWorkingGLSOutcomeWeight E n) = 0 := by
    rw [observedWorkingGLSOutcomeWeight_eq]
    simpa only [controls, treatment] using
      (source_gls_weight_first_order_condition (E.kernel n) (E.kernel_posDef n)
        controls treatment hgram hresidual (observedTrueGLSOutcomeWeight E n)
        hfeasible.1 hfeasible.2)
  calc
    (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ⬝ᵥ
        ((covariance.sigmaSquared • E.kernel n) *ᵥ observedWorkingGLSOutcomeWeight E n) =
        covariance.sigmaSquared *
          ((observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ⬝ᵥ
            (E.kernel n *ᵥ observedWorkingGLSOutcomeWeight E n)) := by
          rw [Matrix.smul_mulVec, dotProduct_smul]
          rfl
    _ = 0 := by
      rw [show observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n =
        -(observedTrueGLSOutcomeWeight E n - observedWorkingGLSOutcomeWeight E n) by abel,
        neg_dotProduct, hbase, neg_zero, mul_zero]

/-- The paper's finite working-versus-true GLS perturbation inequality at one
source-full-rank resolution.  The two covariance-order premises are only
rescaled versions of the two displayed halves of `CovarianceAssumption.sandwich`;
the literal true row is handled through its exact normal condition above,
rather than replacing it with a different FWL definition. -/
theorem observedWorkingGLSOutcomeWeight_true_perturbation_of_full_rank
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ) (hstart : covariance.start ≤ n)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    quadraticForm (trueCovariance E n)
        (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ≤
      (covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
        observedTrueGLSTreatmentVariance E n := by
  classical
  rcases covariance.sandwich n hstart with
    ⟨hdelta_nonneg, hdelta_lt_one, hsandwich_lower, hsandwich_upper⟩
  have htruth : (trueCovariance E n).PosDef :=
    trueCovariance_posDef E covariance n
  have hworking : (covariance.sigmaSquared • E.kernel n).PosDef :=
    (E.kernel_posDef n).smul covariance.sigmaSquared_pos
  have hminus_pos : 0 < 1 - covariance.delta n := by linarith
  have hplus_pos : 0 < 1 + covariance.delta n := by linarith
  have hworking_lower :
      (covariance.sigmaSquared • E.kernel n -
        (1 - covariance.delta n) • trueCovariance E n).PosSemidef := by
    have hscaled := hsandwich_upper.smul hminus_pos.le
    convert hscaled using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt hminus_pos]
  have hworking_upper :
      ((1 + covariance.delta n) • trueCovariance E n -
        covariance.sigmaSquared • E.kernel n).PosSemidef := by
    have hscaled := hsandwich_lower.smul hplus_pos.le
    convert hscaled using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt hplus_pos]
  have hnormalize : ((CFC.sqrt (trueCovariance E n))⁻¹)ᵀ *
      trueCovariance E n * (CFC.sqrt (trueCovariance E n))⁻¹ =
        (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) ℝ) :=
    actual_inverse_sqrt_normalizes_covariance htruth
  have hrelative_lower' :=
    relative_error_lower_sandwich_of_covariance_lower_sandwich hnormalize
      hworking_lower
  have hrelative_upper' :=
    relative_error_upper_sandwich_of_covariance_upper_sandwich hnormalize
      hworking_upper
  have hrelative_lower :
      (covariance.delta n • (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) ℝ) +
        (CFC.sqrt (trueCovariance E n))⁻¹ *
          (covariance.sigmaSquared • E.kernel n - trueCovariance E n) *
          (CFC.sqrt (trueCovariance E n))⁻¹).PosSemidef := by
    simpa only [actual_inverse_sqrt_transpose] using hrelative_lower'
  have hrelative_upper :
      (covariance.delta n • (1 : Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) ℝ) -
        (CFC.sqrt (trueCovariance E n))⁻¹ *
          (covariance.sigmaSquared • E.kernel n - trueCovariance E n) *
          (CFC.sqrt (trueCovariance E n))⁻¹).PosSemidef := by
    simpa only [actual_inverse_sqrt_transpose] using hrelative_upper'
  have hfirst_order := actual_whitening_transports_first_order_conditions htruth
    (observedTrueGLSOutcomeWeight E n) (observedWorkingGLSOutcomeWeight E n)
    (observedTrueGLSOutcomeWeight_true_normal_condition E covariance n hfull)
    (observedWorkingGLSOutcomeWeight_working_normal_condition E covariance n hfull)
  have hperturbation := relative_perturbation_bound_of_sandwich_and_stationarity
    hdelta_nonneg hdelta_lt_one hrelative_lower hrelative_upper
    (CFC.sqrt (trueCovariance E n) *ᵥ observedTrueGLSOutcomeWeight E n)
    (CFC.sqrt (trueCovariance E n) *ᵥ
      (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n))
    hfirst_order.1 hfirst_order.2
  calc
    quadraticForm (trueCovariance E n)
        (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) =
        (CFC.sqrt (trueCovariance E n) *ᵥ
          (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n)) ⬝ᵥ
          (CFC.sqrt (trueCovariance E n) *ᵥ
            (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n)) :=
      (actual_sqrt_dot_eq_quadraticForm htruth _).symm
    _ ≤ (covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
        ((CFC.sqrt (trueCovariance E n) *ᵥ observedTrueGLSOutcomeWeight E n) ⬝ᵥ
          (CFC.sqrt (trueCovariance E n) *ᵥ observedTrueGLSOutcomeWeight E n)) :=
      hperturbation
    _ = (covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
        quadraticForm (trueCovariance E n) (observedTrueGLSOutcomeWeight E n) := by
      rw [actual_sqrt_dot_eq_quadraticForm htruth]
    _ = (covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
        observedTrueGLSTreatmentVariance E n := by
      rw [observedTrueGLSOutcomeWeight_quadraticForm_eq_treatmentVariance E covariance n hfull]

/-- The exact covariance-space consequence of the finite perturbation bound.
It is the squared form of the paper's Cauchy--Schwarz step for the difference
between the literal working and true GLS rows; `V` is the already-proved
fixed spatial representer, not a new mean assumption. -/
theorem observedWorkingGLSOutcomeWeight_scaled_meanOffset_sq_le_of_full_rank
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : Lp ℝ 2 P)
    (hrepresentation : centeredErrorPairingL2 E V = spatialMeanOffsetL2 E c)
    (n : ℕ) (hstart : covariance.start ≤ n)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    E.information n *
        ((observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ⬝ᵥ
          meanOffset E c n) ^ 2 ≤
      ‖V‖ ^ 2 *
        ((covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
          (E.information n * observedTrueGLSTreatmentVariance E n)) := by
  have hscore := meanOffset_score_sq_le_representer_mul_trueQuadratic E covariance c V
    hrepresentation n
    (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n)
  have hperturbation := observedWorkingGLSOutcomeWeight_true_perturbation_of_full_rank
    E covariance n hstart hfull
  have hnorm_nonneg : 0 ≤ ‖V‖ ^ 2 := sq_nonneg _
  have hscore_bound :
      ((observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ⬝ᵥ
          meanOffset E c n) ^ 2 ≤
        ‖V‖ ^ 2 *
          ((covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
            observedTrueGLSTreatmentVariance E n) := by
    calc
      ((observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ⬝ᵥ
          meanOffset E c n) ^ 2 =
          (meanOffset E c n ⬝ᵥ
            (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n)) ^ 2 := by
        rw [dotProduct_comm]
      _ ≤
          ‖V‖ ^ 2 * quadraticForm (trueCovariance E n)
            (observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) :=
        hscore
      _ ≤ ‖V‖ ^ 2 *
          ((covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
            observedTrueGLSTreatmentVariance E n) :=
        mul_le_mul_of_nonneg_left hperturbation hnorm_nonneg
  have hinformation_nonneg : 0 ≤ E.information n :=
    (observed_information_pos_of_full_rank E n hfull).le
  calc
    E.information n *
        ((observedWorkingGLSOutcomeWeight E n - observedTrueGLSOutcomeWeight E n) ⬝ᵥ
          meanOffset E c n) ^ 2 ≤
        E.information n *
          (‖V‖ ^ 2 *
            ((covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
              observedTrueGLSTreatmentVariance E n)) :=
      mul_le_mul_of_nonneg_left hscore_bound hinformation_nonneg
    _ = ‖V‖ ^ 2 *
        ((covariance.delta n ^ 2 / (1 - covariance.delta n) ^ 2) *
          (E.information n * observedTrueGLSTreatmentVariance E n)) := by ring

/-- Reindexed tail form of the paper's conclusion
`√Q_n (ω_n - ω_n^*)' f_n → 0`.  The shift contains only the already-stated
covariance-sandwich start and eventual full-rank start.  This is deliberately
limited to the deterministic working-minus-true mean-bias transfer, so it can
be combined with the separately formalized true-GLS contribution. -/
theorem exists_reindexed_tendsto_sqrt_information_working_minus_true_meanOffset_of_representer
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : Lp ℝ 2 P)
    (hrepresentation : centeredErrorPairingL2 E V = spatialMeanOffsetL2 E c) :
    ∃ start : ℕ,
      Tendsto
        (fun n => Real.sqrt (E.information (n + start)) *
          ((observedWorkingGLSOutcomeWeight E (n + start) -
            observedTrueGLSOutcomeWeight E (n + start)) ⬝ᵥ
              meanOffset E c (n + start)))
        atTop (nhds 0) := by
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  let start := max covariance.start rankStart
  refine ⟨start, ?_⟩
  let score : ℕ → ℝ := fun n =>
    (observedWorkingGLSOutcomeWeight E (n + start) -
      observedTrueGLSOutcomeWeight E (n + start)) ⬝ᵥ meanOffset E c (n + start)
  have hstart_shift : ∀ n : ℕ, covariance.start ≤ n + start := by
    intro n
    dsimp [start]
    exact le_trans (le_max_left _ _) (Nat.le_add_left _ _)
  have hrank_shift : ∀ n : ℕ, rankStart ≤ n + start := by
    intro n
    dsimp [start]
    exact le_trans (le_max_right _ _) (Nat.le_add_left _ _)
  have hfull_shift : ∀ n : ℕ,
      (regionalDesign μ E.maps E.treatment E.controls (n + start)).rank = E.q + 1 := by
    intro n
    exact hfull (n + start) (hrank_shift n)
  have hinformation_nonneg : ∀ n : ℕ, 0 ≤ E.information (n + start) := by
    intro n
    exact (observed_information_pos_of_full_rank E (n + start) (hfull_shift n)).le
  have hdelta_shift : Tendsto (fun n => covariance.delta (n + start)) atTop (nhds 0) := by
    exact (tendsto_add_atTop_iff_nat start).mpr covariance.delta_tendsto_zero
  have hgap : Tendsto (fun n => (1 : ℝ) - covariance.delta (n + start)) atTop
      (nhds (1 - 0)) := tendsto_const_nhds.sub hdelta_shift
  have hfactor : Tendsto
      (fun n => covariance.delta (n + start) ^ 2 /
        (1 - covariance.delta (n + start)) ^ 2) atTop (nhds 0) := by
    change Tendsto
      ((fun n => covariance.delta (n + start) ^ 2) /
        fun n => (1 - covariance.delta (n + start)) ^ 2) atTop (nhds 0)
    simpa using (hdelta_shift.pow 2).div (hgap.pow 2)
      (by norm_num : (1 - 0 : ℝ) ^ 2 ≠ 0)
  have hvariance : Tendsto
      (fun n => E.information (n + start) *
        observedTrueGLSTreatmentVariance E (n + start)) atTop
        (nhds covariance.sigmaSquared) := by
    exact (tendsto_add_atTop_iff_nat start).mpr
      (information_mul_observedTrueGLSTreatmentVariance_tendsto_sigmaSquared E covariance)
  have hproduct : Tendsto
      (fun n => (covariance.delta (n + start) ^ 2 /
        (1 - covariance.delta (n + start)) ^ 2) *
        (E.information (n + start) *
          observedTrueGLSTreatmentVariance E (n + start))) atTop (nhds 0) := by
    simpa using hfactor.mul hvariance
  have henvelope : Tendsto
      (fun n => ‖V‖ ^ 2 *
        ((covariance.delta (n + start) ^ 2 /
          (1 - covariance.delta (n + start)) ^ 2) *
          (E.information (n + start) *
            observedTrueGLSTreatmentVariance E (n + start)))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hproduct
  have hfinite : ∀ n : ℕ,
      E.information (n + start) * score n ^ 2 ≤ ‖V‖ ^ 2 *
        ((covariance.delta (n + start) ^ 2 /
          (1 - covariance.delta (n + start)) ^ 2) *
          (E.information (n + start) *
            observedTrueGLSTreatmentVariance E (n + start))) := by
    intro n
    simpa only [score] using
      (observedWorkingGLSOutcomeWeight_scaled_meanOffset_sq_le_of_full_rank
        E covariance c V hrepresentation (n + start) (hstart_shift n) (hfull_shift n))
  have hsquared : Tendsto
      (fun n => E.information (n + start) * score n ^ 2) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henvelope
    · exact Filter.Eventually.of_forall (fun n =>
        mul_nonneg (hinformation_nonneg n) (sq_nonneg _))
    · exact Filter.Eventually.of_forall hfinite
  have hroot_squared : Tendsto
      (fun n => (Real.sqrt (E.information (n + start)) * score n) ^ 2)
      atTop (nhds 0) := by
    refine hsquared.congr' (Filter.Eventually.of_forall (fun n => ?_))
    change E.information (n + start) * score n ^ 2 =
      (Real.sqrt (E.information (n + start)) * score n) ^ 2
    rw [mul_pow, Real.sq_sqrt (hinformation_nonneg n)]
  have hroot : Tendsto
      (fun n => Real.sqrt (E.information (n + start)) * score n) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using hroot_squared.sqrt
  simpa only [score] using hroot

end InfillGLSLean.ManuscriptSpecification.L051
