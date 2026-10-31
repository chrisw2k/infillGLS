module

public import «L-051-mean-working-true-bias».WorkingTrueBias
public import «L-052-mean-representer-evaluation».RepresenterEvaluation
public import Mathlib.Tactic

namespace InfillGLSLean.ManuscriptSpecification.L054

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal RealInnerProductSpace

open InfillGLSLean.ManuscriptSpecification.L044
open InfillGLSLean.ManuscriptSpecification.L047
open InfillGLSLean.ManuscriptSpecification.L048
open InfillGLSLean.ManuscriptSpecification.L051
open InfillGLSLean.ManuscriptSpecification.L052
open InfillGLSLean.MeanHilbertRiesz

universe v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

public section

/- The squared variant is useful while auditing the cancellation, but the
actual source proof uses the direct normalized product below. -/
private theorem sqrt_mul_score_sq_eq_normalized_product_sq (Q v t : ℝ)
    (hQ : 0 ≤ Q) (hv : 0 < v) :
    (Real.sqrt Q * t) ^ 2 = (Q * v) * (t / Real.sqrt v) ^ 2 := by
  have hsqrtv : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hv)
  rw [mul_pow, Real.sq_sqrt hQ]
  field_simp [hsqrtv]
  rw [Real.sq_sqrt hv.le]

/-- Exact algebra reassembling a normalized true score and `Q*v`. -/
private theorem sqrt_mul_score_eq_normalized_product (Q v t : ℝ)
    (hQ : 0 ≤ Q) (hv : 0 < v) :
    Real.sqrt Q * t = Real.sqrt (Q * v) * (t / Real.sqrt v) := by
  have hsqrtv : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hv)
  rw [Real.sqrt_mul hQ]
  field_simp [hsqrtv]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The L-048 proof-only row and L-044 true score use the same literal first
row of the true GLS coefficient map.  This is a local definitional bridge,
not a replacement of either row. -/
private theorem observedTrueGLSOutcomeWeight_eq_trueGLSOutcomeWeight
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    observedTrueGLSOutcomeWeight E n =
      trueGLSOutcomeWeight (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) 0 := rfl

/-- The true-GLS half of the final deterministic mean-bias calculation in
Appendix `lem:mean`: L-052's normalized true score is multiplied back by the
source-normalized variance `Q_n v_n`. -/
private theorem exists_reindexed_tendsto_sqrt_information_true_meanOffset
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ start : ℕ,
      Tendsto (fun n =>
        Real.sqrt (E.information (n + start)) *
          (observedTrueGLSOutcomeWeight E (n + start) ⬝ᵥ
            meanOffset E mean.c (n + start)))
        atTop (nhds 0) := by
  rcases exists_reindexed_trueGLS_mean_bias_div_sqrt_variance_tendsto_zero
      E covariance mean with ⟨trueStart, htrue⟩
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  let start := covariance.start + rankStart + trueStart
  refine ⟨start, ?_⟩
  have htrue_shift : Tendsto (fun n =>
      (observedTrueGLSOutcomeWeight E (n + start) ⬝ᵥ
        meanOffset E mean.c (n + start)) /
        Real.sqrt (observedTrueGLSTreatmentVariance E (n + start)))
      atTop (nhds 0) := by
    have hshift := (tendsto_add_atTop_iff_nat (covariance.start + rankStart)).mpr htrue
    have hindex : ∀ n : ℕ,
        n + start = (n + (covariance.start + rankStart)) + trueStart := by
      intro n
      dsimp [start]
      omega
    refine hshift.congr' ?_
    filter_upwards [] with n
    simp only [observedTrueGLSOutcomeWeight_eq_trueGLSOutcomeWeight]
    rw [hindex n]
  have hQv_shift : Tendsto (fun n =>
      E.information (n + start) * observedTrueGLSTreatmentVariance E (n + start))
      atTop (nhds covariance.sigmaSquared) := by
    exact (tendsto_add_atTop_iff_nat start).mpr
      (information_mul_observedTrueGLSTreatmentVariance_tendsto_sigmaSquared E covariance)
  have hcov_start : ∀ n : ℕ, covariance.start ≤ n + start := by
    intro n
    dsimp [start]
    omega
  have hrank_start : ∀ n : ℕ, rankStart ≤ n + start := by
    intro n
    dsimp [start]
    omega
  have hfull_start : ∀ n : ℕ,
      (regionalDesign μ E.maps E.treatment E.controls (n + start)).rank = E.q + 1 := by
    intro n
    exact hfull (n + start) (hrank_start n)
  have hQpos : ∀ n : ℕ, 0 < E.information (n + start) := by
    intro n
    exact observed_information_pos_of_full_rank E (n + start) (hfull_start n)
  have hvpos : ∀ n : ℕ, 0 < observedTrueGLSTreatmentVariance E (n + start) := by
    intro n
    have hsand := observedTrueGLSTreatmentVariance_sandwich_of_full_rank
      E covariance (n + start) (hcov_start n) (hfull_start n)
    rcases covariance.sandwich (n + start) (hcov_start n) with
      ⟨hdelta_nonneg, _, _, _⟩
    have hplus : 0 < 1 + covariance.delta (n + start) := by linarith
    have hdenom : 0 < (1 + covariance.delta (n + start)) *
        E.information (n + start) :=
      mul_pos hplus (hQpos n)
    have hlower : 0 < covariance.sigmaSquared /
        ((1 + covariance.delta (n + start)) * E.information (n + start)) :=
      div_pos covariance.sigmaSquared_pos hdenom
    exact lt_of_lt_of_le hlower hsand.1
  have hnormalized_product : Tendsto (fun n =>
      Real.sqrt (E.information (n + start) *
        observedTrueGLSTreatmentVariance E (n + start)) *
      ((observedTrueGLSOutcomeWeight E (n + start) ⬝ᵥ
        meanOffset E mean.c (n + start)) /
        Real.sqrt (observedTrueGLSTreatmentVariance E (n + start))))
      atTop (nhds 0) := by
    simpa using hQv_shift.sqrt.mul htrue_shift
  refine hnormalized_product.congr' (Filter.Eventually.of_forall (fun n => ?_))
  exact (sqrt_mul_score_eq_normalized_product
    (E.information (n + start))
    (observedTrueGLSTreatmentVariance E (n + start))
    (observedTrueGLSOutcomeWeight E (n + start) ⬝ᵥ meanOffset E mean.c (n + start))
    (hQpos n).le (hvpos n)).symm

/-- The exact conclusion `sqrt(Q_n) * omega_n' f_n -> 0` of Appendix
`lem:mean`, obtained by adding the already-proved working-minus-true and
true-GLS contributions.  The only representer is derived from the manuscript
fixed-mean assumption. -/
theorem exists_reindexed_tendsto_sqrt_information_working_meanOffset
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ start : ℕ,
      Tendsto (fun n =>
        Real.sqrt (E.information (n + start)) *
          (observedWorkingGLSOutcomeWeight E (n + start) ⬝ᵥ
            meanOffset E mean.c (n + start)))
        atTop (nhds 0) := by
  rcases exists_covarianceHilbert_spatial_representer_of_fixedMeanAssumption
      E covariance mean with ⟨V, hrepresentation⟩
  rcases exists_reindexed_tendsto_sqrt_information_working_minus_true_meanOffset_of_representer
      E covariance mean.c (V : Lp ℝ 2 P) hrepresentation with ⟨differenceStart, hdifference⟩
  rcases exists_reindexed_tendsto_sqrt_information_true_meanOffset
      E covariance mean with ⟨trueStart, htrue⟩
  let start := differenceStart + trueStart
  refine ⟨start, ?_⟩
  have htrue_shift : Tendsto (fun n =>
      Real.sqrt (E.information (n + start)) *
        (observedTrueGLSOutcomeWeight E (n + start) ⬝ᵥ
          meanOffset E mean.c (n + start)))
      atTop (nhds 0) := by
    have hshift := (tendsto_add_atTop_iff_nat differenceStart).mpr htrue
    have hindex : ∀ n : ℕ,
        n + start = (n + differenceStart) + trueStart := by
      intro n
      dsimp [start]
      omega
    refine hshift.congr' ?_
    filter_upwards [] with n
    rw [hindex n]
  have hdifference_shift : Tendsto (fun n =>
      Real.sqrt (E.information (n + start)) *
        ((observedWorkingGLSOutcomeWeight E (n + start) -
          observedTrueGLSOutcomeWeight E (n + start)) ⬝ᵥ
          meanOffset E mean.c (n + start)))
      atTop (nhds 0) := by
    have hshift := (tendsto_add_atTop_iff_nat trueStart).mpr hdifference
    have hindex : ∀ n : ℕ,
        n + start = (n + trueStart) + differenceStart := by
      intro n
      dsimp [start]
      omega
    refine hshift.congr' ?_
    filter_upwards [] with n
    rw [hindex n]
  have hsum : Tendsto (fun n =>
      Real.sqrt (E.information (n + start)) *
        ((observedWorkingGLSOutcomeWeight E (n + start) -
          observedTrueGLSOutcomeWeight E (n + start)) ⬝ᵥ
          meanOffset E mean.c (n + start)) +
      Real.sqrt (E.information (n + start)) *
        (observedTrueGLSOutcomeWeight E (n + start) ⬝ᵥ
          meanOffset E mean.c (n + start)))
      atTop (nhds 0) := by
    simpa using hdifference_shift.add htrue_shift
  refine hsum.congr' (Filter.Eventually.of_forall (fun n => ?_))
  change Real.sqrt (E.information (n + start)) *
      ((observedWorkingGLSOutcomeWeight E (n + start) -
        observedTrueGLSOutcomeWeight E (n + start)) ⬝ᵥ
        meanOffset E mean.c (n + start)) +
    Real.sqrt (E.information (n + start)) *
      (observedTrueGLSOutcomeWeight E (n + start) ⬝ᵥ
        meanOffset E mean.c (n + start)) =
      Real.sqrt (E.information (n + start)) *
        (observedWorkingGLSOutcomeWeight E (n + start) ⬝ᵥ
          meanOffset E mean.c (n + start))
  rw [sub_dotProduct]
  ring

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The literal working FWL row annihilates every observed control column,
so its mean score is unchanged by replacing the conditional mean with the
paper's fixed residual `m_n - W_n c`. -/
private theorem observedWorkingGLSOutcomeWeight_dot_conditionalMean_eq_meanOffset
    (E : FixedConditionalExperiment μ P) (n : ℕ) (c : Fin E.q → ℝ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    observedWorkingGLSOutcomeWeight E n ⬝ᵥ
        regionalConditionalMean E.maps P E.error n =
      observedWorkingGLSOutcomeWeight E n ⬝ᵥ meanOffset E c n := by
  classical
  let controls := regionalControls μ E.maps E.controls n
  let weight := observedWorkingGLSOutcomeWeight E n
  have hdesign :=
    transpose_regionalDesign_mulVec_observedWorkingGLSOutcomeWeight_eq_first E n hfull
  have hcontrols_transpose : Matrix.transpose controls *ᵥ weight = 0 := by
    ext j
    have hentry := congrFun hdesign j.succ
    change (Matrix.transpose controls *ᵥ weight) j = 0
    simpa [Matrix.mulVec, Matrix.transpose_apply, regionalDesign_apply,
      Fin.cases_succ, dotProduct, controls, weight] using hentry
  have hcontrol_dot : weight ⬝ᵥ (controls *ᵥ c) = 0 := by
    calc
      weight ⬝ᵥ (controls *ᵥ c) =
          c ⬝ᵥ (Matrix.transpose controls *ᵥ weight) := by
            simpa using
              (Matrix.dotProduct_transpose_mulVec (Matrix.transpose controls) weight c)
      _ = (Matrix.transpose controls *ᵥ weight) ⬝ᵥ c := dotProduct_comm _ _
      _ = 0 := by rw [hcontrols_transpose]; simp
  have hmean : regionalConditionalMean E.maps P E.error n =
      meanOffset E c n + controls *ᵥ c := by
    rw [meanOffset]
    abel
  change weight ⬝ᵥ regionalConditionalMean E.maps P E.error n =
    weight ⬝ᵥ meanOffset E c n
  rw [hmean, dotProduct_add, hcontrol_dot, add_zero]

/-- Equation (bias) in the paper: after the fixed control adjustment, the
literal working GLS row has negligible scaled conditional mean on a reindexed
tail. -/
theorem exists_reindexed_tendsto_sqrt_information_working_conditionalMean
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ start : ℕ,
      Tendsto (fun n =>
        Real.sqrt (E.information (n + start)) *
          (observedWorkingGLSOutcomeWeight E (n + start) ⬝ᵥ
            regionalConditionalMean E.maps P E.error (n + start)))
        atTop (nhds 0) := by
  rcases exists_reindexed_tendsto_sqrt_information_working_meanOffset
      E covariance mean with ⟨meanStart, hmean⟩
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  let start := rankStart + meanStart
  refine ⟨start, ?_⟩
  have hmean_shift : Tendsto (fun n =>
      Real.sqrt (E.information (n + start)) *
        (observedWorkingGLSOutcomeWeight E (n + start) ⬝ᵥ
          meanOffset E mean.c (n + start)))
      atTop (nhds 0) := by
    have hshift := (tendsto_add_atTop_iff_nat rankStart).mpr hmean
    have hindex : ∀ n : ℕ, n + start = (n + rankStart) + meanStart := by
      intro n
      dsimp [start]
      omega
    refine hshift.congr' ?_
    filter_upwards [] with n
    rw [hindex n]
  have hrank : ∀ n : ℕ, rankStart ≤ n + start := by
    intro n
    dsimp [start]
    omega
  refine hmean_shift.congr' (Filter.Eventually.of_forall (fun n => ?_))
  change Real.sqrt (E.information (n + start)) *
      (observedWorkingGLSOutcomeWeight E (n + start) ⬝ᵥ
        meanOffset E mean.c (n + start)) =
    Real.sqrt (E.information (n + start)) *
      (observedWorkingGLSOutcomeWeight E (n + start) ⬝ᵥ
        regionalConditionalMean E.maps P E.error (n + start))
  rw [observedWorkingGLSOutcomeWeight_dot_conditionalMean_eq_meanOffset
    E (n + start) mean.c (hfull (n + start) (hrank n))]

end

end InfillGLSLean.ManuscriptSpecification.L054

