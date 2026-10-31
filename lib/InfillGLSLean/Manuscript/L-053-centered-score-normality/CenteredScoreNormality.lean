module

public import «L-034-normality-exact-integration».Explore
public import «L-047-mean-information-assembly».InformationAssembly
public import InfillGLSLean
import Mathlib.Tactic

/-!
# Centered working-score normality for Proposition `prop:normality`

This module formalizes the centered-score paragraph of
`the source manuscript:692--693`.  It retains the paper's literal working
GLS outcome row and its literal normalization by `sqrt(Q_n) / sigma`; it does
not replace that score by a true-GLS score, assert a bias conclusion, or alter
`manuscriptNormality`.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L053

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal

open InfillGLSLean
open InfillGLSLean.ManuscriptSpecification.L034
open InfillGLSLean.ManuscriptSpecification.L041
open InfillGLSLean.ManuscriptSpecification.L047

universe v

/-- A private, standard distributional bridge: coupling a centered Gaussian
law with a standard Gaussian shows that nonnegative variance parameters
converging to one yield a standard-normal distributional limit.  This is only
Mathlib's affine-Gaussian and distributional-convergence machinery; the
source-specific score is supplied below. -/
private theorem gaussian_zero_variance_tendsto_standard
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {variance : ℕ → ℝ}
    (hvariance_nonneg : ∀ n, 0 ≤ variance n)
    (hlaw : ∀ n, HasLaw (X n) (gaussianReal 0 (variance n).toNNReal) P)
    (hvariance : Tendsto variance atTop (nhds 1)) :
    TendstoInDistribution X atTop (fun z : ℝ => z)
      (fun _ => P) (gaussianReal 0 1) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (variance n)) atTop (nhds 1) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 1).comp hvariance
  have hbase : TendstoInDistribution
      (fun n (z : ℝ) => Real.sqrt (variance n) * z + 0) atTop
      (fun z : ℝ => z) (fun _ => gaussianReal 0 1) (gaussianReal 0 1) := by
    exact InfillGLSLean.gaussian_scale_and_bias_tendstoInDistribution
      (P := gaussianReal 0 1) (X := fun z : ℝ => z) (variance := (1 : NNReal))
      ProbabilityTheory.HasLaw.id hsqrt (by exact tendsto_const_nhds)
  have hscaleLaw : ∀ n, HasLaw
      (fun z : ℝ => Real.sqrt (variance n) * z + 0)
      (gaussianReal 0 (variance n).toNNReal) (gaussianReal 0 1) := by
    intro n
    convert gaussianReal_const_mul
        (ProbabilityTheory.HasLaw.id : HasLaw (fun z : ℝ => z)
          (gaussianReal 0 (1 : NNReal)) (gaussianReal 0 1))
        (Real.sqrt (variance n)) using 1
    · ext z
      simp
    · congr 1
      · simp
      · apply NNReal.coe_injective
        simp only [NNReal.coe_mk, mul_one]
        rw [Real.sq_sqrt (hvariance_nonneg n), Real.coe_toNNReal _ (hvariance_nonneg n)]
  refine {
    forall_aemeasurable := fun n => (hlaw n).aemeasurable
    aemeasurable_limit := measurable_id.aemeasurable
    tendsto := ?_
  }
  have hmaps : ∀ n, P.map (X n) =
      (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (variance n) * z + 0) := by
    intro n
    exact (hlaw n).map_eq.trans (hscaleLaw n).map_eq.symm
  have hfun :
      (fun n => (⟨P.map (X n), inferInstance⟩ : ProbabilityMeasure ℝ)) =
        fun n => (⟨(gaussianReal 0 1).map
          (fun z : ℝ => Real.sqrt (variance n) * z + 0), inferInstance⟩ :
          ProbabilityMeasure ℝ) := by
    funext n
    apply Subtype.ext
    exact hmaps n
  rw [hfun]
  exact hbase.tendsto

/-- The exact covariance-sandwich variance ratio for the paper's *working*
GLS score.  This remains private because it is an intermediate calculation
whose source-facing distributional consequence is exported below. -/
private theorem working_variance_ratio_tendsto_one
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    Tendsto (fun n =>
      (E.information n * quadraticForm (trueCovariance E n)
        (observedWorkingGLSOutcomeWeight E n)) / covariance.sigmaSquared)
      atTop (nhds 1) := by
  apply InfillGLSLean.varyingIndex_normalizedVariance_tendsto_one_of_eventually_covariance_sandwich
    covariance.sigmaSquared_pos
  · filter_upwards [eventually_ge_atTop covariance.start] with n hn
    exact (covariance.sandwich n hn).1
  · filter_upwards [eventually_ge_atTop covariance.start] with n hn
    exact (covariance.sandwich n hn).2.1
  · exact covariance.delta_tendsto_zero
  · exact E.information_tendsto.eventually (eventually_gt_atTop (0 : ℝ))
  · filter_upwards [eventually_ge_atTop covariance.start] with n hn
    exact (covariance.sandwich n hn).2.2.1
  · filter_upwards [eventually_ge_atTop covariance.start] with n hn
    exact (covariance.sandwich n hn).2.2.2
  · rcases E.eventual_full_rank with ⟨start, hfull⟩
    filter_upwards [eventually_ge_atTop start] with n hn
    exact observedWorkingGLSOutcomeWeight_quadraticForm_eq_inv_information E n (hfull n hn)

/-- The finite Gaussian law of the exact normalized centered working score.
The only local positivity premise is supplied later by the existing diverging
information field; it changes no source covariance, score, or normalization. -/
private theorem scaled_working_score_hasLaw
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ) (hinformation : 0 < E.information n) :
    HasLaw
      (fun ω =>
        (Real.sqrt (E.information n) / Real.sqrt covariance.sigmaSquared) *
          finiteWeightedScore (observedWorkingGLSOutcomeWeight E n)
            (centeredFiniteError
              (regionalRandomValues μ E.maps E.error n)
              (regionalConditionalMean E.maps P E.error n)) ω)
      (gaussianReal 0
        ((E.information n * quadraticForm (trueCovariance E n)
          (observedWorkingGLSOutcomeWeight E n)) /
          covariance.sigmaSquared).toNNReal) P := by
  let weight := observedWorkingGLSOutcomeWeight E n
  let score := finiteWeightedScore weight
    (centeredFiniteError
      (regionalRandomValues μ E.maps E.error n)
      (regionalConditionalMean E.maps P E.error n))
  let scale := Real.sqrt (E.information n) / Real.sqrt covariance.sigmaSquared
  let qform := quadraticForm (trueCovariance E n) weight
  have hqform_nonneg : 0 ≤ qform := by
    exact quadraticForm_nonneg (trueCovariance_posDef E covariance n).posSemidef weight
  have hvariance_nonneg : 0 ≤ (E.information n * qform) / covariance.sigmaSquared := by
    exact div_nonneg (mul_nonneg hinformation.le hqform_nonneg) covariance.sigmaSquared_pos.le
  have hraw := centered_regional_score_hasLaw E covariance n weight
  change HasLaw (fun ω => scale * score ω)
    (gaussianReal 0 ((E.information n * qform) / covariance.sigmaSquared).toNNReal) P
  convert gaussianReal_const_mul hraw scale using 1
  · congr 1
    · simp
    · apply NNReal.coe_injective
      simp only [NNReal.coe_mul, NNReal.coe_mk]
      rw [Real.coe_toNNReal _ hqform_nonneg]
      dsimp only [scale]
      rw [div_pow, Real.sq_sqrt hinformation.le,
        Real.sq_sqrt covariance.sigmaSquared_pos.le]
      rw [Real.coe_toNNReal _ hvariance_nonneg]
      field_simp [covariance.sigmaSquared_pos.ne']

/-- The centered term in the proof of Proposition `prop:normality` is
asymptotically standard normal on a reindexed tail.  Written literally, this
is `sqrt(Q_n) / sigma * omega_n' (epsilon_n - m_n)`.  The selected start is
the maximum of the experiment's existing positive-information tail and its
existing full-rank tail; reindexing discards no asymptotically relevant term
and makes this endpoint directly compatible with the exact FWL decomposition.
No true-GLS substitution or mean/bias conclusion is made here. -/
theorem exists_reindexed_centeredWorkingGLSScore_tendsto_standardNormal
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∃ start : ℕ,
      TendstoInDistribution
        (fun n ω =>
          (Real.sqrt (E.information (n + start)) /
            Real.sqrt covariance.sigmaSquared) *
            finiteWeightedScore (observedWorkingGLSOutcomeWeight E (n + start))
              (centeredFiniteError
                (regionalRandomValues μ E.maps E.error (n + start))
                (regionalConditionalMean E.maps P E.error (n + start))) ω)
        atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1) := by
  have hinformation_eventually : ∀ᶠ n in atTop, 0 < E.information n :=
    E.information_tendsto.eventually (eventually_gt_atTop (0 : ℝ))
  rcases eventually_atTop.1 hinformation_eventually with ⟨informationStart, hinformation⟩
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  let start := max informationStart rankStart
  have hinformation_tail : ∀ n, 0 < E.information (n + start) := by
    intro n
    exact hinformation (n + start) (le_trans (le_max_left _ _) (Nat.le_add_left _ _))
  have hfull_tail : ∀ n,
      (regionalDesign μ E.maps E.treatment E.controls (n + start)).rank = E.q + 1 := by
    intro n
    exact hfull (n + start) (le_trans (le_max_right _ _) (Nat.le_add_left _ _))
  have hratio := working_variance_ratio_tendsto_one E covariance
  have hratio_tail : Tendsto (fun n =>
      (E.information (n + start) * quadraticForm (trueCovariance E (n + start))
        (observedWorkingGLSOutcomeWeight E (n + start))) / covariance.sigmaSquared)
      atTop (nhds 1) :=
    (tendsto_add_atTop_iff_nat start).mpr hratio
  let X : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt (E.information (n + start)) / Real.sqrt covariance.sigmaSquared) *
      finiteWeightedScore (observedWorkingGLSOutcomeWeight E (n + start))
        (centeredFiniteError
          (regionalRandomValues μ E.maps E.error (n + start))
          (regionalConditionalMean E.maps P E.error (n + start))) ω
  let variance : ℕ → ℝ := fun n =>
    (E.information (n + start) * quadraticForm (trueCovariance E (n + start))
      (observedWorkingGLSOutcomeWeight E (n + start))) / covariance.sigmaSquared
  have hvariance_nonneg : ∀ n, 0 ≤ variance n := by
    intro n
    apply div_nonneg
    · apply mul_nonneg (hinformation_tail n).le
      exact quadraticForm_nonneg
        (trueCovariance_posDef E covariance (n + start)).posSemidef
        (observedWorkingGLSOutcomeWeight E (n + start))
    · exact covariance.sigmaSquared_pos.le
  have hlaw : ∀ n, HasLaw (X n) (gaussianReal 0 (variance n).toNNReal) P := by
    intro n
    simpa only [X, variance] using
      scaled_working_score_hasLaw E covariance (n + start) (hinformation_tail n)
  have hvariance : Tendsto variance atTop (nhds 1) := by
    simpa only [variance] using hratio_tail
  refine ⟨start, ?_⟩
  simpa only [X] using gaussian_zero_variance_tendsto_standard
    hvariance_nonneg hlaw hvariance

end InfillGLSLean.ManuscriptSpecification.L053

end
