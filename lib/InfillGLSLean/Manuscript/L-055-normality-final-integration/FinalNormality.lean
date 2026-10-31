module

public import ManuscriptSpecification
import InfillGLSLean
import Mathlib.Tactic
import «L-027-api-fwl-integration».FWLIntegration
import «L-029-consistency-integration».Explore
import «L-047-mean-information-assembly».InformationAssembly
import «L-053-centered-score-normality».CenteredScoreNormality
import «L-054-mean-bias-integration».MeanBiasIntegration

/-!
# Final source-faithful integration for Proposition `prop:normality`

This module proves the unchanged `manuscriptNormality` target from the two
already formalized parts of the paper's line-693 proof: the centered literal
working-score normal limit (L-053) and the literal working conditional-mean
bias limit (L-054).  The only finite bridge is the source's exact FWL/raw
error decomposition.  No true-GLS score replaces the working score, and no
assumption or formula of the proposition is changed.

Manuscript source: `the source manuscript:692--694`.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L055

open Filter MeasureTheory ProbabilityTheory Topology
open InfillGLSLean.ManuscriptSpecification.L047

universe v

/-- Reindex a distributional limit by a finite natural-number tail.  This is
private support for synchronizing existing paper-derived tails. -/
private theorem tendstoInDistribution_shift_nat
    {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {Z : ℝ → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => P) (gaussianReal 0 1))
    (start : ℕ) :
    TendstoInDistribution (fun n => X (n + start)) atTop Z
      (fun _ => P) (gaussianReal 0 1) := by
  refine ⟨?_, hX.aemeasurable_limit, ?_⟩
  · intro n
    exact hX.forall_aemeasurable (n + start)
  · convert hX.tendsto.comp (tendsto_add_atTop_nat start) using 1
    rfl

/-- Transfer a distributional limit of a finite tail back to the original
sequence.  The original all-index measurability is explicit, so no prefix is
silently discarded. -/
private theorem tendstoInDistribution_unshift_nat
    {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {Z : ℝ → ℝ}
    (hX_meas : ∀ n, AEMeasurable (X n) P)
    (start : ℕ)
    (hX : TendstoInDistribution (fun n => X (n + start)) atTop Z
      (fun _ => P) (gaussianReal 0 1)) :
    TendstoInDistribution X atTop Z (fun _ => P) (gaussianReal 0 1) := by
  refine ⟨hX_meas, hX.aemeasurable_limit, ?_⟩
  apply (tendsto_add_atTop_iff_nat start).mp
  simpa using hX.tendsto

/-- On the literal source full-rank/FWL tail, the selected estimator error is
exactly its working conditional mean plus its centered working error score.
This combines L-029's literal estimator/raw-error identity only with the
public finite error decomposition; it introduces no new estimator. -/
private theorem eventually_slope_error_eq_working_bias_add_centered_score
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) :
    ∀ᶠ n in atTop, ∀ᵐ ω ∂P,
      E.betaHat n ω - E.beta =
        dotProduct (observedWorkingGLSOutcomeWeight E n)
          (regionalConditionalMean E.maps P E.error n) +
        finiteWeightedScore (observedWorkingGLSOutcomeWeight E n)
          (centeredFiniteError
            (regionalRandomValues μ E.maps E.error n)
            (regionalConditionalMean E.maps P E.error n)) ω := by
  have hFWL : ∀ᶠ n in atTop, ∀ ω, E.betaHat n ω = fwlSlope E n ω :=
    (estimatorHasFWLForm_iff E).mp
      (InfillGLSLean.ManuscriptSpecification.L027.estimatorHasFWLForm_of_fixedLawHypotheses E)
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  filter_upwards [eventually_ge_atTop rankStart, hFWL] with n hnrank hnFWL
  have hraw := InfillGLSLean.ManuscriptSpecification.L029.slope_error_eq_weighted_regional_error
    E n (hfull n hnrank) hnFWL
  filter_upwards [hraw] with ω hω
  calc
    E.betaHat n ω - E.beta =
        finiteWeightedScore (observedWorkingGLSOutcomeWeight E n)
          (regionalRandomValues μ E.maps E.error n) ω := by
      simpa only [observedWorkingGLSOutcomeWeight_eq] using hω
    _ = dotProduct (observedWorkingGLSOutcomeWeight E n)
          (regionalConditionalMean E.maps P E.error n) +
        finiteWeightedScore (observedWorkingGLSOutcomeWeight E n)
          (centeredFiniteError
            (regionalRandomValues μ E.maps E.error n)
            (regionalConditionalMean E.maps P E.error n)) ω := by
      simpa only [dotProduct] using congrFun
        (finiteWeightedError_eq_bias_add_centeredScore
          (observedWorkingGLSOutcomeWeight E n)
          (regionalRandomValues μ E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n)) ω

/-- Private composition of the two exact source limits.  The hypotheses are
precisely the centered score and deterministic bias tails proved separately by
L-053 and L-054. -/
private theorem estimator_standardized_tendsto_standardNormal_of_reindexed_components
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (hcentered : ∃ start : ℕ,
      TendstoInDistribution
        (fun n ω =>
          (Real.sqrt (E.information (n + start)) /
            Real.sqrt covariance.sigmaSquared) *
            finiteWeightedScore (observedWorkingGLSOutcomeWeight E (n + start))
              (centeredFiniteError
                (regionalRandomValues μ E.maps E.error (n + start))
                (regionalConditionalMean E.maps P E.error (n + start))) ω)
        atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1))
    (hbias : ∃ start : ℕ,
      Tendsto
        (fun n => Real.sqrt (E.information (n + start)) *
          dotProduct (observedWorkingGLSOutcomeWeight E (n + start))
            (regionalConditionalMean E.maps P E.error (n + start)))
        atTop (nhds 0)) :
    TendstoInDistribution
      (fun n ω =>
        (Real.sqrt (E.information n) / Real.sqrt covariance.sigmaSquared) *
          (E.betaHat n ω - E.beta))
      atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1) := by
  rcases hcentered with ⟨centerStart, hcentered⟩
  rcases hbias with ⟨biasStart, hbias⟩
  rcases eventually_atTop.1
      (eventually_slope_error_eq_working_bias_add_centered_score E) with
    ⟨decompositionStart, hdecomposition⟩
  let start := centerStart + (biasStart + decompositionStart)
  have hcentered_common := tendstoInDistribution_shift_nat hcentered
    (biasStart + decompositionStart)
  have hcentered_at_start :
      TendstoInDistribution
        (fun n ω =>
          (Real.sqrt (E.information (n + start)) /
            Real.sqrt covariance.sigmaSquared) *
            finiteWeightedScore (observedWorkingGLSOutcomeWeight E (n + start))
              (centeredFiniteError
                (regionalRandomValues μ E.maps E.error (n + start))
                (regionalConditionalMean E.maps P E.error (n + start))) ω)
        atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1) := by
    refine hcentered_common.congr ?_ ?_
    · intro n
      filter_upwards [] with ω
      have hindex : (n + (biasStart + decompositionStart)) + centerStart =
          n + start := by
        dsimp [start]
        omega
      rw [hindex]
    · filter_upwards [] with z
      rfl
  have hbias_common := (tendsto_add_atTop_iff_nat (centerStart + decompositionStart)).mpr hbias
  have hbias_raw_at_start :
      Tendsto
        (fun n => Real.sqrt (E.information (n + start)) *
          dotProduct (observedWorkingGLSOutcomeWeight E (n + start))
            (regionalConditionalMean E.maps P E.error (n + start)))
        atTop (nhds 0) := by
    refine hbias_common.congr' (Filter.Eventually.of_forall fun n => ?_)
    have hindex : (n + (centerStart + decompositionStart)) + biasStart =
        n + start := by
      dsimp [start]
      omega
    rw [hindex]
  have hsigma : Real.sqrt covariance.sigmaSquared ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 covariance.sigmaSquared_pos)
  have hbias_at_start :
      Tendsto
        (fun n =>
          (Real.sqrt (E.information (n + start)) /
            Real.sqrt covariance.sigmaSquared) *
            dotProduct (observedWorkingGLSOutcomeWeight E (n + start))
              (regionalConditionalMean E.maps P E.error (n + start)))
        atTop (nhds 0) := by
    have hscaled := tendsto_const_nhds.mul hbias_raw_at_start
      (a := (Real.sqrt covariance.sigmaSquared)⁻¹)
    have hscaled_zero : Tendsto
        (fun n => (Real.sqrt covariance.sigmaSquared)⁻¹ *
          (Real.sqrt (E.information (n + start)) *
            dotProduct (observedWorkingGLSOutcomeWeight E (n + start))
              (regionalConditionalMean E.maps P E.error (n + start))))
        atTop (nhds 0) := by
      simpa using hscaled
    refine hscaled_zero.congr' (Filter.Eventually.of_forall fun n => ?_)
    field_simp [hsigma]
  have hbias_in_measure : TendstoInMeasure P
      (fun n (_ : Ω) =>
        (Real.sqrt (E.information (n + start)) /
          Real.sqrt covariance.sigmaSquared) *
          dotProduct (observedWorkingGLSOutcomeWeight E (n + start))
            (regionalConditionalMean E.maps P E.error (n + start)))
      atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact stronglyMeasurable_const.aestronglyMeasurable
    · filter_upwards [] with ω
      simpa using hbias_at_start
  have hbias_meas : ∀ n, AEMeasurable
      (fun _ : Ω =>
        (Real.sqrt (E.information (n + start)) /
          Real.sqrt covariance.sigmaSquared) *
          dotProduct (observedWorkingGLSOutcomeWeight E (n + start))
            (regionalConditionalMean E.maps P E.error (n + start))) P := by
    intro n
    exact stronglyMeasurable_const.aemeasurable
  have hadd := hcentered_at_start.add_of_tendstoInMeasure_const
    hbias_in_measure hbias_meas
  have hsum : TendstoInDistribution
      (fun n ω =>
        (Real.sqrt (E.information (n + start)) /
          Real.sqrt covariance.sigmaSquared) *
          finiteWeightedScore (observedWorkingGLSOutcomeWeight E (n + start))
            (centeredFiniteError
              (regionalRandomValues μ E.maps E.error (n + start))
              (regionalConditionalMean E.maps P E.error (n + start))) ω +
        (Real.sqrt (E.information (n + start)) /
          Real.sqrt covariance.sigmaSquared) *
          dotProduct (observedWorkingGLSOutcomeWeight E (n + start))
            (regionalConditionalMean E.maps P E.error (n + start)))
      atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1) := by
    refine hadd.congr ?_ ?_
    · intro n
      filter_upwards [] with ω
      rfl
    · filter_upwards [] with z
      simp
  have hstandardized_meas : ∀ n, AEMeasurable
      (fun ω =>
        (Real.sqrt (E.information n) / Real.sqrt covariance.sigmaSquared) *
          (E.betaHat n ω - E.beta)) P := by
    intro n
    exact ((E.betaHat_aemeasurable n).sub measurable_const.aemeasurable).const_mul _
  refine tendstoInDistribution_unshift_nat hstandardized_meas start ?_
  refine hsum.congr ?_ ?_
  · intro n
    have hnstart : decompositionStart ≤ n + start := by
      dsimp [start]
      omega
    filter_upwards [hdecomposition (n + start) hnstart] with ω hω
    rw [hω]
    ring
  · filter_upwards [] with z
    rfl

/-- Complete proof of the unchanged Proposition `prop:normality`.  The public
conclusion is literally `manuscriptNormality E`; the two source-facing
definitional expansion theorems are used only to enter and leave that existing
proposition. -/
theorem manuscriptNormality_complete
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) :
    manuscriptNormality E := by
  rw [manuscriptNormality_iff]
  intro covariance mean
  rw [normalityConclusion_iff]
  exact estimator_standardized_tendsto_standardNormal_of_reindexed_components
    E covariance
    (InfillGLSLean.ManuscriptSpecification.L053.exists_reindexed_centeredWorkingGLSScore_tendsto_standardNormal
      E covariance)
    (InfillGLSLean.ManuscriptSpecification.L054.exists_reindexed_tendsto_sqrt_information_working_conditionalMean
      E covariance mean)

end InfillGLSLean.ManuscriptSpecification.L055
