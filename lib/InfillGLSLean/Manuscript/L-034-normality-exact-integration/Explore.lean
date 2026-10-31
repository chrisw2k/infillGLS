module

public import ManuscriptSpecification
import «L-025-api-fubini-integration».RegionalMeanCompatibility
import «L-027-api-fwl-integration».FWLIntegration
import «L-029-consistency-integration».Explore
public import InfillGLSLean.FiniteConditionalError
import InfillGLSLean
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
Exploration for the exact source-facing normality proof.  This file contains
only fully proved supporting lemmas; it does not restate or weaken the target.
-/

namespace InfillGLSLean.ManuscriptSpecification.L034

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

universe v

variable {D : CompactEuclideanDomain}
variable {Omega : Type v} [MeasurableSpace Omega]
variable {mu : Measure (Point D)} [IsProbabilityMeasure mu]
variable {P : Measure Omega} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
private theorem error_square_product_integrable
    (E : FixedConditionalExperiment mu P) :
    Integrable (fun z : Omega × Point D => E.error z.1 z.2 ^ 2) (P.prod mu) := by
  have hsq_measurable : Measurable
      (fun z : Omega × Point D => E.error z.1 z.2 ^ 2) :=
    E.error_jointly_measurable.pow measurable_const
  have hsq_ennreal_measurable : Measurable
      (fun z : Omega × Point D => ENNReal.ofReal (E.error z.1 z.2 ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp hsq_measurable
  have hsq_lintegral :
      (∫⁻ z : Omega × Point D, ENNReal.ofReal (E.error z.1 z.2 ^ 2) ∂(P.prod mu)) < ∞ := by
    rw [lintegral_prod _ hsq_ennreal_measurable.aemeasurable]
    exact E.conditional_error_second_moment
  exact
    (lintegral_ofReal_ne_top_iff_integrable hsq_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => sq_nonneg (E.error z.1 z.2))).mp
      hsq_lintegral.ne

private theorem error_product_integrable
    (E : FixedConditionalExperiment mu P) :
    Integrable (fun z : Omega × Point D => E.error z.1 z.2) (P.prod mu) := by
  have hmemLp : MemLp (fun z : Omega × Point D => E.error z.1 z.2) 2 (P.prod mu) :=
    (memLp_two_iff_integrable_sq E.error_jointly_measurable.aestronglyMeasurable).mpr
      (error_square_product_integrable E)
  exact hmemLp.integrable (by norm_num)

private theorem conditional_error_mean_integrable
    (E : FixedConditionalExperiment mu P) :
    Integrable (conditionalErrorMean P E.error) mu := by
  change Integrable (fun s => ∫ w, E.error w s ∂P) mu
  simpa using (error_product_integrable E).integral_prod_right

private theorem regional_error_integrableOn_ae
    (E : FixedConditionalExperiment mu P) (n : Nat) (i : Fin (E.maps.N n)) :
    ∀ᵐ w ∂P, IntegrableOn (E.error w) ((E.maps.partition n).cell i) mu := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  have hmeasure : P.prod (mu.restrict R) =
      (P.prod mu).restrict (Set.univ ×ˢ R) := by
    calc
      P.prod (mu.restrict R) = (P.restrict Set.univ).prod (mu.restrict R) := by
        rw [Measure.restrict_univ]
      _ = (P.prod mu).restrict (Set.univ ×ˢ R) := by
        rw [Measure.prod_restrict]
  have hrestrict : Integrable
      (fun z : Omega × Point D => E.error z.1 z.2) (P.prod (mu.restrict R)) := by
    rw [hmeasure]
    exact (error_product_integrable E).restrict
  simpa only [IntegrableOn, R] using
    (integrable_prod_iff E.error_jointly_measurable.aestronglyMeasurable).mp
      hrestrict |>.1

private theorem regional_error_integrable
    (E : FixedConditionalExperiment mu P) (n : Nat) (i : Fin (E.maps.N n)) :
    Integrable (regionalRandomValues mu E.maps E.error n i) P := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  have hmeasure : P.prod (mu.restrict R) =
      (P.prod mu).restrict (Set.univ ×ˢ R) := by
    calc
      P.prod (mu.restrict R) = (P.restrict Set.univ).prod (mu.restrict R) := by
        rw [Measure.restrict_univ]
      _ = (P.prod mu).restrict (Set.univ ×ˢ R) := by
        rw [Measure.prod_restrict]
  have hrestrict : Integrable
      (fun z : Omega × Point D => E.error z.1 z.2) (P.prod (mu.restrict R)) := by
    rw [hmeasure]
    exact (error_product_integrable E).restrict
  have hinterior : Integrable (fun w => ∫ s, E.error w s ∂(mu.restrict R)) P :=
    hrestrict.integral_prod_left
  change Integrable (fun w => ⨍ s in R, E.error w s ∂mu) P
  rw [show (fun w => ⨍ s in R, E.error w s ∂mu) =
      fun w => (mu.real R)⁻¹ • ∫ s, E.error w s ∂(mu.restrict R) by
        funext w
        rw [setAverage_eq]]
  exact hinterior.const_mul _

/-- The normalized indicator of one observed region, viewed as an `L2` test
function for the literal centered Gaussian-field assumption. -/
noncomputable def cellAverageTest
    (E : FixedConditionalExperiment mu P) (n : Nat) (i : Fin (E.maps.N n)) :
    L2TestFunction mu :=
  ⟨(E.maps.partition n).cell i |>.indicator
      (fun _ => (mu.real ((E.maps.partition n).cell i))⁻¹), by
    apply memLp_indicator_const 2
      ((E.maps.partition n).measurable_cell i).nullMeasurableSet
    right
    exact measure_ne_top mu ((E.maps.partition n).cell i)⟩

/-- The deterministic `L²` test function obtained by combining normalized
cell indicators with a finite vector of regional weights. -/
noncomputable def weightedCellTest
    (E : FixedConditionalExperiment mu P) (n : Nat)
    (weight : Fin (E.maps.N n) -> Real) : L2TestFunction mu :=
  ⟨fun s => ∑ i, weight i * (cellAverageTest E n i).1 s, by
    exact memLp_finsetSum Finset.univ fun i _ =>
      (cellAverageTest E n i).2.const_mul (weight i)⟩

example (E : FixedConditionalExperiment mu P) (n : Nat) (i : Fin (E.maps.N n)) :
    MemLp (cellAverageTest E n i).1 2 mu :=
  (cellAverageTest E n i).2

private theorem indicator_const_mul_eq_indicator
    (R : Set (Point D)) (a : Real) (g : Point D -> Real) :
    (fun s => R.indicator (fun _ => a) s * g s) =
      R.indicator (fun s => a * g s) := by
  funext s
  by_cases hs : s ∈ R <;> simp [hs]

/-- A single centered regional average is, almost everywhere, the literal
centered test integral for its normalized cell indicator. -/
private theorem centeredTestIntegral_cell_ae_eq
    (E : FixedConditionalExperiment mu P) (n : Nat) (i : Fin (E.maps.N n)) :
    centeredIntegralProcess mu P E.error (cellAverageTest E n i) =ᵐ[P]
      centeredFiniteError
        (regionalRandomValues mu E.maps E.error n)
        (regionalConditionalMean E.maps P E.error n) i := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  let a : Real := (mu.real R)⁻¹
  have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
  have hm : Integrable (conditionalErrorMean P E.error) (mu.restrict R) :=
    (conditional_error_mean_integrable E).restrict
  have hcompat := regionalMeanCompatibility_of_fixedLawHypotheses E n i
  filter_upwards [regional_error_integrableOn_ae E n i] with w hw
  have hsub : Integrable (fun s => E.error w s - conditionalErrorMean P E.error s)
      (mu.restrict R) := hw.sub hm
  rw [centeredIntegralProcess_apply, centeredTestIntegral_apply, centeredFiniteError_apply]
  change (∫ s, (cellAverageTest E n i).1 s *
      (E.error w s - conditionalErrorMean P E.error s) ∂mu) =
        regionalRandomValues mu E.maps E.error n i w -
          regionalConditionalMean E.maps P E.error n i
  change (∫ s, R.indicator (fun _ => a) s *
      (E.error w s - conditionalErrorMean P E.error s) ∂mu) =
        regionalRandomValues mu E.maps E.error n i w -
          regionalConditionalMean E.maps P E.error n i
  rw [indicator_const_mul_eq_indicator, integral_indicator hR]
  rw [integral_const_mul, integral_sub hw hm]
  rw [mul_sub]
  have hregional : regionalRandomValues mu E.maps E.error n i w =
      a * (∫ s in R, E.error w s ∂mu) := by
    simp [regionalRandomValues, cellMean, setAverage_eq, R, a, smul_eq_mul]
  rw [hregional]
  congr 1
  rw [← hcompat]
  simp [regionalMeanFromSpatialConditionalMean, regionalValues, cellMean,
    setAverage_eq, R, a, smul_eq_mul]

private theorem centered_regional_error_integral_eq_zero
    (E : FixedConditionalExperiment mu P) (n : Nat) (i : Fin (E.maps.N n)) :
    P[centeredFiniteError
      (regionalRandomValues mu E.maps E.error n)
      (regionalConditionalMean E.maps P E.error n) i] = 0 := by
  have hraw : Integrable (regionalRandomValues mu E.maps E.error n i) P :=
    regional_error_integrable E n i
  simp_rw [centeredFiniteError_apply]
  rw [integral_sub hraw (integrable_const _), integral_const]
  simp [regionalConditionalMean]

private theorem cell_centered_integrand_integrable_ae
    (E : FixedConditionalExperiment mu P) (n : Nat) (i : Fin (E.maps.N n)) :
    ∀ᵐ w ∂P, Integrable (fun s => (cellAverageTest E n i).1 s *
      (E.error w s - conditionalErrorMean P E.error s)) mu := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  let a : Real := (mu.real R)⁻¹
  have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
  have hm : Integrable (conditionalErrorMean P E.error) (mu.restrict R) :=
    (conditional_error_mean_integrable E).restrict
  filter_upwards [regional_error_integrableOn_ae E n i] with w hw
  have hsub : Integrable (fun s => E.error w s - conditionalErrorMean P E.error s)
      (mu.restrict R) := hw.sub hm
  change Integrable (fun s => R.indicator (fun _ => a) s *
    (E.error w s - conditionalErrorMean P E.error s)) mu
  rw [indicator_const_mul_eq_indicator, integrable_indicator_iff hR]
  exact hsub.const_mul _

/-- The centered integral for a finite weighted cell test is a.e. the
corresponding finite weighted centered regional score. -/
private theorem centeredTestIntegral_weighted_ae_eq_score
    (E : FixedConditionalExperiment mu P) (n : Nat)
    (weight : Fin (E.maps.N n) -> Real) :
    centeredIntegralProcess mu P E.error (weightedCellTest E n weight) =ᵐ[P]
      finiteWeightedScore weight
        (centeredFiniteError
          (regionalRandomValues mu E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n)) := by
  have hintegrable : ∀ᵐ w ∂P, ∀ i,
      Integrable (fun s => (cellAverageTest E n i).1 s *
        (E.error w s - conditionalErrorMean P E.error s)) mu :=
    ae_all_iff.2 fun i => cell_centered_integrand_integrable_ae E n i
  have hcell : ∀ᵐ w ∂P, ∀ i,
      centeredIntegralProcess mu P E.error (cellAverageTest E n i) w =
        centeredFiniteError
          (regionalRandomValues mu E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n) i w :=
    ae_all_iff.2 fun i => centeredTestIntegral_cell_ae_eq E n i
  filter_upwards [hintegrable, hcell] with w hInt hCell
  rw [centeredIntegralProcess_apply, centeredTestIntegral_apply]
  change (∫ s, (∑ i, weight i * (cellAverageTest E n i).1 s) *
      (E.error w s - conditionalErrorMean P E.error s) ∂mu) =
        finiteWeightedScore weight
          (centeredFiniteError
            (regionalRandomValues mu E.maps E.error n)
            (regionalConditionalMean E.maps P E.error n)) w
  have hsum : (fun s => (∑ i, weight i * (cellAverageTest E n i).1 s) *
      (E.error w s - conditionalErrorMean P E.error s)) =
      fun s => ∑ i, weight i * ((cellAverageTest E n i).1 s *
        (E.error w s - conditionalErrorMean P E.error s)) := by
    funext s
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, integral_finsetSum]
  · simp only [finiteWeightedScore_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    congr 1
    rw [← centeredTestIntegral_apply, ← centeredIntegralProcess_apply, hCell i]
  · intro i hi
    exact (hInt i).const_mul (weight i)

/-- The finite centered regional score is Gaussian under the paper's literal
Gaussian-field assumption.  Its mean and variance are identified separately
from the source covariance definition. -/
private theorem centered_regional_score_hasGaussianLaw
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (weight : Fin (E.maps.N n) -> Real) :
    HasGaussianLaw
      (finiteWeightedScore weight
        (centeredFiniteError
          (regionalRandomValues mu E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n))) P := by
  have htest : HasGaussianLaw
      (centeredIntegralProcess mu P E.error (weightedCellTest E n weight)) P :=
    covariance.centered_field_gaussian.hasGaussianLaw_eval (weightedCellTest E n weight)
  exact htest.congr (centeredTestIntegral_weighted_ae_eq_score E n weight)

private theorem centered_regional_error_memLp_two
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (i : Fin (E.maps.N n)) :
    MemLp (centeredFiniteError
      (regionalRandomValues mu E.maps E.error n)
      (regionalConditionalMean E.maps P E.error n) i) 2 P := by
  have htest : MemLp
      (centeredIntegralProcess mu P E.error (cellAverageTest E n i)) 2 P :=
    (covariance.centered_field_gaussian.hasGaussianLaw_eval (cellAverageTest E n i)).memLp_two
  exact htest.ae_eq (centeredTestIntegral_cell_ae_eq E n i)

private theorem centered_regional_error_covariance_eq_true
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    finiteErrorCovariance
      (centeredFiniteError (regionalRandomValues mu E.maps E.error n)
        (regionalConditionalMean E.maps P E.error n)) P = trueCovariance E n := by
  ext i j
  simp only [finiteErrorCovariance_apply, trueCovariance]
  change cov[(fun w => regionalRandomValues mu E.maps E.error n i w -
      regionalConditionalMean E.maps P E.error n i),
    (fun w => regionalRandomValues mu E.maps E.error n j w -
      regionalConditionalMean E.maps P E.error n j); P] =
    cov[regionalRandomValues mu E.maps E.error n i,
      regionalRandomValues mu E.maps E.error n j; P]
  rw [covariance_sub_const_left (regional_error_integrable E n i),
    covariance_sub_const_right (regional_error_integrable E n j)]

/- The scalar-law bridge below is reusable residual-scale infrastructure.
Opening this public boundary changes only the visibility of the already-proved
source-facing result; it adds no Gaussian, covariance, or manuscript premise. -/
public section

/-- Public exact source-to-scalar-Gaussian bridge for any deterministic finite
regional score.  This is a visibility-only export of the existing proof; it
does not alter the Gaussian-field assumption, covariance formula, or any
manuscript proposition. -/
theorem centered_regional_score_hasLaw
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (weight : Fin (E.maps.N n) -> Real) :
    HasLaw
      (finiteWeightedScore weight
        (centeredFiniteError
          (regionalRandomValues mu E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n)))
      (gaussianReal 0 (quadraticForm (trueCovariance E n) weight).toNNReal) P := by
  let centered := centeredFiniteError
    (regionalRandomValues mu E.maps E.error n)
    (regionalConditionalMean E.maps P E.error n)
  have hgaussian := centered_regional_score_hasGaussianLaw E covariance n weight
  have hmem : ∀ i, MemLp (centered i) 2 P := by
    intro i
    exact centered_regional_error_memLp_two E covariance n i
  have hcentered : ∀ i, P[centered i] = 0 := by
    intro i
    exact centered_regional_error_integral_eq_zero E n i
  have hmean : P[finiteWeightedScore weight centered] = 0 :=
    integral_finiteWeightedScore_eq_zero weight centered hmem hcentered
  have hvariance : Var[finiteWeightedScore weight centered; P] =
      quadraticForm (trueCovariance E n) weight := by
    rw [variance_finiteWeightedScore_eq_quadraticForm weight centered hmem,
      centered_regional_error_covariance_eq_true E n]
  refine ⟨hgaussian.aemeasurable, ?_⟩
  calc
    P.map (finiteWeightedScore weight centered) =
        gaussianReal P[finiteWeightedScore weight centered]
          Var[finiteWeightedScore weight centered; P].toNNReal :=
      hgaussian.map_eq_gaussianReal
    _ = gaussianReal 0 (quadraticForm (trueCovariance E n) weight).toNNReal := by
      rw [hmean, hvariance]

end

/-- The literal GLS outcome weight from the manuscript's `eq:weights`, kept
private here only to connect the exact FWL API to the centered Gaussian-score
bridge. -/
private noncomputable def outcomeWeight
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    Fin (E.maps.N n) -> Real :=
  glsOutcomeWeight (E.kernel n)
    (regionalControls mu E.maps E.controls n)
    (regionalValues mu E.maps E.treatment n)

omit [IsProbabilityMeasure mu] [IsProbabilityMeasure P] in
/-- At a source full-rank resolution, the literal GLS weight has the exact
working-covariance normalization `1 / Q_n`.  This is only the existing FWL
and finite weight algebra specialized to the manuscript objects. -/
private theorem outcomeWeight_quadraticForm_eq_inv_information
    (E : FixedConditionalExperiment mu P) (n : Nat)
    (hfull : (regionalDesign mu E.maps E.treatment E.controls n).rank = E.q + 1) :
    quadraticForm (E.kernel n) (outcomeWeight E n) = 1 / E.information n := by
  let controls := regionalControls mu E.maps E.controls n
  let treatment := regionalValues mu E.maps E.treatment n
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign treatment controls).rank = E.q + 1 := by
    change (InfillGLSLean.L023.sourceDesign
      (regionalValues mu E.maps E.treatment n)
      (regionalControls mu E.maps E.controls n)).rank = E.q + 1 at hfull
    exact hfull
  have hprecision : (E.kernel n)⁻¹ |>.PosDef := (E.kernel_posDef n).inv
  rcases InfillGLSLean.L023.sourceDesign_fwl_nonsingularity_and_relevance_of_full_rank
    treatment controls (E.kernel n)⁻¹ hprecision hfull_source with ⟨_, hresidual⟩
  have hinformation :
      E.information n = InfillGLSLean.controlInformation (E.kernel n)⁻¹ controls treatment :=
    InfillGLSLean.ManuscriptSpecification.L027.information_eq_controlInformation_of_full_rank
      E n hfull
  change quadraticForm (E.kernel n)
      (glsOutcomeWeight (E.kernel n)
        (regionalControls mu E.maps E.controls n)
        (regionalValues mu E.maps E.treatment n)) = 1 / E.information n
  rw [glsOutcomeWeight_quadraticForm_eq_inv_information (E.kernel n)
    (E.kernel_posDef n) controls treatment hresidual, hinformation]

omit [IsProbabilityMeasure mu] [IsProbabilityMeasure P] in
/-- Tail form of the exact GLS-weight normalization, obtained solely from the
literal eventual full-rank field of the fixed conditional experiment. -/
private theorem eventually_outcomeWeight_quadraticForm_eq_inv_information
    (E : FixedConditionalExperiment mu P) :
    ∀ᶠ n in atTop,
      quadraticForm (E.kernel n) (outcomeWeight E n) = 1 / E.information n := by
  rcases E.eventual_full_rank with ⟨n0, hfull⟩
  filter_upwards [eventually_ge_atTop n0] with n hn
  exact outcomeWeight_quadraticForm_eq_inv_information E n (hfull n hn)

omit [IsProbabilityMeasure mu] [IsProbabilityMeasure P] in
/-- The shrinking covariance sandwich gives the exact standardized variance
limit for the centered literal GLS score.  It uses no conditional-mean or
bias assertion. -/
private theorem centered_score_variance_ratio_tendsto_one
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E) :
    Tendsto (fun n =>
      (E.information n * quadraticForm (trueCovariance E n) (outcomeWeight E n)) /
        covariance.sigmaSquared) atTop (nhds 1) := by
  apply InfillGLSLean.varyingIndex_normalizedVariance_tendsto_one_of_eventually_covariance_sandwich
    covariance.sigmaSquared_pos
  · filter_upwards [eventually_ge_atTop covariance.start] with n hn
    exact (covariance.sandwich n hn).1
  · filter_upwards [eventually_ge_atTop covariance.start] with n hn
    exact (covariance.sandwich n hn).2.1
  · exact covariance.delta_tendsto_zero
  · exact E.information_tendsto.eventually (eventually_gt_atTop (0 : Real))
  · filter_upwards [eventually_ge_atTop covariance.start] with n hn
    exact (covariance.sandwich n hn).2.2.1
  · filter_upwards [eventually_ge_atTop covariance.start] with n hn
    exact (covariance.sandwich n hn).2.2.2
  · exact eventually_outcomeWeight_quadraticForm_eq_inv_information E

/-- On the literal full-rank/FWL tail, the selected estimator error is the
GLS-weighted raw regional error.  This consumes the already-proved exact L-029
translation API and introduces no replacement estimator. -/
private theorem eventually_slope_error_eq_raw_score
    (E : FixedConditionalExperiment mu P) :
    ∀ᶠ n in atTop, ∀ᵐ w ∂P,
      E.betaHat n w - E.beta =
        finiteWeightedScore (outcomeWeight E n)
          (regionalRandomValues mu E.maps E.error n) w := by
  have hFWL : ∀ᶠ n in atTop, ∀ w, E.betaHat n w = fwlSlope E n w :=
    (estimatorHasFWLForm_iff E).mp
      (InfillGLSLean.ManuscriptSpecification.L027.estimatorHasFWLForm_of_fixedLawHypotheses E)
  rcases E.eventual_full_rank with ⟨n0, hfull⟩
  filter_upwards [eventually_ge_atTop n0, hFWL] with n hn hFWL_n
  simpa only [outcomeWeight] using
    InfillGLSLean.ManuscriptSpecification.L029.slope_error_eq_weighted_regional_error
      E n (hfull n hn) hFWL_n

omit [IsProbabilityMeasure mu] [IsProbabilityMeasure P] in
/-- The exact finite raw-error decomposition for the literal GLS weights. -/
private theorem raw_score_eq_bias_add_centered_score
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    finiteWeightedScore (outcomeWeight E n)
        (regionalRandomValues mu E.maps E.error n) =
      fun w => dotProduct (outcomeWeight E n)
          (regionalConditionalMean E.maps P E.error n) +
        finiteWeightedScore (outcomeWeight E n)
          (centeredFiniteError
            (regionalRandomValues mu E.maps E.error n)
            (regionalConditionalMean E.maps P E.error n)) w := by
  simpa only [dotProduct] using
    finiteWeightedError_eq_bias_add_centeredScore (outcomeWeight E n)
      (regionalRandomValues mu E.maps E.error n)
      (regionalConditionalMean E.maps P E.error n)

/-- Combining the exact estimator/FWL translation with the finite conditional
error decomposition isolates precisely the deterministic bias term appearing
in Appendix `lem:mean`. -/
private theorem eventually_slope_error_eq_bias_add_centered_score
    (E : FixedConditionalExperiment mu P) :
    ∀ᶠ n in atTop, ∀ᵐ w ∂P,
      E.betaHat n w - E.beta =
        dotProduct (outcomeWeight E n)
          (regionalConditionalMean E.maps P E.error n) +
        finiteWeightedScore (outcomeWeight E n)
          (centeredFiniteError
            (regionalRandomValues mu E.maps E.error n)
            (regionalConditionalMean E.maps P E.error n)) w := by
  filter_upwards [eventually_slope_error_eq_raw_score E] with n hn
  filter_upwards [hn] with w hw
  calc
    E.betaHat n w - E.beta =
        finiteWeightedScore (outcomeWeight E n)
          (regionalRandomValues mu E.maps E.error n) w := hw
    _ = dotProduct (outcomeWeight E n)
          (regionalConditionalMean E.maps P E.error n) +
        finiteWeightedScore (outcomeWeight E n)
          (centeredFiniteError
            (regionalRandomValues mu E.maps E.error n)
            (regionalConditionalMean E.maps P E.error n)) w :=
      congrFun (raw_score_eq_bias_add_centered_score E n) w

example (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (i : Fin (E.maps.N n)) :
    HasGaussianLaw (centeredIntegralProcess mu P E.error (cellAverageTest E n i)) P :=
  covariance.centered_field_gaussian.hasGaussianLaw_eval (cellAverageTest E n i)

end InfillGLSLean.ManuscriptSpecification.L034
