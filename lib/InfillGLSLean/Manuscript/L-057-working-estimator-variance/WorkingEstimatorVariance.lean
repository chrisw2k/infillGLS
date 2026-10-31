module

public import ManuscriptSpecification
public import «L-027-api-fwl-integration».FWLIntegration
public import «L-029-consistency-integration».Explore
public import «L-047-mean-information-assembly».InformationAssembly
public import «L-046-residual-scale-source».ScalarMomentBridge
public import InfillGLSLean.FiniteConditionalError
import Mathlib.Tactic

/-!
# Exact conditional variance of the selected working-GLS slope

This support module formalizes the finite variance identity used at
`the source manuscript:699--702`: on the existing full-rank/FWL tail, the
conditional variance of the literal selected working-GLS slope is the true
covariance quadratic form of the literal working outcome row.  It does not
use the proof-only true-GLS row or alter any main manuscript proposition.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L057

open Filter MeasureTheory ProbabilityTheory

open InfillGLSLean.ManuscriptSpecification.L047
open InfillGLSLean.ManuscriptSpecification.L046.ScalarMomentBridge

universe v

/-- At one resolution where the existing selected estimator has its FWL form,
the variance under the fixed conditional outcome law is exactly the true
covariance energy of the paper's literal *working* GLS outcome row.  The
covariance-start premise is used only to turn the already-public centered
Gaussian score variance into its real quadratic-form parameter. -/
theorem varianceUnder_betaHat_eq_workingQuadraticForm_of_full_rank_fwl
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (hstart : covariance.start ≤ n)
    (hfull : (regionalDesign mu E.maps E.treatment E.controls n).rank = E.q + 1)
    (hFWL : ∀ omega, E.betaHat n omega = fwlSlope E n omega) :
    varianceUnder P (E.betaHat n) =
      quadraticForm (trueCovariance E n) (observedWorkingGLSOutcomeWeight E n) := by
  let weight : Fin (E.maps.N n) → Real := observedWorkingGLSOutcomeWeight E n
  let rawError : Fin (E.maps.N n) → Omega → Real :=
    regionalRandomValues mu E.maps E.error n
  let mean : Fin (E.maps.N n) → Real := regionalConditionalMean E.maps P E.error n
  let score : Omega → Real := centeredRegionalScore E n weight
  let bias : Real := dotProduct weight mean
  have hraw : ∀ᵐ omega ∂P,
      E.betaHat n omega - E.beta = finiteWeightedScore weight rawError omega := by
    simpa only [weight, rawError, observedWorkingGLSOutcomeWeight_eq] using
      InfillGLSLean.ManuscriptSpecification.L029.slope_error_eq_weighted_regional_error
        E n hfull hFWL
  have hdecomposition : finiteWeightedScore weight rawError =
      fun omega => bias + score omega := by
    simpa only [bias, score, mean, rawError, weight, centeredRegionalScore,
      centeredRegionalError, dotProduct] using
      (finiteWeightedError_eq_bias_add_centeredScore weight rawError mean)
  have hbeta : ∀ᵐ omega ∂P,
      E.betaHat n omega = E.beta + bias + score omega := by
    filter_upwards [hraw] with omega homega
    calc
      E.betaHat n omega = E.beta + finiteWeightedScore weight rawError omega := by
        linarith
      _ = E.beta + bias + score omega := by
        rw [show finiteWeightedScore weight rawError omega = bias + score omega by
          exact congrFun hdecomposition omega]
        ring
  have hscore_mem : MemLp score 2 P :=
    (centeredRegionalScore_memLp_four E covariance n weight).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ (4 : ENNReal))
  have hvariance_congr :
      varianceUnder P (E.betaHat n) =
        varianceUnder P (fun omega => E.beta + bias + score omega) := by
    rw [varianceUnder_eq, varianceUnder_eq]
    have hmean : (∫ omega, E.betaHat n omega ∂P) =
        ∫ omega, (E.beta + bias + score omega) ∂P :=
      integral_congr_ae hbeta
    rw [hmean]
    apply integral_congr_ae
    filter_upwards [hbeta] with omega homega
    rw [homega]
  calc
    varianceUnder P (E.betaHat n) =
        varianceUnder P (fun omega => E.beta + bias + score omega) := hvariance_congr
    _ = Var[fun omega => E.beta + bias + score omega; P] := by
      rw [varianceUnder_eq, ← variance_eq_integral]
      exact ((memLp_const (E.beta + bias)).add hscore_mem).aemeasurable
    _ = Var[score; P] := by
      rw [variance_const_add hscore_mem.aestronglyMeasurable (E.beta + bias)]
    _ = quadraticForm (trueCovariance E n) weight :=
      centeredRegionalScore_variance E covariance n hstart weight
    _ = quadraticForm (trueCovariance E n) (observedWorkingGLSOutcomeWeight E n) := by
      rfl

/-- Eventual form of the exact finite working-estimator variance identity.
All three finite premises are already supplied by the experiment and source
covariance assumption, so this introduces no additional main assumption. -/
theorem eventually_varianceUnder_betaHat_eq_workingQuadraticForm
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E) :
    ∀ᶠ n in atTop,
      varianceUnder P (E.betaHat n) =
        quadraticForm (trueCovariance E n) (observedWorkingGLSOutcomeWeight E n) := by
  have hFWL : ∀ᶠ n in atTop, ∀ omega, E.betaHat n omega = fwlSlope E n omega :=
    (estimatorHasFWLForm_iff E).mp
      (InfillGLSLean.ManuscriptSpecification.L027.estimatorHasFWLForm_of_fixedLawHypotheses E)
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  filter_upwards [eventually_ge_atTop covariance.start,
    eventually_ge_atTop rankStart, hFWL] with n hnstart hnrank hnFWL
  exact varianceUnder_betaHat_eq_workingQuadraticForm_of_full_rank_fwl
    E covariance n hnstart (hfull n hnrank) hnFWL

end InfillGLSLean.ManuscriptSpecification.L057

end
