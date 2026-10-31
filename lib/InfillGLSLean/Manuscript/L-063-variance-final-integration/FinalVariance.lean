module

public import ManuscriptSpecification
import InfillGLSLean
import Mathlib.Tactic
public import «L-046-residual-scale-source».ResidualScaleBridge
public import «L-059-reported-variance-ratios».ReportedVarianceRatios
public import «L-061-literal-studentization».Studentization
public import «L-062-coverage-support».CoverageSupport

/-!
# Final source-faithful integration for Proposition `prop:variance`

This module proves the unchanged five-conjunct `manuscriptVariance` target.
It composes the literal residual-scale, selected-working-estimator variance,
reported-variance, studentization, and confidence-interval endpoints already
proved in their dedicated lanes. The final coverage transfer retains the
source's `ENNReal` probability target and original reported-variance interval.

Manuscript source: `the source manuscript:345--358` and `:697--704`.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L063

open Filter MeasureTheory ProbabilityTheory Topology
open InfillGLSLean.ManuscriptSpecification.L046
open InfillGLSLean.ManuscriptSpecification.L059
open InfillGLSLean.ManuscriptSpecification.L061
open InfillGLSLean.ManuscriptSpecification.L062

universe v

/-- The fifth unchanged variance conclusion follows from the literal
studentized normal limit. The only conversion is the accepted eventual-a.e.
equivalence between the manuscript's original reported-variance interval and
the studentized event; it is transferred with `measure_congr`, not replaced by
a pointwise or surrogate-variance interval. -/
private theorem confidenceCoverage_complete
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) (alpha : Real) (z : StandardNormalQuantile alpha) :
    confidenceCoverage E alpha z := by
  rw [confidenceCoverage_iff]
  have hstudentized := studentized_betaHat_tendsto_standardNormal E covariance mean
  have hidentity : HasLaw (fun x : Real => x) (gaussianReal 0 1)
      (gaussianReal 0 1) :=
    HasLaw.id
  have hstudentized_nnreal :
      Tendsto
        (fun n =>
          (P {omega |
            (E.betaHat n omega - E.beta) /
              Real.sqrt (reportedVariance E n omega) ∈
                Set.Icc (-z.value) z.value}).toNNReal)
        atTop (nhds (1 - alpha).toNNReal) := by
    exact InfillGLSLean.infillGLS_interval_event_coverage hstudentized hidentity
      (-z.value) z.value (sourceQuantile_neg_value_le z) (1 - alpha).toNNReal
      (sourceQuantile_interval_toNNReal z)
  have hstudentized_ennreal :
      Tendsto
        (fun n =>
          P {omega |
            (E.betaHat n omega - E.beta) /
              Real.sqrt (reportedVariance E n omega) ∈
                Set.Icc (-z.value) z.value})
        atTop (nhds (ENNReal.ofReal (1 - alpha))) :=
    tendsto_measure_ennreal_of_tendsto_toNNReal_ofReal hstudentized_nnreal
  have hinterval_ae :=
    eventually_ae_sourceConfidenceInterval_iff_studentizedInterval E covariance z
  refine hstudentized_ennreal.congr' ?_
  filter_upwards [hinterval_ae] with n hn
  apply measure_congr
  filter_upwards [hn] with omega homega
  exact propext homega.symm

/-- Complete proof of the unchanged Proposition `prop:variance`. Each field
is discharged by the corresponding source-faithful endpoint, and the public
`rfl` interfaces are used only to enter the existing proposition-shaped
definitions. -/
theorem manuscriptVariance_complete
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) :
    manuscriptVariance E := by
  rw [manuscriptVariance_iff]
  intro covariance mean
  rw [varianceConclusion_iff]
  refine ⟨residualScale_tendstoInMeasure E covariance mean,
    reportedVariance_div_varianceUnder_betaHat_tendstoInMeasure_one E covariance mean,
    reportedVariance_div_sigmaSquared_div_information_tendstoInMeasure_one E covariance mean,
    studentized_betaHat_tendsto_standardNormal E covariance mean, ?_⟩
  intro alpha z
  exact confidenceCoverage_complete E covariance mean alpha z

end InfillGLSLean.ManuscriptSpecification.L063

end
