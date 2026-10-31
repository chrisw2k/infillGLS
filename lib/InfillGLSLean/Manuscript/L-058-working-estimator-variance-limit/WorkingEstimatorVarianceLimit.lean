module

public import «L-057-working-estimator-variance».WorkingEstimatorVariance
public import «L-047-mean-information-assembly».InformationAssembly
public import InfillGLSLean.CovarianceSandwichLimit
import Mathlib.Tactic

/-!
# Actual conditional variance limit for the selected working-GLS slope

This module formalizes the deterministic comparison in the proof of
`prop:variance` at `the source manuscript:697--704`.  It combines the
accepted exact finite variance identity for the selected estimator with the
paper's literal working-row normalization and the stated covariance sandwich.
It does not use the proof-only true-GLS treatment variance.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L058

open Filter MeasureTheory ProbabilityTheory

open InfillGLSLean.ManuscriptSpecification.L047
open InfillGLSLean.ManuscriptSpecification.L057

universe v

/-- Under the manuscript's covariance assumption, the actual conditional
variance of the *selected working-GLS estimator* has the paper's exact
normalized limit.  This is the limit form of the displayed comparison in
`main.tex:699--703`; the finite equality to the literal working-row
quadratic form is supplied by L057. -/
theorem information_mul_varianceUnder_betaHat_div_sigmaSquared_tendsto_one
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E) :
    Tendsto
      (fun n => E.information n * varianceUnder P (E.betaHat n) /
        covariance.sigmaSquared)
      atTop (nhds 1) := by
  have hquadratic : Tendsto
      (fun n =>
        (E.information n * quadraticForm (trueCovariance E n)
          (observedWorkingGLSOutcomeWeight E n)) / covariance.sigmaSquared)
      atTop (nhds 1) := by
    apply varyingIndex_normalizedVariance_tendsto_one_of_eventually_covariance_sandwich
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
    · rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
      filter_upwards [eventually_ge_atTop rankStart] with n hn
      exact observedWorkingGLSOutcomeWeight_quadraticForm_eq_inv_information
        E n (hfull n hn)
  refine hquadratic.congr' ?_
  filter_upwards [eventually_varianceUnder_betaHat_eq_workingQuadraticForm
    E covariance] with n hn
  rw [hn]

end InfillGLSLean.ManuscriptSpecification.L058

end
