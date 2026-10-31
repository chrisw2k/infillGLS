module

public import ManuscriptSpecification
public import «L-047-mean-information-assembly».InformationAssembly
import «L-054-mean-bias-integration».MeanBiasIntegration
import Mathlib.Tactic

/-!
# Literal all-index endpoint for Appendix `lem:mean`

The paper's lemma is the all-index convergence of the working GLS outcome
weight against the literal regional conditional mean.  L-054 proves precisely
that expression on a finite reindexed tail.  This module transfers that
tail limit back to the unchanged all-index sequence; it adds no new
assumption, representer, or arbitrary-function generalization.

Manuscript source: `the source manuscript:519--604`.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L065

open Filter MeasureTheory ProbabilityTheory Topology
open InfillGLSLean.ManuscriptSpecification.L047
open InfillGLSLean.ManuscriptSpecification.L054

universe v

/-- Exact endpoint of Appendix `lem:mean`: under the four listed manuscript
assumptions, the literal working GLS outcome weights have a negligible
scaled conditional-mean contribution. -/
theorem conditionalMean_bias_tendsto
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    Tendsto (fun n =>
      Real.sqrt (E.information n) *
        (observedWorkingGLSOutcomeWeight E n ⬝ᵥ
          regionalConditionalMean E.maps P E.error n))
      atTop (nhds 0) := by
  rcases exists_reindexed_tendsto_sqrt_information_working_conditionalMean
      E covariance mean with ⟨start, htail⟩
  apply (tendsto_add_atTop_iff_nat start).mp
  simpa using htail

end InfillGLSLean.ManuscriptSpecification.L065

end
