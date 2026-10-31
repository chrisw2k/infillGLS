module

public import ManuscriptSpecification

public section

namespace InfillGLSLean.ManuscriptSpecification.L035

open Filter MeasureTheory ProbabilityTheory

universe u v

variable {D : CompactEuclideanDomain}
variable {Omega : Type v} [MeasurableSpace Omega]
variable {mu : Measure (Point D)} [IsProbabilityMeasure mu]
variable {P : Measure Omega} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure mu] [IsProbabilityMeasure P] in
/-- The paper's increasing number of cells makes the residual degrees of
freedom positive eventually.  This discharges only the `if` fallback in the
literal residual-scale definition; it adds no asymptotic condition. -/
theorem eventually_residual_divisor_positive (E : FixedConditionalExperiment mu P) :
    Filter.Eventually (fun n => E.q + 1 < E.maps.N n) atTop :=
  E.maps.cell_count_tendsto.eventually (eventually_gt_atTop (E.q + 1))

end InfillGLSLean.ManuscriptSpecification.L035
