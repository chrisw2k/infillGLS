module

public import InfillGLSLean.InfillPropositions
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.Order.DenselyOrdered

public section

/-!
# Confidence-interval coverage from a standard-normal limit

This module formalizes the final Portmanteau step in the manuscript's
confidence-interval conclusion.  A standardized statistic converging in
distribution to a nondegenerate standard Gaussian has convergent closed
interval probabilities because the Gaussian assigns zero mass to interval
boundaries.  The numerical normal-quantile calibration is intentionally an
explicit hypothesis: it is a separate analytic fact from distributional
convergence.
-/

namespace InfillGLSLean

open Filter MeasureTheory ProbabilityTheory Topology

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The law of a statistic with a standard-normal distributional limit assigns
asymptotically the standard-normal probability to every closed interval. -/
theorem infillGLS_interval_law_coverage
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {statistic : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hstatistic : TendstoInDistribution statistic atTop Z (fun _ => μ) μ')
    (hZ : HasLaw Z (gaussianReal 0 1) μ')
    (lower upper : ℝ) (hinterval : lower ≤ upper) :
    Tendsto (fun n => ((μ.map (statistic n)) (Set.Icc lower upper)).toNNReal) atTop
      (𝓝 (((gaussianReal 0 1) (Set.Icc lower upper)).toNNReal)) := by
  let _ : NullSingletonClass (gaussianReal 0 (1 : NNReal)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hfrontier :
      (gaussianReal 0 (1 : NNReal)) (frontier (Set.Icc lower upper)) = 0 := by
    rw [frontier_Icc hinterval]
    exact ((Set.finite_singleton upper).insert lower).measure_zero _
  have hfrontierZ : (μ'.map Z) (frontier (Set.Icc lower upper)) = 0 := by
    rw [hZ.map_eq]
    exact hfrontier
  have hfrontierP :
      ((μ'.map Z) (frontier (Set.Icc lower upper))).toNNReal = 0 := by
    rw [hfrontierZ]
    rfl
  have hmaps := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (E := Set.Icc lower upper) hstatistic.tendsto hfrontierP
  simpa [hZ.map_eq] using hmaps

/-- If the standard-normal mass of an interval is the supplied nominal level,
the interval coverage probability converges to that nominal level. -/
theorem infillGLS_interval_coverage
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {statistic : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hstatistic : TendstoInDistribution statistic atTop Z (fun _ => μ) μ')
    (hZ : HasLaw Z (gaussianReal 0 1) μ')
    (lower upper : ℝ) (hinterval : lower ≤ upper) (nominal : NNReal)
    (hcalibration : ((gaussianReal 0 1) (Set.Icc lower upper)).toNNReal = nominal) :
    Tendsto (fun n => ((μ.map (statistic n)) (Set.Icc lower upper)).toNNReal) atTop
      (𝓝 nominal) := by
  simpa [hcalibration] using
    infillGLS_interval_law_coverage hstatistic hZ lower upper hinterval

/-- The same coverage conclusion expressed as probabilities of the original
statistic falling in the interval, rather than probabilities under its law. -/
theorem infillGLS_interval_event_coverage
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {statistic : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hstatistic : TendstoInDistribution statistic atTop Z (fun _ => μ) μ')
    (hZ : HasLaw Z (gaussianReal 0 1) μ')
    (lower upper : ℝ) (hinterval : lower ≤ upper) (nominal : NNReal)
    (hcalibration : ((gaussianReal 0 1) (Set.Icc lower upper)).toNNReal = nominal) :
    Tendsto (fun n => (μ {ω | statistic n ω ∈ Set.Icc lower upper}).toNNReal) atTop
      (𝓝 nominal) := by
  have hlaw := infillGLS_interval_coverage hstatistic hZ lower upper hinterval nominal hcalibration
  have hevent :
      (fun n => (μ {ω | statistic n ω ∈ Set.Icc lower upper}).toNNReal) =
        fun n => ((μ.map (statistic n)) (Set.Icc lower upper)).toNNReal := by
    funext n
    rw [Measure.map_apply_of_aemeasurable (hstatistic.forall_aemeasurable n)
      measurableSet_Icc]
    rfl
  rw [hevent]
  exact hlaw

end InfillGLSLean
