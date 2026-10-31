module

public import InfillGLSLean.Coverage
public import «L-033-normal-cdf-calibration».SourceQuantileBridge
public import «L-046-residual-scale-source».ResidualScaleBridge
import Mathlib.Tactic

/-!
# Literal coverage support for Proposition `prop:variance`

This module supplies only the finite/tail event algebra and probability
codomain bookkeeping needed by the fifth unchanged `varianceConclusion`
conjunct.  It does not assume a studentized normal limit and does not enter
or alter `confidenceCoverage` or `manuscriptVariance`.

Manuscript source: `the source manuscript:345--358` and `:697--704`.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L062

open Filter MeasureTheory ProbabilityTheory Topology

universe v

/-- The source quantile's two-sided interval cannot be empty: the existing
L-033 calibration and `alpha < 1` imply the ordering required by the
closed-interval coverage API.  This is derived from, rather than added to,
`StandardNormalQuantile`. -/
theorem sourceQuantile_neg_value_le {alpha : Real}
    (z : StandardNormalQuantile alpha) :
    -z.value <= z.value := by
  by_contra hnot
  have hlt : z.value < -z.value := lt_of_not_ge hnot
  have hempty :
      (gaussianReal 0 1 (Set.Icc (-z.value) z.value)).toNNReal = 0 := by
    simp [Set.Icc_eq_empty_of_lt hlt]
  have hcalibration :=
    InfillGLSLean.ManuscriptSpecification.L033.sourceQuantile_interval_toNNReal z
  have hpositive : 0 < (1 - alpha).toNNReal := by
    exact Real.toNNReal_pos.mpr (by linarith [z.alpha_lt_one])
  exact (ne_of_gt hpositive) (hcalibration.symm.trans hempty)

/-- Re-export the exact L-033 two-sided calibration next to the interval-order
bridge.  It introduces no new quantile premise or numerical assertion. -/
theorem sourceQuantile_interval_toNNReal {alpha : Real}
    (z : StandardNormalQuantile alpha) :
    (gaussianReal 0 1 (Set.Icc (-z.value) z.value)).toNNReal =
      (1 - alpha).toNNReal :=
  InfillGLSLean.ManuscriptSpecification.L033.sourceQuantile_interval_toNNReal z

/-- Finite ordered-field equivalence between the literal symmetric confidence
interval and the standardized closed interval, valid when the reported
variance is strictly positive. -/
private theorem confidenceInterval_mem_iff_studentized_mem
    (beta betaHat z variance : Real) (hvariance : 0 < variance) :
    beta ∈ Set.Icc
      (betaHat - z * Real.sqrt variance)
      (betaHat + z * Real.sqrt variance) <->
    (betaHat - beta) / Real.sqrt variance ∈ Set.Icc (-z) z := by
  have hsqrt : 0 < Real.sqrt variance := Real.sqrt_pos.2 hvariance
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [le_div_iff₀ hsqrt]
      nlinarith
    · rw [div_le_iff₀ hsqrt]
      nlinarith
  · rintro ⟨hlower, hupper⟩
    constructor
    · have hupper' : betaHat - beta <= z * Real.sqrt variance :=
        (div_le_iff₀ hsqrt).mp hupper
      nlinarith
    · have hlower' : -z * Real.sqrt variance <= betaHat - beta :=
        (le_div_iff₀ hsqrt).mp hlower
      nlinarith

/-- On the existing positive-information and a.s.-positive residual-scale
tail, the literal confidence interval in `confidenceCoverage` is equivalent
almost everywhere to the studentized `[-z,z]` event.  The reported variance,
not a replacement variance, remains in both expressions. -/
theorem eventually_ae_sourceConfidenceInterval_iff_studentizedInterval
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    {alpha : Real} (z : StandardNormalQuantile alpha) :
    ∀ᶠ n in atTop, ∀ᵐ omega ∂P,
      (E.beta ∈ Set.Icc
        (E.betaHat n omega - z.value * Real.sqrt (reportedVariance E n omega))
        (E.betaHat n omega + z.value * Real.sqrt (reportedVariance E n omega))) <->
      ((E.betaHat n omega - E.beta) /
        Real.sqrt (reportedVariance E n omega) ∈ Set.Icc (-z.value) z.value) := by
  have hscale :=
    InfillGLSLean.ManuscriptSpecification.L046.eventually_ae_residualScale_pos
      E covariance
  have hinformation : ∀ᶠ n in atTop, 0 < E.information n :=
    E.information_tendsto.eventually (eventually_gt_atTop (0 : Real))
  filter_upwards [hscale, hinformation] with n hscale_n hinformation_n
  filter_upwards [hscale_n] with omega hscale_omega
  apply confidenceInterval_mem_iff_studentized_mem
  rw [reportedVariance_eq]
  exact div_pos hscale_omega hinformation_n

/-- A finite probability measure can be recovered from the `NNReal` values
used by `Coverage.lean`: convergence of event probabilities after `toNNReal`
implies convergence in the source's literal `ENNReal` codomain. -/
theorem tendsto_measure_ennreal_of_tendsto_toNNReal
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {A : Nat -> Set Omega} {q : NNReal}
    (h : Tendsto (fun n => (P (A n)).toNNReal) atTop (nhds q)) :
    Tendsto (fun n => P (A n)) atTop (nhds (q : ENNReal)) := by
  have hreal : Tendsto (fun n => ((P (A n)).toNNReal : Real)) atTop
      (nhds (q : Real)) :=
    (NNReal.continuous_coe.tendsto q).comp h
  have hennreal : Tendsto
      (fun n => ENNReal.ofReal ((P (A n)).toNNReal : Real)) atTop
      (nhds (ENNReal.ofReal (q : Real))) :=
    (ENNReal.continuous_ofReal.tendsto (q : Real)).comp hreal
  have hcoe : Tendsto (fun n => ((P (A n)).toNNReal : ENNReal)) atTop
      (nhds (q : ENNReal)) := by
    simpa using hennreal
  refine hcoe.congr' ?_
  filter_upwards [] with n
  exact ENNReal.coe_toNNReal (measure_ne_top P (A n))

/-- The preceding bridge with the exact `ENNReal.ofReal r` target used by
the source, when the supplied real nominal coverage level is nonnegative. -/
theorem tendsto_measure_ennreal_of_tendsto_toNNReal_ofReal
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {A : Nat -> Set Omega} {r : Real}
    (h : Tendsto (fun n => (P (A n)).toNNReal) atTop (nhds r.toNNReal)) :
    Tendsto (fun n => P (A n)) atTop (nhds (ENNReal.ofReal r)) := by
  have hbase := tendsto_measure_ennreal_of_tendsto_toNNReal h
  simpa [ENNReal.ofReal] using hbase

end InfillGLSLean.ManuscriptSpecification.L062

end
