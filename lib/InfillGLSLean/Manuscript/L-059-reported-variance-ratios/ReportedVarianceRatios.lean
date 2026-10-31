module

public import «L-046-residual-scale-source».ResidualScaleBridge
public import «L-058-working-estimator-variance-limit».WorkingEstimatorVarianceLimit
import Mathlib.Tactic

/-!
# Reported-variance ratio bridges for Proposition `prop:variance`

This module proves only the two probability-limit comparisons stated in the
unchanged `varianceConclusion`.  It uses the literal reported variance,
accepted residual-scale consistency, and the accepted actual-variance limit.
It does not prove studentization or coverage.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L059

open Filter MeasureTheory ProbabilityTheory Topology

open InfillGLSLean.ManuscriptSpecification.L046
open InfillGLSLean.ManuscriptSpecification.L058

universe v

/-- Standard finite-dimensional probability calculus used privately below:
if a random numerator converges in measure to a positive constant and a
deterministic denominator converges to the same constant, then their ratio
converges in measure to one.  The proof makes the eventually-positive
denominator explicit. -/
private theorem tendstoInMeasure_div_deterministic_tendsto_const
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {X : Nat → Omega → Real} {denominator : Nat → Real}
    {c : Real} (hc : 0 < c)
    (hX : TendstoInMeasure P X atTop (fun _ => c))
    (hdenominator : Tendsto denominator atTop (nhds c)) :
    TendstoInMeasure P (fun n omega => X n omega / denominator n) atTop
      (fun _ => (1 : Real)) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro epsilon hepsilon
  have hquarter_pos : 0 < epsilon * c / 4 := by positivity
  have hXtail := hX (epsilon * c / 4) hquarter_pos
  have hdenominator_close : ∀ᶠ n in atTop,
      dist (denominator n) c < epsilon * c / 4 := by
    have hball := hdenominator.eventually
      (Metric.ball_mem_nhds c hquarter_pos)
    filter_upwards [hball] with n hn
    simpa only [Metric.mem_ball, dist_comm] using hn
  have hdenominator_lower : ∀ᶠ n in atTop, c / 2 < denominator n :=
    hdenominator.eventually_const_lt (by linarith)
  rw [ENNReal.tendsto_atTop_zero] at hXtail ⊢
  intro eta heta
  apply eventually_atTop.1
  filter_upwards [eventually_atTop.2 (hXtail eta heta), hdenominator_close,
    hdenominator_lower]
    with n hXmeasure hclose hlower
  exact (measure_mono (by
    intro omega homega
    by_contra hnot
    have hXclose : dist (X n omega) c < epsilon * c / 4 :=
      lt_of_not_ge hnot
    have hdenominator_pos : 0 < denominator n := by linarith
    have hsum : dist (X n omega) (denominator n) < epsilon * c / 2 := by
      calc
        dist (X n omega) (denominator n) ≤
            dist (X n omega) c + dist c (denominator n) :=
          dist_triangle _ _ _
        _ = dist (X n omega) c + dist (denominator n) c := by
          rw [dist_comm c]
        _ < epsilon * c / 4 + epsilon * c / 4 :=
          add_lt_add hXclose hclose
        _ = epsilon * c / 2 := by ring
    have hbound : epsilon * c / 2 < epsilon * denominator n := by
      calc
        epsilon * c / 2 = epsilon * (c / 2) := by ring
        _ < epsilon * denominator n :=
          mul_lt_mul_of_pos_left hlower hepsilon
    have hratio_lt : dist (X n omega) (denominator n) / denominator n < epsilon :=
      (div_lt_iff₀ hdenominator_pos).2 (hsum.trans hbound)
    have hratio_eq :
        dist (X n omega / denominator n) (1 : Real) =
          dist (X n omega) (denominator n) / denominator n := by
      rw [Real.dist_eq, Real.dist_eq]
      have hrewrite : X n omega / denominator n - 1 =
          (X n omega - denominator n) / denominator n := by
        field_simp [ne_of_gt hdenominator_pos]
      rw [hrewrite, abs_div, abs_of_pos hdenominator_pos]
    exact (not_lt_of_ge homega) (hratio_eq.trans_lt hratio_lt))).trans hXmeasure

/-- The reported variance divided by the paper's nominal
`sigma² / Q_n` variance converges in probability to one.  This uses the
literal `reportedVariance` definition and derives the eventual positivity of
`Q_n` from the existing information-divergence field. -/
theorem reportedVariance_div_sigmaSquared_div_information_tendstoInMeasure_one
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    TendstoInMeasure P
      (fun n omega => reportedVariance E n omega /
        (covariance.sigmaSquared / E.information n))
      atTop (fun _ => (1 : Real)) := by
  have hscale : TendstoInMeasure P (residualScale E) atTop
      (fun _ => covariance.sigmaSquared) :=
    residualScale_tendstoInMeasure E covariance mean
  have hratio : TendstoInMeasure P
      (fun n omega => residualScale E n omega / covariance.sigmaSquared)
      atTop (fun _ => (1 : Real)) :=
    tendstoInMeasure_div_deterministic_tendsto_const covariance.sigmaSquared_pos
      hscale tendsto_const_nhds
  apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hratio
  filter_upwards [E.information_tendsto.eventually
    (eventually_gt_atTop (0 : Real))] with n hinformation
  filter_upwards [] with omega
  rw [reportedVariance_eq]
  field_simp [hinformation.ne', covariance.sigmaSquared_pos.ne']

/-- The reported variance divided by the actual conditional variance of the
literal selected working-GLS slope converges in probability to one.  The
deterministic denominator limit is L058's exact working-estimator variance
comparison, not L-048's true-GLS variance. -/
theorem reportedVariance_div_varianceUnder_betaHat_tendstoInMeasure_one
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    TendstoInMeasure P
      (fun n omega => reportedVariance E n omega /
        varianceUnder P (E.betaHat n))
      atTop (fun _ => (1 : Real)) := by
  have hscale : TendstoInMeasure P (residualScale E) atTop
      (fun _ => covariance.sigmaSquared) :=
    residualScale_tendstoInMeasure E covariance mean
  have hnormalized : Tendsto
      (fun n => E.information n * varianceUnder P (E.betaHat n) /
        covariance.sigmaSquared)
      atTop (nhds 1) :=
    information_mul_varianceUnder_betaHat_div_sigmaSquared_tendsto_one E covariance
  have hactual : Tendsto
      (fun n => E.information n * varianceUnder P (E.betaHat n))
      atTop (nhds covariance.sigmaSquared) := by
    have hconstant : Tendsto (fun _ : Nat => covariance.sigmaSquared)
        atTop (nhds covariance.sigmaSquared) := tendsto_const_nhds
    have hscaled := hnormalized.mul hconstant
    convert hscaled using 1
    · funext n
      field_simp [covariance.sigmaSquared_pos.ne']
    · simp
  have hratio : TendstoInMeasure P
      (fun n omega => residualScale E n omega /
        (E.information n * varianceUnder P (E.betaHat n)))
      atTop (fun _ => (1 : Real)) :=
    tendstoInMeasure_div_deterministic_tendsto_const covariance.sigmaSquared_pos
      hscale hactual
  apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hratio
  filter_upwards [] with n
  filter_upwards [] with omega
  simp only [reportedVariance_eq, div_div]

end InfillGLSLean.ManuscriptSpecification.L059

end
