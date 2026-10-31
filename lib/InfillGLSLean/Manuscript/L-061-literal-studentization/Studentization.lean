module

public import ManuscriptSpecification
import InfillGLSLean
import Mathlib.Tactic
public import «L-046-residual-scale-source».ResidualScaleBridge
public import «L-055-normality-final-integration».FinalNormality

/-!
# Literal reported-variance studentization

This module is intentionally scoped to the fourth conjunct of the unchanged
`varianceConclusion`.  It will compose the accepted normality and literal
residual-scale endpoints without changing either the estimator or the
reported-variance formula.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L061

open Filter MeasureTheory ProbabilityTheory Topology
open InfillGLSLean.ManuscriptSpecification.L046
open InfillGLSLean.ManuscriptSpecification.L055

universe v

/-- A regional outcome average is a.e.-measurable at every finite resolution.
This is a direct Fubini consequence of the experiment's existing joint
outcome measurability field, not a new statistical assumption. -/
private theorem regionalOutcome_aemeasurable
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (n : Nat) (i : Fin (E.maps.N n)) :
    AEMeasurable (regionalRandomValues mu E.maps E.outcome n i) P := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  change AEMeasurable (fun omega => ⨍ s in R, E.outcome omega s ∂mu) P
  rw [show (fun omega => ⨍ s in R, E.outcome omega s ∂mu) =
      fun omega => (mu.real R)⁻¹ • ∫ s, E.outcome omega s ∂(mu.restrict R) by
        funext omega
        rw [setAverage_eq]]
  have hinterior : AEStronglyMeasurable
      (fun omega : Omega => ∫ s, E.outcome omega s ∂(mu.restrict R)) P :=
    E.outcome_jointly_measurable.aestronglyMeasurable.integral_prod_right'
  exact (hinterior.const_smul ((mu.real R)⁻¹)).aemeasurable

/-- The literal fitted-residual vector is a.e.-measurable at every index.
The proof retains the selected `betaHat` and `gammaHat` fields exactly and
uses only finite coordinate algebra after the regional Fubini step. -/
private theorem fittedResidual_aemeasurable
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    AEMeasurable (fittedResidual E n) P := by
  apply AEMeasurable.of_eval
  intro i
  change AEMeasurable (fun omega =>
    regionalRandomValues mu E.maps E.outcome n i omega -
      (E.betaHat n omega * regionalValues mu E.maps E.treatment n i) -
      ∑ j : Fin E.q, regionalControls mu E.maps E.controls n i j *
        E.gammaHat n omega j) P
  have houtcome : AEMeasurable
      (regionalRandomValues mu E.maps E.outcome n i) P :=
    regionalOutcome_aemeasurable E n i
  have hbeta : AEMeasurable (E.betaHat n) P := E.betaHat_aemeasurable n
  have hbeta_term : AEMeasurable (fun omega =>
      E.betaHat n omega * regionalValues mu E.maps E.treatment n i) P :=
    hbeta.mul measurable_const.aemeasurable
  have hcontrols : AEMeasurable (fun omega =>
      ∑ j : Fin E.q, regionalControls mu E.maps E.controls n i j *
        E.gammaHat n omega j) P := by
    rw [show (fun omega =>
        ∑ j : Fin E.q, regionalControls mu E.maps E.controls n i j *
          E.gammaHat n omega j) =
        ∑ j : Fin E.q, fun omega => regionalControls mu E.maps E.controls n i j *
          E.gammaHat n omega j by
            funext omega
            simp]
    apply Finset.aemeasurable_sum Finset.univ
    intro j _
    exact (E.gammaHat_aemeasurable n).eval j |>.const_mul _
  exact (houtcome.sub hbeta_term).sub hcontrols

/-- A fixed finite quadratic form of an a.e.-measurable real vector is
a.e.-measurable.  This is kept private because it is ordinary finite
measurability support rather than a manuscript theorem. -/
private theorem quadraticForm_aemeasurable
    {I : Type*} [Fintype I] [DecidableEq I]
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    (K : Matrix I I Real) (r : Omega → I → Real)
    (hr : AEMeasurable r P) :
    AEMeasurable (fun omega => quadraticForm K (r omega)) P := by
  simp only [quadraticForm_eq_dotProduct_mulVec]
  change AEMeasurable (fun omega =>
    ∑ i : I, r omega i * ∑ j : I, K i j * r omega j) P
  rw [show (fun omega => ∑ i : I, r omega i * ∑ j : I, K i j * r omega j) =
      ∑ i : I, fun omega => r omega i * ∑ j : I, K i j * r omega j by
        funext omega
        simp]
  apply Finset.aemeasurable_sum Finset.univ
  intro i _
  apply (hr.eval i).mul
  rw [show (fun omega => ∑ j : I, K i j * r omega j) =
      ∑ j : I, fun omega => K i j * r omega j by
        funext omega
        simp]
  apply Finset.aemeasurable_sum Finset.univ
  intro j _
  exact (hr.eval j).const_mul _

/-- The literal residual-scale statistic is a.e.-measurable at every index,
including its fixed early-prefix fallback branch. -/
private theorem residualScale_aemeasurable
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    AEMeasurable (residualScale E n) P := by
  unfold residualScale
  split_ifs with hdivisor
  · exact (quadraticForm_aemeasurable (E.kernel n)⁻¹ (fittedResidual E n)
      (fittedResidual_aemeasurable E n)).div measurable_const.aemeasurable
  · exact measurable_const.aemeasurable

/-- The unchanged reported variance is a.e.-measurable at every index. -/
private theorem reportedVariance_aemeasurable
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    AEMeasurable (reportedVariance E n) P := by
  have hreported : reportedVariance E n = fun omega =>
      residualScale E n omega / E.information n := by
    funext omega
    exact reportedVariance_eq E n omega
  rw [hreported]
  exact (residualScale_aemeasurable E n).div measurable_const.aemeasurable

/-- The exact literal studentized statistic is a.e.-measurable at every
index.  This matters when returning a reindexed tail limit to the all-index
source statistic. -/
private theorem studentized_aemeasurable
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (n : Nat) :
    AEMeasurable (fun omega =>
      (E.betaHat n omega - E.beta) /
        Real.sqrt (reportedVariance E n omega)) P := by
  exact ((E.betaHat_aemeasurable n).sub measurable_const.aemeasurable).div
    (reportedVariance_aemeasurable E n).sqrt

/-- A minimal continuous-mapping-in-measure bridge at a constant.  Pinned
Mathlib has no ready-made general theorem for this form, so the standard
epsilon--delta event containment is recorded privately here. -/
private theorem tendstoInMeasure_comp_continuousAt_const
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Nat -> Omega -> Real} {c : Real} {f : Real -> Real}
    (hX : TendstoInMeasure P X atTop (fun _ => c))
    (hf : ContinuousAt f c) :
    TendstoInMeasure P (fun n omega => f (X n omega)) atTop
      (fun _ => f c) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro epsilon hepsilon
  rcases (Metric.continuousAt_iff.mp hf epsilon hepsilon) with
    ⟨delta, hdelta_pos, hdelta⟩
  have hXtail := hX delta hdelta_pos
  rw [ENNReal.tendsto_atTop_zero] at hXtail ⊢
  intro eta heta
  apply eventually_atTop.1
  filter_upwards [eventually_atTop.2 (hXtail eta heta)] with n hn
  refine (measure_mono ?_).trans hn
  intro omega homega
  by_contra hnot
  have hclose : dist (X n omega) c < delta := lt_of_not_ge hnot
  exact (not_lt_of_ge homega) (hdelta hclose)

/-- The source's literal residual-scale consistency yields convergence in
probability of the exact square-root multiplier used by studentization.
Continuity is used only at the positive limiting variance, so no finite
zero-scale cancellation is assumed. -/
private theorem tendstoInMeasure_sqrt_div_sqrt_one
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    {S : Nat -> Omega -> Real} {c : Real} (hc : 0 < c)
    (hS : TendstoInMeasure P S atTop (fun _ => c)) :
    TendstoInMeasure P (fun n omega => Real.sqrt c / Real.sqrt (S n omega))
      atTop (fun _ => (1 : Real)) := by
  have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hcontinuous : ContinuousAt (fun x : Real =>
      Real.sqrt c / Real.sqrt x) c :=
    continuousAt_const.div Real.continuous_sqrt.continuousAt hsqrt_pos.ne'
  have h := tendstoInMeasure_comp_continuousAt_const hS hcontinuous
  have hvalue : Real.sqrt c / Real.sqrt c = (1 : Real) :=
    div_self hsqrt_pos.ne'
  simpa only [hvalue] using h

/-- Exact total-real algebra for the source statistic on a positive-
information tail.  The nonpositive-scale case is retained explicitly rather
than cancelling `sqrt s`; this is what makes the identity valid at every
sample point and permits the generic Slutsky interface. -/
private theorem literal_studentized_factorization
    (b s q c : Real) (hq : 0 < q) (hc : 0 < c) :
    b / Real.sqrt (s / q) =
      ((Real.sqrt q / Real.sqrt c) * b) *
        (Real.sqrt c / Real.sqrt s) := by
  by_cases hs : 0 < s
  · rw [Real.sqrt_div (le_of_lt hs)]
    have hqsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
    have hcsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
    have hssqrt : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    field_simp
  · have hsnonpos : s ≤ 0 := le_of_not_gt hs
    have hsdiv_nonpos : s / q ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hsnonpos (le_of_lt hq)
    rw [Real.sqrt_eq_zero_of_nonpos hsnonpos,
      Real.sqrt_eq_zero_of_nonpos hsdiv_nonpos]
    simp

/-- Extract the exact normalized selected-estimator limit already proved by
L-055, without changing its working-GLS normalization. -/
private theorem normalized_betaHat_tendsto_standardNormal
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    TendstoInDistribution
      (fun n omega =>
        (Real.sqrt (E.information n) / Real.sqrt covariance.sigmaSquared) *
          (E.betaHat n omega - E.beta))
      atTop (fun z : Real => z) (fun _ => P) (gaussianReal 0 1) := by
  have hnormal : manuscriptNormality E := manuscriptNormality_complete E
  rw [manuscriptNormality_iff] at hnormal
  have hconclusion : normalityConclusion E covariance mean := hnormal covariance mean
  rw [normalityConclusion_iff] at hconclusion
  exact hconclusion

/-- Reindex a standard-normal distributional limit by a finite tail. -/
private theorem tendstoInDistribution_shift_nat
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {X : Nat -> Omega -> Real} {Z : Real -> Real}
    (hX : TendstoInDistribution X atTop Z (fun _ => P) (gaussianReal 0 1))
    (start : Nat) :
    TendstoInDistribution (fun n => X (n + start)) atTop Z
      (fun _ => P) (gaussianReal 0 1) := by
  refine ⟨?_, hX.aemeasurable_limit, ?_⟩
  · intro n
    exact hX.forall_aemeasurable (n + start)
  · convert hX.tendsto.comp (tendsto_add_atTop_nat start) using 1
    rfl

/-- Transfer a finite-tail distributional limit back to the unchanged
all-index statistic, retaining the required all-index measurability proof. -/
private theorem tendstoInDistribution_unshift_nat
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {X : Nat -> Omega -> Real} {Z : Real -> Real}
    (hX_meas : forall n, AEMeasurable (X n) P) (start : Nat)
    (hX : TendstoInDistribution (fun n => X (n + start)) atTop Z
      (fun _ => P) (gaussianReal 0 1)) :
    TendstoInDistribution X atTop Z (fun _ => P) (gaussianReal 0 1) := by
  refine ⟨hX_meas, hX.aemeasurable_limit, ?_⟩
  apply (tendsto_add_atTop_iff_nat start).mp
  simpa using hX.tendsto

/-- The literal residual-scale multiplier is a.e.-measurable at every
index, including when its denominator is zero under total real division. -/
private theorem residualScale_multiplier_aemeasurable
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (c : Real) (n : Nat) :
    AEMeasurable (fun omega =>
      Real.sqrt c / Real.sqrt (residualScale E n omega)) P := by
  exact measurable_const.aemeasurable.div (residualScale_aemeasurable E n).sqrt

/-- Exact fourth-conjunct endpoint from `varianceConclusion`: the selected
working-GLS slope divided by the square root of the literal reported variance
converges in distribution to the standard normal law.  The finite prefix is
not redefined: it is retained through an explicit tail unshift. -/
theorem studentized_betaHat_tendsto_standardNormal
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    TendstoInDistribution
      (fun n omega =>
        (E.betaHat n omega - E.beta) /
          Real.sqrt (reportedVariance E n omega))
      atTop (fun z : Real => z) (fun _ => P) (gaussianReal 0 1) := by
  have hstandardized := normalized_betaHat_tendsto_standardNormal E covariance mean
  have hresidual_scale : TendstoInMeasure P (residualScale E) atTop
      (fun _ => covariance.sigmaSquared) :=
    residualScale_tendstoInMeasure E covariance mean
  have hmultiplier : TendstoInMeasure P
      (fun n omega => Real.sqrt covariance.sigmaSquared /
        Real.sqrt (residualScale E n omega))
      atTop (fun _ => (1 : Real)) :=
    tendstoInMeasure_sqrt_div_sqrt_one covariance.sigmaSquared_pos hresidual_scale
  have hinformation : ∀ᶠ n in atTop, 0 < E.information n :=
    E.information_tendsto.eventually (eventually_gt_atTop (0 : Real))
  rcases eventually_atTop.1 hinformation with ⟨start, hstart⟩
  have hstandardized_shift : TendstoInDistribution
      (fun n omega =>
        (Real.sqrt (E.information (n + start)) /
          Real.sqrt covariance.sigmaSquared) *
          (E.betaHat (n + start) omega - E.beta))
      atTop (fun z : Real => z) (fun _ => P) (gaussianReal 0 1) := by
    simpa only using tendstoInDistribution_shift_nat hstandardized start
  have hmultiplier_shift : TendstoInMeasure P
      (fun n omega => Real.sqrt covariance.sigmaSquared /
        Real.sqrt (residualScale E (n + start) omega))
      atTop (fun _ => (1 : Real)) := by
    convert hmultiplier.comp (tendsto_add_atTop_nat start) using 1
    rfl
  have hproduct : TendstoInDistribution
      (fun n omega =>
        ((Real.sqrt (E.information (n + start)) /
          Real.sqrt covariance.sigmaSquared) *
          (E.betaHat (n + start) omega - E.beta)) *
        (Real.sqrt covariance.sigmaSquared /
          Real.sqrt (residualScale E (n + start) omega)))
      atTop (fun z : Real => z) (fun _ => P) (gaussianReal 0 1) :=
    tendstoInDistribution_mul_of_tendstoInMeasure_one hstandardized_shift
      hmultiplier_shift
      (fun n => residualScale_multiplier_aemeasurable E covariance.sigmaSquared
        (n + start))
  refine tendstoInDistribution_unshift_nat
    (fun n => studentized_aemeasurable E n) start ?_
  refine hproduct.congr ?_ ?_
  · intro n
    filter_upwards [] with omega
    rw [reportedVariance_eq]
    exact (literal_studentized_factorization
      (E.betaHat (n + start) omega - E.beta)
      (residualScale E (n + start) omega)
      (E.information (n + start)) covariance.sigmaSquared
      (hstart (n + start) (Nat.le_add_left _ _)) covariance.sigmaSquared_pos).symm
  · filter_upwards [] with z
    rfl

end InfillGLSLean.ManuscriptSpecification.L061

end
