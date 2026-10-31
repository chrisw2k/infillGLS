module

public import «L-046-residual-scale-source».ResidualScaleBridge
public import «L-064-residual-scale-rate».StochasticOrder
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic

/-!
# Exact standard-order form of Appendix `lem:scale`

This module formalizes the displayed statement at
`the source manuscript:623` with the usual tail-probability meaning of
`O_p`.  It does not replace the rate by consistency: the literal source error
is decomposed pointwise into (i) the deterministic covariance-trace deviation,
which is `O(delta_n)`, and (ii) the literal residual-scale remainder, which is
`O_p(N_n^{-1/2})`.  The fixed-mean `C/(N_n-q-1)` contribution belongs to the
second component, as required when `delta_n` can be zero.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L064

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open scoped ENNReal MeasureTheory ProbabilityTheory Topology
open InfillGLSLean.ManuscriptSpecification.L046

universe v

/-- The deterministic covariance-trace component of the paper's residual
scale error. -/
noncomputable def residualScaleRateDeterministic
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} {P : Measure Omega}
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) : Real :=
  residualScaleTraceTerm E n - covariance.sigmaSquared

/-- The stochastic residual-scale component left after subtracting the
covariance-trace term.  It is the literal source statistic, not a replacement
or a sampled approximation. -/
noncomputable def residualScaleRateRemainder
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} {P : Measure Omega}
    (E : FixedConditionalExperiment mu P) (n : Nat) (omega : Omega) : Real :=
  residualScale E n omega - residualScaleTraceTerm E n

/-- The paper's deterministic interpretation of `N_n^{-1/2}`. -/
noncomputable def residualScaleNInvSqrt
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} {P : Measure Omega}
    (E : FixedConditionalExperiment mu P) (n : Nat) : Real :=
  (Real.sqrt ((E.maps.N n : Nat) : Real))⁻¹

/-- Pointwise literal decomposition of the source residual-scale error into
the deterministic trace deviation and stochastic remainder. -/
theorem residualScale_rate_pointwise_decomposition
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} {P : Measure Omega}
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (n : Nat) (omega : Omega) :
    residualScale E n omega - covariance.sigmaSquared =
      residualScaleRateDeterministic E covariance n +
        residualScaleRateRemainder E n omega := by
  simp only [residualScaleRateDeterministic, residualScaleRateRemainder]
  ring

/-- The covariance-trace component is exactly deterministic `O(delta_n)`.
Only the existing covariance sandwich, eventual full rank, and literal
positive-divisor tail are used. -/
theorem residualScaleRateDeterministic_isBigO
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E) :
    residualScaleRateDeterministic E covariance =O[atTop] covariance.delta := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * covariance.sigmaSquared, ?_⟩
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  have hstart : ∀ᶠ n in atTop, covariance.start ≤ n :=
    eventually_ge_atTop covariance.start
  have hNlarge : ∀ᶠ n in atTop, 2 * (E.q + 1) + 1 ≤ E.maps.N n :=
    E.maps.cell_count_tendsto.eventually
      (eventually_ge_atTop (2 * (E.q + 1) + 1))
  have hdivisor : ∀ᶠ n in atTop, E.q + 1 < E.maps.N n := by
    filter_upwards [hNlarge] with n hn
    omega
  have hdeltaSmall : ∀ᶠ n in atTop, covariance.delta n < (1 / 2 : Real) :=
    covariance.delta_tendsto_zero.eventually_lt_const (by norm_num)
  filter_upwards [hstart, eventually_ge_atTop nRank, hdivisor, hdeltaSmall]
    with n hnStart hnRank hnDivisor hnSmall
  rcases covariance.sandwich n hnStart with ⟨hnNonneg, hnLtOne, _, _⟩
  have hbounds := residualScaleTraceTerm_bounds E covariance n hnStart
    (hRank n hnRank) hnDivisor
  have hdenomUpper : 0 < 1 - covariance.delta n := by linarith
  have hdenomLower : 0 < 1 + covariance.delta n := by linarith
  have htraceNonneg : 0 ≤ residualScaleTraceTerm E n := by
    exact le_trans
      (div_nonneg covariance.sigmaSquared_pos.le (by linarith)) hbounds.1
  have htraceLeTwoSigma : residualScaleTraceTerm E n ≤ 2 * covariance.sigmaSquared := by
    calc
      residualScaleTraceTerm E n ≤ covariance.sigmaSquared / (1 - covariance.delta n) :=
        hbounds.2
      _ ≤ 2 * covariance.sigmaSquared := by
        apply (div_le_iff₀ hdenomUpper).2
        nlinarith [covariance.sigmaSquared_pos]
  have hupper : residualScaleTraceTerm E n - covariance.sigmaSquared ≤
      2 * covariance.sigmaSquared * covariance.delta n := by
    have hmult : residualScaleTraceTerm E n * (1 - covariance.delta n) ≤
        covariance.sigmaSquared := (le_div_iff₀ hdenomUpper).1 hbounds.2
    nlinarith [mul_nonneg htraceNonneg hnNonneg]
  have htraceLowerApprox : covariance.sigmaSquared * (1 - covariance.delta n) ≤
      residualScaleTraceTerm E n := by
    calc
      covariance.sigmaSquared * (1 - covariance.delta n) ≤
          covariance.sigmaSquared / (1 + covariance.delta n) := by
        apply (le_div_iff₀ hdenomLower).2
        nlinarith [covariance.sigmaSquared_pos, sq_nonneg (covariance.delta n)]
      _ ≤ residualScaleTraceTerm E n := hbounds.1
  have hlower : -(2 * covariance.sigmaSquared * covariance.delta n) ≤
      residualScaleTraceTerm E n - covariance.sigmaSquared := by
    nlinarith [covariance.sigmaSquared_pos, hnNonneg]
  change |residualScaleRateDeterministic E covariance n| ≤
    (2 * covariance.sigmaSquared) * |covariance.delta n|
  rw [abs_of_nonneg hnNonneg]
  exact abs_le.2 ⟨hlower, hupper⟩

/-- Elementary deterministic comparison between the literal residual degrees
of freedom and `N_n`.  It is used only after `N_n` has crossed the fixed
finite threshold determined by the fixed control dimension. -/
private theorem residual_divisor_geometry
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} {P : Measure Omega}
    (E : FixedConditionalExperiment mu P) (n : Nat)
    (hN : 2 * (E.q + 1) + 1 ≤ E.maps.N n) :
    0 < ((E.maps.N n : Nat) : Real) ∧
      1 ≤ ((E.maps.N n - E.q - 1 : Nat) : Real) ∧
      ((E.maps.N n : Nat) : Real) ≤
        2 * ((E.maps.N n - E.q - 1 : Nat) : Real) := by
  have hNpos : 0 < E.maps.N n := by omega
  have hdivisorNat : 1 ≤ E.maps.N n - E.q - 1 := by omega
  have hratioNat : E.maps.N n ≤ 2 * (E.maps.N n - E.q - 1) := by omega
  constructor
  · exact_mod_cast hNpos
  constructor
  · exact_mod_cast hdivisorNat
  · exact_mod_cast hratioNat

/-- The normalized literal residual-scale remainder has an eventually bounded
second moment.  This is the exact finite variance-plus-projected-mean bound
from Appendix `lem:scale`, with `N_n` compared to the unchanged residual
divisor only after a fixed deterministic tail. -/
private theorem normalized_residualScaleRateRemainder_eventually_moment_bound
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ K : Real, 0 ≤ K ∧
      ∀ᶠ n in atTop,
        MemLp (fun omega => Real.sqrt ((E.maps.N n : Nat) : Real) *
          residualScaleRateRemainder E n omega) 2 P ∧
        (∫ omega, (Real.sqrt ((E.maps.N n : Nat) : Real) *
          residualScaleRateRemainder E n omega) ^ 2 ∂P) ≤ K := by
  rcases mean.bounded_energy with ⟨C0, hC0⟩
  let C : Real := max C0 0
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have hC : ∀ n : Nat, meanEnergy E mean.c n ≤ C := by
    intro n
    exact (hC0 ⟨n, rfl⟩).trans (le_max_left _ _)
  let K : Real := 16 * covariance.sigmaSquared ^ 2 +
    16 * covariance.sigmaSquared * C + 2 * C ^ 2
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    have hcross : 0 ≤ covariance.sigmaSquared * C :=
      mul_nonneg covariance.sigmaSquared_pos.le hCnonneg
    nlinarith [sq_nonneg covariance.sigmaSquared, sq_nonneg C]
  refine ⟨K, hKnonneg, ?_⟩
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  have hstart : ∀ᶠ n in atTop, covariance.start ≤ n :=
    eventually_ge_atTop covariance.start
  have hrank : ∀ᶠ n in atTop,
      (regionalDesign mu E.maps E.treatment E.controls n).rank = E.q + 1 := by
    filter_upwards [eventually_ge_atTop nRank] with n hn
    exact hRank n hn
  have hNlarge : ∀ᶠ n in atTop, 2 * (E.q + 1) + 1 ≤ E.maps.N n :=
    E.maps.cell_count_tendsto.eventually
      (eventually_ge_atTop (2 * (E.q + 1) + 1))
  have hdivisor : ∀ᶠ n in atTop, E.q + 1 < E.maps.N n := by
    filter_upwards [hNlarge] with n hn
    omega
  have hdeltaHalf : ∀ᶠ n in atTop, covariance.delta n < (1 / 2 : Real) :=
    covariance.delta_tendsto_zero.eventually_lt_const (by norm_num)
  filter_upwards [hstart, hrank, hdivisor, hdeltaHalf, hNlarge]
    with n hnStart hnRank hnDivisor hnDelta hnN
  rcases residual_divisor_geometry E n hnN with ⟨hNpos, hdivisorOne, hNle⟩
  rcases covariance.sandwich n hnStart with ⟨hdeltaNonneg, hdeltaLtOne, _, _⟩
  let N : Real := ((E.maps.N n : Nat) : Real)
  let d : Real := ((E.maps.N n - E.q - 1 : Nat) : Real)
  let u : Real := covariance.sigmaSquared / (1 - covariance.delta n)
  have hN : 0 < N := by simpa [N] using hNpos
  have hdOne : 1 ≤ d := by simpa [d] using hdivisorOne
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hdOne
  have hNOverD : N * d⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hd).2 (by simpa [N, d] using hNle)
  have hdinvNonneg : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hdinvLeOne : d⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hd).2 hdOne
  have hNOverDSq : N * (d⁻¹) ^ 2 ≤ 2 := by
    calc
      N * (d⁻¹) ^ 2 = (N * d⁻¹) * d⁻¹ := by ring
      _ ≤ 2 * d⁻¹ := mul_le_mul_of_nonneg_right hNOverD hdinvNonneg
      _ ≤ 2 := by nlinarith
  have huNonneg : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg covariance.sigmaSquared_pos.le (by linarith)
  have huLe : u ≤ 2 * covariance.sigmaSquared := by
    dsimp [u]
    have hdenom : 0 < 1 - covariance.delta n := by linarith
    apply (div_le_iff₀ hdenom).2
    nlinarith [covariance.sigmaSquared_pos]
  have husqLe : u ^ 2 ≤ (2 * covariance.sigmaSquared) ^ 2 :=
    (sq_le_sq₀ huNonneg
      (mul_nonneg (by norm_num) covariance.sigmaSquared_pos.le)).2 huLe
  have hfirst : N * (2 * u ^ 2 * d⁻¹) ≤ 16 * covariance.sigmaSquared ^ 2 := by
    calc
      N * (2 * u ^ 2 * d⁻¹) = (2 * u ^ 2) * (N * d⁻¹) := by ring
      _ ≤ (2 * (2 * covariance.sigmaSquared) ^ 2) * (N * d⁻¹) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left husqLe (by norm_num)
        · exact mul_nonneg hN.le hdinvNonneg
      _ ≤ (2 * (2 * covariance.sigmaSquared) ^ 2) * 2 := by
        apply mul_le_mul_of_nonneg_left hNOverD
        positivity
      _ = 16 * covariance.sigmaSquared ^ 2 := by ring
  have hsecond : N * (4 * u * C * (d⁻¹) ^ 2) ≤
      16 * covariance.sigmaSquared * C := by
    have hcoefficient : 4 * u * C ≤ 4 * (2 * covariance.sigmaSquared) * C := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left huLe (by norm_num)
      · exact hCnonneg
    calc
      N * (4 * u * C * (d⁻¹) ^ 2) = (4 * u * C) * (N * (d⁻¹) ^ 2) := by ring
      _ ≤ (4 * (2 * covariance.sigmaSquared) * C) * (N * (d⁻¹) ^ 2) := by
        apply mul_le_mul_of_nonneg_right hcoefficient
        exact mul_nonneg hN.le (sq_nonneg _)
      _ ≤ (4 * (2 * covariance.sigmaSquared) * C) * 2 := by
        apply mul_le_mul_of_nonneg_left hNOverDSq
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (mul_nonneg (by norm_num) covariance.sigmaSquared_pos.le)) hCnonneg
      _ = 16 * covariance.sigmaSquared * C := by ring
  have hmeanNonneg : 0 ≤ residualScaleMeanTerm E n :=
    residualScaleMeanTerm_nonneg E n hnDivisor
  have hmeanLe : residualScaleMeanTerm E n ≤ C / d := by
    simpa [d] using residualScaleMeanTerm_le E mean n hnRank hnDivisor (hC n)
  have hCOverDNonneg : 0 ≤ C / d := div_nonneg hCnonneg hd.le
  have hmeanSqLe : (residualScaleMeanTerm E n) ^ 2 ≤ (C / d) ^ 2 :=
    (sq_le_sq₀ hmeanNonneg hCOverDNonneg).2 hmeanLe
  have hmeanTerm : N * (residualScaleMeanTerm E n) ^ 2 ≤ 2 * C ^ 2 := by
    calc
      N * (residualScaleMeanTerm E n) ^ 2 ≤ N * (C / d) ^ 2 :=
        mul_le_mul_of_nonneg_left hmeanSqLe hN.le
      _ = C ^ 2 * (N * (d⁻¹) ^ 2) := by
        field_simp [hd.ne']
      _ ≤ C ^ 2 * 2 := by
        apply mul_le_mul_of_nonneg_left hNOverDSq
        exact sq_nonneg C
      _ = 2 * C ^ 2 := by ring
  have hvariance := residualScale_variance_le_rate_envelope E covariance mean n
    hnStart hnRank hnDivisor (hC n)
  have hNvariance : N * Var[residualScale E n; P] ≤
      16 * covariance.sigmaSquared ^ 2 + 16 * covariance.sigmaSquared * C := by
    calc
      N * Var[residualScale E n; P] ≤ N *
          (2 * u ^ 2 * d⁻¹ + 4 * u * C * (d⁻¹) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [u, d] using hvariance
        · exact hN.le
      _ = N * (2 * u ^ 2 * d⁻¹) + N * (4 * u * C * (d⁻¹) ^ 2) := by ring
      _ ≤ 16 * covariance.sigmaSquared ^ 2 + 16 * covariance.sigmaSquared * C :=
        add_le_add hfirst hsecond
  have hmemResidual : MemLp (residualScale E n) 2 P :=
    residualScale_memLp_two_on_tail E covariance n hnRank hnDivisor
  have hmemNormalized : MemLp (fun omega => Real.sqrt N *
      residualScaleRateRemainder E n omega) 2 P := by
    have hsub := hmemResidual.sub (memLp_const (residualScaleTraceTerm E n))
    simpa [residualScaleRateRemainder] using hsub.const_mul (Real.sqrt N)
  constructor
  · simpa [N] using hmemNormalized
  · have hintegral := integral_sq_sub_const_eq_variance_add_bias_sq hmemResidual
      (residualScaleTraceTerm E n)
    have hmeanEq : (∫ omega, residualScale E n omega ∂P) -
        residualScaleTraceTerm E n = residualScaleMeanTerm E n := by
      rw [residualScale_integral_eq_traceTerm_add_meanTerm E covariance n hnStart hnRank
        hnDivisor]
      ring
    have hbase : (∫ omega,
        (residualScale E n omega - residualScaleTraceTerm E n) ^ 2 ∂P) =
        Var[residualScale E n; P] + (residualScaleMeanTerm E n) ^ 2 := by
      rw [hintegral, hmeanEq]
    have hnormalized : (∫ omega, (Real.sqrt N *
        residualScaleRateRemainder E n omega) ^ 2 ∂P) =
        N * (Var[residualScale E n; P] + (residualScaleMeanTerm E n) ^ 2) := by
      calc
        (∫ omega, (Real.sqrt N * residualScaleRateRemainder E n omega) ^ 2 ∂P) =
            ∫ omega, (Real.sqrt N) ^ 2 *
              (residualScale E n omega - residualScaleTraceTerm E n) ^ 2 ∂P := by
          congr 1
          funext omega
          simp only [residualScaleRateRemainder]
          ring
        _ = (Real.sqrt N) ^ 2 * (∫ omega,
            (residualScale E n omega - residualScaleTraceTerm E n) ^ 2 ∂P) := by
          rw [integral_const_mul]
        _ = N * (Var[residualScale E n; P] + (residualScaleMeanTerm E n) ^ 2) := by
          rw [Real.sq_sqrt hN.le, hbase]
    calc
      (∫ omega, (Real.sqrt ((E.maps.N n : Nat) : Real) *
          residualScaleRateRemainder E n omega) ^ 2 ∂P) =
          N * (Var[residualScale E n; P] + (residualScaleMeanTerm E n) ^ 2) := by
        simpa [N] using hnormalized
      _ ≤ (16 * covariance.sigmaSquared ^ 2 +
          16 * covariance.sigmaSquared * C) + 2 * C ^ 2 := by
        calc
          N * (Var[residualScale E n; P] + (residualScaleMeanTerm E n) ^ 2) =
              N * Var[residualScale E n; P] +
                N * (residualScaleMeanTerm E n) ^ 2 := by ring
          _ ≤ (16 * covariance.sigmaSquared ^ 2 +
              16 * covariance.sigmaSquared * C) + 2 * C ^ 2 :=
            add_le_add hNvariance hmeanTerm
      _ = K := by rfl

/-- The literal residual-scale remainder is standard
`O_p(N_n^{-1/2})`: after multiplication by `sqrt(N_n)`, it is bounded in
probability in the tail-probability sense defined in `StochasticOrder.lean`. -/
theorem residualScaleRateRemainder_isStochasticBigO
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    IsStochasticBigO P (residualScaleRateRemainder E)
      (residualScaleNInvSqrt E) := by
  rcases normalized_residualScaleRateRemainder_eventually_moment_bound E covariance mean
    with ⟨K, hK, htail⟩
  rw [isStochasticBigO_iff]
  simpa [residualScaleNInvSqrt] using
    (boundedInProbability_of_eventually_integral_sq_le (P := P) hK
      (by
        filter_upwards [htail] with n hn
        exact hn.1)
      (by
        filter_upwards [htail] with n hn
        exact hn.2))

/-- Exact formal rendering of the paper's displayed
`O(delta_n) + O_p(N_n^{-1/2})` statement.  The error is literally the sum of
the named deterministic trace deviation and named stochastic remainder;
the deterministic component uses Mathlib's `IsBigO`, while the stochastic
component uses the standard tail-probability definition documented above. -/
theorem residualScale_rate_decomposition
    {D : CompactEuclideanDomain} {Omega : Type v} [MeasurableSpace Omega]
    {mu : Measure (Point D)} [IsProbabilityMeasure mu]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment mu P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    (∀ n omega, residualScale E n omega - covariance.sigmaSquared =
      residualScaleRateDeterministic E covariance n +
        residualScaleRateRemainder E n omega) ∧
      residualScaleRateDeterministic E covariance =O[atTop] covariance.delta ∧
      IsStochasticBigO P (residualScaleRateRemainder E)
        (residualScaleNInvSqrt E) := by
  exact ⟨residualScale_rate_pointwise_decomposition E covariance,
    residualScaleRateDeterministic_isBigO E covariance,
    residualScaleRateRemainder_isStochasticBigO E covariance mean⟩

end InfillGLSLean.ManuscriptSpecification.L064

end
