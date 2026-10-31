module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

public section

/-!
# Abstract asymptotic core for infill GLS

This module captures two reusable implication steps in the manuscript's three
propositions, without claiming the spatial assumptions that construct their
hypotheses.

* A vanishing squared `L2` (mean-square) bound implies convergence in
  probability, with no artificial centering assumption.
* A distributional limit is preserved after multiplication by a scale that
  converges in probability to one and addition of a bias that converges in
  probability to zero.

The first statement is the final step of Proposition `prop:consistency`; the
second is the Slutsky step used in Proposition `prop:variance` after normality
and residual-scale consistency have been established.  Conditional,
matrix-covariance, Gaussian quadratic-form, and spatial-partition arguments
remain separate obligations.
-/

namespace InfillGLSLean

open Filter MeasureTheory Topology
open scoped ENNReal MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Extended-valued squared `L2` error.  Under a probability measure and a
finite second moment, this is the usual mean squared error. -/
noncomputable def quadraticL2Error (X : Ω → ℝ) (μ : Measure Ω) : ℝ≥0∞ :=
  eLpNorm X 2 μ ^ (2 : ℝ)

/-- For a real-valued finite-second-moment variable, `quadraticL2Error` is
exactly its squared-error integral, embedded into `ℝ≥0∞`.  Thus it is the
ordinary mean squared error whenever `μ` is a probability measure. -/
theorem quadraticL2Error_eq_ofReal_integral_sq
    {μ : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    quadraticL2Error X μ = ENNReal.ofReal (∫ ω, X ω ^ 2 ∂μ) := by
  unfold quadraticL2Error
  rw [hX.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (integral_nonneg (fun _ => sq_nonneg _)) _) 2]
  congr 1
  simpa using
    (Real.rpow_inv_natCast_pow (x := ∫ ω, X ω ^ 2 ∂μ) (n := 2)
      (integral_nonneg (fun _ => sq_nonneg _)) (by norm_num : (2 : ℕ) ≠ 0))

/-- If a nonnegative quadratic `L2` error is bounded by an envelope tending
to zero, then the quadratic error itself tends to zero. -/
theorem quadraticL2Error_tendsto_zero_of_bound
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {bound : ℕ → ℝ≥0∞}
    (hbound : ∀ n, quadraticL2Error (X n) μ ≤ bound n)
    (hbound_zero : Tendsto bound atTop (𝓝 0)) :
    Tendsto (fun n => quadraticL2Error (X n) μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hbound_zero ⊢
  intro ε hε
  filter_upwards [hbound_zero ε hε] with n hn
  exact (hbound n).trans hn

/-- A vanishing squared `L2` error has a vanishing `L2` norm. -/
theorem tendsto_eLpNorm_two_zero_of_tendsto_quadraticL2Error
    {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (herror : Tendsto (fun n => quadraticL2Error (X n) μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (X n) 2 μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at herror ⊢
  intro ε hε
  have hεpow : 0 < ε ^ (2 : ℝ) :=
    ENNReal.rpow_pos_of_nonneg hε (by norm_num)
  filter_upwards [herror (ε ^ (2 : ℝ)) hεpow] with n hn
  by_contra hnot
  have hlt : ε < eLpNorm (X n) 2 μ := lt_of_not_ge hnot
  have hpow := ENNReal.rpow_lt_rpow hlt (by norm_num : (0 : ℝ) < 2)
  exact (not_lt_of_ge hn) hpow

/-- The non-centred mean-square-to-probability implication.  This is the
final probabilistic step of the GLS consistency proposition once an exact MSE
bound has been supplied. -/
theorem tendstoInMeasure_zero_of_quadraticL2Error_bound
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {bound : ℕ → ℝ≥0∞}
    (hbound : ∀ n, quadraticL2Error (X n) μ ≤ bound n)
    (hbound_zero : Tendsto bound atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop (fun _ => 0) := by
  have hL2 : Tendsto (fun n => eLpNorm (X n) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_zero_of_tendsto_quadraticL2Error
      (quadraticL2Error_tendsto_zero_of_bound hbound hbound_zero)
  apply tendstoInMeasure_of_tendsto_eLpNorm (μ := μ) (p := (2 : ℝ≥0∞)) (by norm_num)
  have hsame :
      (fun n => eLpNorm (X n - fun _ : Ω => (0 : ℝ)) 2 μ) =
        fun n => eLpNorm (X n) 2 μ := by
    funext n
    congr
    funext ω
    simp
  rw [hsame]
  exact hL2

/-- The manuscript-facing non-centred MSE form of the consistency bridge.
The bound is imposed on the actual squared-error integral, not on a variance
around a separately assumed zero mean. -/
theorem tendstoInMeasure_zero_of_integral_sq_bound
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {bound : ℕ → ℝ≥0∞}
    (hX : ∀ n, MemLp (X n) 2 μ)
    (hbound : ∀ n, ENNReal.ofReal (∫ ω, (X n ω) ^ 2 ∂μ) ≤ bound n)
    (hbound_zero : Tendsto bound atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop (fun _ => 0) := by
  apply tendstoInMeasure_zero_of_quadraticL2Error_bound (bound := bound)
  intro n
  rw [quadraticL2Error_eq_ofReal_integral_sq (hX n)]
  exact hbound n
  exact hbound_zero

/-- An abstract version of the manuscript's MSE decomposition: a vanishing
variance term plus a vanishing squared-bias term yields consistency. -/
theorem gls_consistency_of_split_quadraticL2_bound
    {μ : Measure Ω} {estimationError : ℕ → Ω → ℝ}
    {varianceTerm biasTerm : ℕ → ℝ≥0∞}
    (hbound : ∀ n, quadraticL2Error (estimationError n) μ ≤ varianceTerm n + biasTerm n)
    (hvariance : Tendsto varianceTerm atTop (𝓝 0))
    (hbias : Tendsto biasTerm atTop (𝓝 0)) :
    TendstoInMeasure μ estimationError atTop (fun _ => 0) := by
  apply tendstoInMeasure_zero_of_quadraticL2Error_bound
    (bound := fun n => varianceTerm n + biasTerm n) hbound
  simpa using hvariance.add hbias

/-- Slutsky's multiplicative step: multiplication by a scale converging in
probability to one preserves a distributional limit. -/
theorem tendstoInDistribution_mul_of_tendstoInMeasure_one
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X scale : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) μ')
    (hscale : TendstoInMeasure μ scale atTop (fun _ => (1 : ℝ)))
    (hscale_meas : ∀ n, AEMeasurable (scale n) μ) :
    TendstoInDistribution (fun n ω => X n ω * scale n ω) atTop Z (fun _ => μ) μ' := by
  have h := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : ℝ × ℝ => z.1 * z.2) (by fun_prop) hscale hscale_meas
  simpa using h

/-- Slutsky's full scale-and-bias step.  This is applicable to the reported
GLS t statistic after a standardized normal limit, residual-scale consistency,
and negligible standardized bias are separately proved. -/
theorem tendstoInDistribution_scale_bias_of_standardized
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X scale bias : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) μ')
    (hscale : TendstoInMeasure μ scale atTop (fun _ => (1 : ℝ)))
    (hscale_meas : ∀ n, AEMeasurable (scale n) μ)
    (hbias : TendstoInMeasure μ bias atTop (fun _ => (0 : ℝ)))
    (hbias_meas : ∀ n, AEMeasurable (bias n) μ) :
    TendstoInDistribution (fun n ω => X n ω * scale n ω + bias n ω)
      atTop Z (fun _ => μ) μ' := by
  have hscaled :
      TendstoInDistribution (fun n ω => X n ω * scale n ω) atTop Z (fun _ => μ) μ' :=
    tendstoInDistribution_mul_of_tendstoInMeasure_one hX hscale hscale_meas
  have h := hscaled.add_of_tendstoInMeasure_const hbias hbias_meas
  refine h.congr ?_ ?_
  · intro n
    filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    simp

end InfillGLSLean
