module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Residual-scale consistency from an L2 envelope

This module formalizes the last probabilistic step of a residual-scale
consistency proof.  A separate calculation may establish a deterministic L2
envelope for a residual-scale estimator (for example from Gaussian
quadratic-form moments).  The results below turn that envelope into
convergence in measure, represented in Mathlib by `TendstoInMeasure`.  When
the supplied measure is a probability measure, this is convergence in
probability.

The module intentionally does not claim the moment calculation itself, nor a
spatial asymptotic construction.  It is a reusable measure-theoretic bridge.
-/

public section

namespace InfillGLSLean

open Filter MeasureTheory Topology
open scoped ENNReal MeasureTheory Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- An explicit deterministic L2 envelope tending to zero forces the L2
seminorm to tend to zero. -/
theorem tendsto_eLpNorm_two_zero_of_bound
    {X : ℕ → Ω → ℝ} {bound : ℕ → ℝ≥0∞}
    (hbound : ∀ n, eLpNorm (X n) 2 μ ≤ bound n)
    (hbound_zero : Tendsto bound atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (X n) 2 μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hbound_zero ⊢
  intro ε hε
  filter_upwards [hbound_zero ε hε] with n hn
  exact (hbound n).trans hn

/-- The concrete order-two Chebyshev--Markov inequality for the error of a
residual-scale estimator.  It exposes the tail-probability control used by the
convergence theorem below. -/
theorem residualScale_tail_bound_L2
    {scale : ℝ} {S : ℕ → Ω → ℝ} (n : ℕ) (ε : ℝ) :
    (ENNReal.ofReal ε) ^ 2 * μ {ω | ε ≤ |S n ω - scale|} ≤
      eLpNorm (fun ω => S n ω - scale) 2 μ ^ 2 := by
  have hset :
      {ω | ε ≤ |S n ω - scale|} =
        {ω | ENNReal.ofReal ε ≤ ‖S n ω - scale‖ₑ} := by
    ext ω
    change (ε ≤ |S n ω - scale|) ↔ ENNReal.ofReal ε ≤ ‖S n ω - scale‖ₑ
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  rw [hset]
  simpa using
    (mul_meas_ge_le_pow_eLpNorm' (μ := μ) (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) (f := fun ω => S n ω - scale) (ENNReal.ofReal ε))

/-- If the L2 error of a real residual-scale estimator tends to zero, then the
estimator converges in measure to its deterministic target (and in probability
when `μ` is a probability measure).  Mathlib's
`tendstoInMeasure_of_tendsto_eLpNorm` supplies the Chebyshev--Markov step. -/
theorem residualScale_tendstoInMeasure_of_L2
    {scale : ℝ} {S : ℕ → Ω → ℝ}
    (hL2 : Tendsto (fun n => eLpNorm (fun ω => S n ω - scale) 2 μ) atTop (𝓝 0)) :
    TendstoInMeasure μ S atTop (fun _ => scale) := by
  refine tendstoInMeasure_of_tendsto_eLpNorm (μ := μ) (p := (2 : ℝ≥0∞)) (by norm_num) ?_
  change Tendsto (fun n => eLpNorm (fun ω => S n ω - scale) 2 μ) atTop (𝓝 0)
  exact hL2

/-- A deterministic L2 envelope is a directly usable hypothesis for
residual-scale consistency.  In an application, `bound n` may be the square
root of a separately proved second-moment bound. -/
theorem residualScale_tendstoInMeasure_of_L2_bound
    {scale : ℝ} {S : ℕ → Ω → ℝ} {bound : ℕ → ℝ≥0∞}
    (hbound : ∀ n, eLpNorm (fun ω => S n ω - scale) 2 μ ≤ bound n)
    (hbound_zero : Tendsto bound atTop (𝓝 0)) :
    TendstoInMeasure μ S atTop (fun _ => scale) :=
  residualScale_tendstoInMeasure_of_L2
    (tendsto_eLpNorm_two_zero_of_bound hbound hbound_zero)

end InfillGLSLean
