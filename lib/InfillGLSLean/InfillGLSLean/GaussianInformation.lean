module

public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Distributions.Gaussian.Real

public section

/-!
# Gaussian innovation information growth

This module verifies the independent-innovation core of the manuscript's
Gaussian information example.  For pairwise independent, identically
distributed standard-Gaussian innovations, the normalized sum of squares
converges almost surely to one.  The paper's full example additionally
constructs those innovations from nested regional measurement spaces and
shows that profiling controls removes only a bounded term; those spatial and
matrix bridges are deliberately not claimed here.
-/

namespace InfillGLSLean

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ProbabilityTheory Function

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Independent standard-Gaussian innovations have average squared magnitude
converging almost surely to one. -/
theorem gaussianInnovation_information_ae
    {innovation : ℕ → Ω → ℝ}
    (hzero : HasLaw (innovation 0) (gaussianReal 0 1) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on innovation))
    (hident : ∀ i, IdentDistrib (innovation i) (innovation 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, (innovation i ω) ^ 2) / n)
      atTop (𝓝 1) := by
  let squared : ℕ → Ω → ℝ := fun i ω => (innovation i ω) ^ 2
  have hmem : MemLp (innovation 0) 2 μ :=
    hzero.memLp (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) 2)
  have hint : Integrable (squared 0) μ := by
    simpa [squared] using hmem.integrable_sq
  have hindep_sq : Pairwise ((· ⟂ᵢ[μ] ·) on squared) := by
    intro i j hij
    exact (hindep hij).comp (measurable_id'.pow_const 2) (measurable_id'.pow_const 2)
  have hident_sq : ∀ i, IdentDistrib (squared i) (squared 0) μ μ := by
    intro i
    exact (hident i).comp (measurable_id'.pow_const 2)
  have hgaussian_mean :
      (∫ x : ℝ, x ∂(gaussianReal 0 (1 : NNReal))) = 0 := by
    exact integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  have hgaussian_variance :
      Var[id; gaussianReal 0 (1 : NNReal)] =
        ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (1 : NNReal)) := by
    have hraw := variance_of_integral_eq_zero (X := id) aemeasurable_id hgaussian_mean
    simpa only [id_eq] using hraw
  have hmean_sq : (∫ x, x ^ 2 ∂(gaussianReal 0 (1 : NNReal))) = 1 := by
    calc
      ∫ x, x ^ 2 ∂(gaussianReal 0 (1 : NNReal)) =
          Var[id; gaussianReal 0 (1 : NNReal)] := hgaussian_variance.symm
      _ = 1 := by simp [variance_id_gaussianReal]
  have hmean : ∫ ω, squared 0 ω ∂μ = 1 := by
    calc
      ∫ ω, squared 0 ω ∂μ = ∫ x, x ^ 2 ∂(gaussianReal 0 (1 : NNReal)) := by
        simpa [squared, Function.comp_def] using
          hzero.integral_comp (measurable_id'.pow_const 2).aestronglyMeasurable
      _ = 1 := hmean_sq
  filter_upwards [strong_law_ae_real squared hint hindep_sq hident_sq] with ω hω
  simpa [squared, hmean] using hω

/-- Multiplying the innovation information by a fixed treatment-variance
multiplier scales its almost-sure limit by that multiplier. -/
theorem scaled_gaussianInnovation_information_ae
    {innovation : ℕ → Ω → ℝ}
    (hzero : HasLaw (innovation 0) (gaussianReal 0 1) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on innovation))
    (hident : ∀ i, IdentDistrib (innovation i) (innovation 0) μ μ)
    (multiplier : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => multiplier *
        ((∑ i ∈ Finset.range n, (innovation i ω) ^ 2) / n))
      atTop (𝓝 multiplier) := by
  filter_upwards [gaussianInnovation_information_ae hzero hindep hident] with ω hω
  simpa using hω.const_mul multiplier

end InfillGLSLean
