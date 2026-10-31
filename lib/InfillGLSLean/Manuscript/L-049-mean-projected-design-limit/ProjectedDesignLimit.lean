module

public import «L-043-mean-refinement-convergence».RefinementConvergence

/-!
# Projected-design limit for Appendix `lem:mean`

This module formalizes the literal `D_nᵀ t_R` convergence invoked in the
true-GLS paragraph of Appendix `lem:mean`.  The observed partitions are not
assumed nested: `t_R` is the cell-mass-times-cell-average vector induced by
the L-026 regional projection of one fixed spatial L² test.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L049

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal RealInnerProductSpace

open InfillGLSLean.ManuscriptSpecification.L026
open InfillGLSLean.ManuscriptSpecification.L039
open InfillGLSLean.ManuscriptSpecification.L043
open InfillGLSLean.MeanHilbertRiesz

universe v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

private theorem indicator_const_mul_eq_indicator
    (R : Set (Point D)) (a : ℝ) (g : Point D → ℝ) :
    (fun s => R.indicator (fun _ => a) s * g s) =
      R.indicator (fun s => a * g s) := by
  funext s
  by_cases hs : s ∈ R <;> simp [hs]

omit [IsProbabilityMeasure μ] in
private theorem inner_toLp_eq_integral_mul
    (f g : Point D → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ s, f s * g s ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with s hfs hgs
  rw [hfs, hgs]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

omit [IsProbabilityMeasure P] in
private theorem dot_regionalProjectionWeights_regionalValues_eq_integral
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ) (n : ℕ)
    (g : Point D → ℝ) (hg : Integrable g μ) :
    dotProduct (regionalProjectionWeights E f n)
      (regionalValues μ E.maps g n) =
      ∫ s, regionalProjection (E.maps.partition n) f s * g s ∂μ := by
  classical
  rw [dotProduct]
  simp only [regionalProjectionWeights, regionalValues]
  simp only [regionalProjection_apply, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    let R : Set (Point D) := (E.maps.partition n).cell i
    have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
    have havg : μ.real R * cellMean μ R g = ∫ s in R, g s ∂μ := by
      simpa [cellMean, smul_eq_mul] using
        (measure_smul_setAverage g (s := R) (by finiteness))
    change μ.real R * cellMean μ R f * cellMean μ R g =
      ∫ s, R.indicator (fun _ => cellMean μ R f) s * g s ∂μ
    rw [indicator_const_mul_eq_indicator, integral_indicator hR, integral_const_mul]
    rw [← havg]
    ring
  · intro i hi
    let R : Set (Point D) := (E.maps.partition n).cell i
    have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
    change Integrable (fun s => R.indicator (fun _ => cellMean μ R f) s * g s) μ
    rw [indicator_const_mul_eq_indicator, integrable_indicator_iff hR]
    exact (hg.restrict).const_mul _

omit [IsProbabilityMeasure P] in
/-- The exact finite pairing identity for the literal projected-test weights.
It identifies a coordinate of `D_nᵀ t_{Π_n h}` with the L² inner product of
the projected test and a fixed spatial regressor. -/
theorem dot_regionalProjectionWeights_regionalValues_eq_inner
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ) (hf : MemLp f 2 μ)
    (g : Point D → ℝ) (hg : MemLp g 2 μ) (n : ℕ) :
    dotProduct (regionalProjectionWeights E f n)
      (regionalValues μ E.maps g n) =
      inner ℝ
        ((memLp_regionalProjection (E.maps.partition n)
          hf).toLp
          (regionalProjection (E.maps.partition n) f))
        (hg.toLp g) := by
  have hdot := dot_regionalProjectionWeights_regionalValues_eq_integral
    E f n g (hg.integrable (by norm_num))
  calc
    dotProduct (regionalProjectionWeights E f n)
        (regionalValues μ E.maps g n) =
        ∫ s, regionalProjection (E.maps.partition n) f s * g s ∂μ := hdot
    _ = inner ℝ
        ((memLp_regionalProjection (E.maps.partition n) hf).toLp
          (regionalProjection (E.maps.partition n) f))
        (hg.toLp g) := by
          symm
          exact inner_toLp_eq_integral_mul _ _
            (memLp_regionalProjection (E.maps.partition n) hf) hg

/-- The fixed spatial-pairing vector occurring as the limit of the literal
projected design.  Coordinate zero pairs the test with treatment; successors
pair it with the fixed controls. -/
noncomputable def projectedDesignLimit
    (E : FixedConditionalExperiment μ P) (h : Lp ℝ 2 μ) :
    Fin (E.q + 1) → ℝ :=
  Fin.cases
    (inner ℝ h ((treatment_memLp_two E).toLp E.treatment))
    (fun c => inner ℝ h ((control_memLp_two E c).toLp (E.controls c)))

private theorem tendsto_dot_regionalProjectionWeights_regionalValues
    (E : FixedConditionalExperiment μ P) (h : Lp ℝ 2 μ)
    (g : Point D → ℝ) (hg : MemLp g 2 μ) :
    Tendsto
      (fun n => dotProduct (regionalProjectionWeights E (fun s => h s) n)
        (regionalValues μ E.maps g n))
      atTop (nhds (inner ℝ h (hg.toLp g))) := by
  let f : Point D → ℝ := fun s => h s
  have hf : MemLp f 2 μ := by
    simpa [f] using Lp.memLp h
  have htoLp : hf.toLp f = h := by
    simp [f]
  have hpair := tendsto_inner_regionalProjection_toLp E f g hf hg
  rw [htoLp] at hpair
  have hpair' : Tendsto
      (fun n => dotProduct (regionalProjectionWeights E f n)
        (regionalValues μ E.maps g n))
      atTop (nhds (inner ℝ h (hg.toLp g))) := by
    apply hpair.congr'
    filter_upwards [] with n
    exact (dot_regionalProjectionWeights_regionalValues_eq_inner E f hf g hg n).symm
  simpa [f] using hpair'

/-- The exact source `D_nᵀ t_R` convergence for every fixed spatial L² test.
This is the projected-design premise used in the paper's weak true-GLS-score
argument, stated with the literal observed design and regional weights. -/
theorem tendsto_transpose_regionalDesign_mulVec_regionalProjectionWeights
    (E : FixedConditionalExperiment μ P) (h : Lp ℝ 2 μ) :
    Tendsto
      (fun n => Matrix.transpose
        (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
          regionalProjectionWeights E (fun s => h s) n)
      atTop (nhds (projectedDesignLimit E h)) := by
  apply tendsto_pi_nhds.2
  intro j
  refine Fin.cases ?_ ?_ j
  · have ht := tendsto_dot_regionalProjectionWeights_regionalValues E h
      E.treatment (treatment_memLp_two E)
    apply ht.congr'
    filter_upwards [] with n
    change (∑ i, regionalProjectionWeights E (fun s => h s) n i *
      regionalValues μ E.maps E.treatment n i) =
      ∑ i, regionalValues μ E.maps E.treatment n i *
        regionalProjectionWeights E (fun s => h s) n i
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro c
    have hc := tendsto_dot_regionalProjectionWeights_regionalValues E h
      (E.controls c) (control_memLp_two E c)
    apply hc.congr'
    filter_upwards [] with n
    change (∑ i, regionalProjectionWeights E (fun s => h s) n i *
      regionalValues μ E.maps (E.controls c) n i) =
      ∑ i, regionalValues μ E.maps (E.controls c) n i *
        regionalProjectionWeights E (fun s => h s) n i
    apply Finset.sum_congr rfl
    intro i hi
    ring

end InfillGLSLean.ManuscriptSpecification.L049

