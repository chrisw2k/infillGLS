module

import Mathlib.Algebra.Order.Star.Real

public import «L-036-mean-hilbert-riesz».MeanHilbertRiesz
public import «L-039-mean-source-common-refinement».SourceCommonRefinement
public import «L-040-mean-information-limit».InformationLimit
public import «L-041-common-refinement-pd».CommonRefinementPD
public import «L-042-mean-tail-pd».TailPositiveDefiniteness

/-!
# Fixed common-refinement approximation for Appendix `lem:mean`

This module formalizes the fixed-refinement projection passage in the paper's
Appendix `lem:mean`.  Its first layer turns the already-proved nonnested
regional `L²` approximation into convergence in the quotient `Lp` space so
that the source field's continuous centered-integral map can be applied.
No observed-partition nesting or covariance regularity is introduced.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L043

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal RealInnerProductSpace

open InfillGLSLean.ManuscriptSpecification.L026
open InfillGLSLean.ManuscriptSpecification.L037
open InfillGLSLean.ManuscriptSpecification.L039
open InfillGLSLean.ManuscriptSpecification.L040
open InfillGLSLean.ManuscriptSpecification.L041
open InfillGLSLean.ManuscriptSpecification.L042
open InfillGLSLean.MeanHilbertRiesz

universe v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The deterministic observation matrix obtained by projecting each
normalized cell test of a fixed finite partition onto the observed partition
at resolution `n`.  Its `(j,i)` entry is literally the observed-cell mass
times the observed-cell average of the fixed test.  It is the matrix of the
linear combinations described in the fixed-common-refinement paragraph of
Appendix `lem:mean`; it is not an additional observation assumption. -/
noncomputable def projectionObservationMatrix {K : ℕ}
    (E : FixedConditionalExperiment μ P) (partition : AERegionalPartition μ K)
    (n : ℕ) : Matrix (Fin K) (Fin (E.maps.N n)) ℝ :=
  fun j i => regionalProjectionWeights E (partitionCellAverageTest partition j).1 n i

private theorem indicator_const_mul_eq_indicator
    (R : Set (Point D)) (a : ℝ) (g : Point D → ℝ) :
    (fun s => R.indicator (fun _ => a) s * g s) =
      R.indicator (fun s => a * g s) := by
  funext s
  by_cases hs : s ∈ R <;> simp [hs]

omit [IsProbabilityMeasure μ] in
/-- The real `L²` inner product of two concrete representatives is their
ordinary product integral.  This local bridge is used only to identify the
paper's projected design entries with the literal finite linear combinations
of observed regional averages. -/
private theorem inner_toLp_eq_integral_mul
    (f g : Point D → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ s, f s * g s ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with s hfs hgs
  rw [hfs, hgs]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

private theorem integral_partitionCellAverageTest_mul_eq_cellMean
    {K : ℕ} (partition : AERegionalPartition μ K) (j : Fin K)
    (g : Point D → ℝ) :
    (∫ s, (partitionCellAverageTest partition j).1 s * g s ∂μ) =
      cellMean μ (partition.cell j) g := by
  let R : Set (Point D) := partition.cell j
  let a : ℝ := (μ.real R)⁻¹
  have hR : MeasurableSet R := partition.measurable_cell j
  change (∫ s, R.indicator (fun _ => a) s * g s ∂μ) = cellMean μ R g
  rw [indicator_const_mul_eq_indicator, integral_indicator hR, integral_const_mul]
  simp [cellMean, setAverage_eq, R, a, smul_eq_mul]

omit [IsProbabilityMeasure P] in
/-- Applying `projectionObservationMatrix` to literal observed regional
averages gives the spatial pairing of the projected fixed-cell test with the
same integrable function.  This is the exact deterministic design/linear
observation identity needed before taking covariance matrices. -/
theorem projectionObservationMatrix_mulVec_regionalValues_eq_integral
    {K : ℕ} (E : FixedConditionalExperiment μ P)
    (partition : AERegionalPartition μ K) (n : ℕ) (j : Fin K)
    (g : Point D → ℝ) (hg : Integrable g μ) :
    (Matrix.mulVec (projectionObservationMatrix E partition n)
      (regionalValues μ E.maps g n)) j =
      ∫ s, regionalProjection (E.maps.partition n)
        (partitionCellAverageTest partition j).1 s * g s ∂μ := by
  classical
  rw [Matrix.mulVec, dotProduct]
  simp only [projectionObservationMatrix, regionalProjectionWeights, regionalValues]
  change (∑ i, μ.real ((E.maps.partition n).cell i) *
      cellMean μ ((E.maps.partition n).cell i)
        (partitionCellAverageTest partition j).1 *
      cellMean μ ((E.maps.partition n).cell i) g) = _
  simp only [InfillGLSLean.ManuscriptSpecification.L026.regionalProjection_apply,
    Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    let R : Set (Point D) := (E.maps.partition n).cell i
    have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
    have havg : μ.real R * cellMean μ R g = ∫ s in R, g s ∂μ := by
      simpa [cellMean, smul_eq_mul] using
        (measure_smul_setAverage g (s := R) (by finiteness))
    change μ.real R * cellMean μ R (partitionCellAverageTest partition j).1 *
        cellMean μ R g =
      ∫ s, R.indicator (fun _ => cellMean μ R
        (partitionCellAverageTest partition j).1) s * g s ∂μ
    rw [indicator_const_mul_eq_indicator, integral_indicator hR, integral_const_mul]
    rw [← havg]
    ring
  · intro i hi
    let R : Set (Point D) := (E.maps.partition n).cell i
    have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
    change Integrable (fun s => R.indicator (fun _ =>
      cellMean μ R (partitionCellAverageTest partition j).1) s * g s) μ
    rw [indicator_const_mul_eq_indicator, integrable_indicator_iff hR]
    exact (hg.restrict).const_mul _

/-- The nonnested regional averaging result, expressed in the actual spatial
`Lp` quotient.  This is the exact bridge from Lemma `lem:averaging` to the
fixed-refinement argument in Appendix `lem:mean`. -/
theorem tendsto_regionalProjection_toLp
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ) (hf : MemLp f 2 μ) :
    Tendsto
      (fun n => (memLp_regionalProjection (E.maps.partition n) hf).toLp
        (regionalProjection (E.maps.partition n) f))
      atTop (nhds (hf.toLp f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hL2 := regionalAveraging_tendsto_L2 E f hf
  simpa only [← MemLp.toLp_sub, Lp.norm_toLp, toReal_eLpNorm] using hL2

/-- Applying the source field's continuous centered-test map to the literal
regional projections preserves the nonnested `L²` limit.  This is precisely
the paper's assertion that the corresponding centered error averages
converge; continuity is derived from the fixed field's joint second moment in
L-036. -/
theorem tendsto_centeredTestIntegral_of_regionalProjection
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (f : Point D → ℝ) (hf : MemLp f 2 μ) :
    Tendsto
      (fun n => centeredTestIntegralLp E covariance
        ((memLp_regionalProjection (E.maps.partition n) hf).toLp
          (regionalProjection (E.maps.partition n) f)))
      atTop (nhds (centeredTestIntegralLp E covariance (hf.toLp f))) := by
  have hprojection := tendsto_regionalProjection_toLp E f hf
  have hcontinuous :=
    ((centeredTestIntegralContinuousLinearMap E).continuous.tendsto (hf.toLp f)).comp
      hprojection
  rw [centeredTestIntegralContinuousLinearMap_apply E covariance] at hcontinuous
  apply hcontinuous.congr
  intro n
  exact centeredTestIntegralContinuousLinearMap_apply E covariance _

/-- The covariance inner products of two projected spatial tests converge to
the covariance inner product of the fixed tests.  This is the Hilbert-space
form of the finite covariance-matrix convergence asserted in the fixed
common-refinement paragraph of Appendix `lem:mean`. -/
theorem tendsto_inner_centeredTestIntegral_of_regionalProjection
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (f g : Point D → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Tendsto
      (fun n => inner ℝ
        (centeredTestIntegralLp E covariance
          ((memLp_regionalProjection (E.maps.partition n) hf).toLp
            (regionalProjection (E.maps.partition n) f)))
        (centeredTestIntegralLp E covariance
          ((memLp_regionalProjection (E.maps.partition n) hg).toLp
            (regionalProjection (E.maps.partition n) g))))
      atTop
      (nhds (inner ℝ (centeredTestIntegralLp E covariance (hf.toLp f))
        (centeredTestIntegralLp E covariance (hg.toLp g)))) := by
  exact (tendsto_centeredTestIntegral_of_regionalProjection E covariance f hf).inner
    (tendsto_centeredTestIntegral_of_regionalProjection E covariance g hg)

/-- Pairing a projected fixed test against any fixed spatial L2 regressor
converges to the corresponding fixed L2 pairing.  This is the generic design
entry convergence needed when the fixed common-refinement cell tests are
paired with treatment and controls. -/
theorem tendsto_inner_regionalProjection_toLp
    (E : FixedConditionalExperiment μ P) (f g : Point D → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Tendsto
      (fun n => inner ℝ
        ((memLp_regionalProjection (E.maps.partition n) hf).toLp
          (regionalProjection (E.maps.partition n) f))
        (hg.toLp g))
      atTop (nhds (inner ℝ (hf.toLp f) (hg.toLp g))) := by
  exact (tendsto_regionalProjection_toLp E f hf).inner tendsto_const_nhds

/-- For a fixed cell of a finite common refinement, its literal projected
linear combination of observed averages converges to its own regional average
against any fixed L2 regressor.  This is the entrywise design convergence in
the fixed-refinement paragraph of Appendix `lem:mean`. -/
theorem tendsto_projectionObservationMatrix_mulVec_regionalValues
    {K : ℕ} (E : FixedConditionalExperiment μ P)
    (partition : AERegionalPartition μ K) (j : Fin K)
    (g : Point D → ℝ) (hg : MemLp g 2 μ) :
    Tendsto
      (fun n => (Matrix.mulVec (projectionObservationMatrix E partition n)
        (regionalValues μ E.maps g n)) j)
      atTop (nhds (cellMean μ (partition.cell j) g)) := by
  let f : Point D → ℝ := (partitionCellAverageTest partition j).1
  let hf : MemLp f 2 μ := (partitionCellAverageTest partition j).2
  have hpair := tendsto_inner_regionalProjection_toLp E f g hf hg
  convert hpair using 1
  · funext n
    calc
      (Matrix.mulVec (projectionObservationMatrix E partition n)
          (regionalValues μ E.maps g n)) j =
          ∫ s, regionalProjection (E.maps.partition n) f s * g s ∂μ := by
            simpa only [f] using
              (projectionObservationMatrix_mulVec_regionalValues_eq_integral
                E partition n j g (hg.integrable (by norm_num)))
      _ = inner ℝ
          ((memLp_regionalProjection (E.maps.partition n) hf).toLp
            (regionalProjection (E.maps.partition n) f))
          (hg.toLp g) := by
            symm
            exact inner_toLp_eq_integral_mul _ _
              (memLp_regionalProjection (E.maps.partition n) hf) hg
  · congr 1
    calc
      cellMean μ (partition.cell j) g = ∫ s, f s * g s ∂μ := by
        symm
        simpa only [f] using
          (integral_partitionCellAverageTest_mul_eq_cellMean partition j g)
      _ = inner ℝ (hf.toLp f) (hg.toLp g) := by
        symm
        exact inner_toLp_eq_integral_mul f g hf hg

/-- The entire projected design matrix converges entrywise to the design of
the fixed finite partition.  Its two finite column cases are exactly the
treatment and fixed-control instances of the preceding literal identity. -/
theorem tendsto_projectionObservationMatrix_mul_regionalDesign
    {K : ℕ} (E : FixedConditionalExperiment μ P)
    (partition : AERegionalPartition μ K) :
    Tendsto
      (fun n => projectionObservationMatrix E partition n *
        regionalDesign μ E.maps E.treatment E.controls n)
      atTop (nhds (partitionDesign partition E.treatment E.controls)) := by
  apply tendsto_pi_nhds.2
  intro j
  apply tendsto_pi_nhds.2
  intro ell
  refine Fin.cases ?_ ?_ ell
  · simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct,
      regionalDesign_apply, partitionDesign_apply, Fin.cases_zero,
      regionalValues, partitionRegionalValues] using
      (tendsto_projectionObservationMatrix_mulVec_regionalValues
        E partition j E.treatment (treatment_memLp_two E))
  · intro c
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct,
      regionalDesign_apply, regionalControls_apply, partitionDesign_apply,
      Fin.cases_succ, regionalValues, partitionRegionalValues] using
      (tendsto_projectionObservationMatrix_mulVec_regionalValues
        E partition j (E.controls c) (control_memLp_two E c))

omit [IsProbabilityMeasure P] in
private theorem transpose_projectionObservationMatrix_mulVec_eq_regionalProjectionWeights
    {K : ℕ} (E : FixedConditionalExperiment μ P)
    (partition : AERegionalPartition μ K) (weight : Fin K → ℝ) (n : ℕ) :
    (projectionObservationMatrix E partition n)ᵀ *ᵥ weight =
      regionalProjectionWeights E (partitionWeightedCellTest partition weight).1 n := by
  classical
  funext i
  rw [Matrix.mulVec_transpose]
  simp only [regionalProjectionWeights_apply]
  let R : Set (Point D) := (E.maps.partition n).cell i
  change (∑ j, weight j *
      (μ.real R * cellMean μ R (partitionCellAverageTest partition j).1)) =
    μ.real R * cellMean μ R (fun s => ∑ j,
      weight j * (partitionCellAverageTest partition j).1 s)
  have hintegrable : ∀ j : Fin K,
      Integrable (fun s => weight j * (partitionCellAverageTest partition j).1 s)
        (μ.restrict R) := by
    intro j
    exact ((partitionCellAverageTest partition j).2.integrable (by norm_num)).restrict.const_mul _
  have hintegral :
      (∫ s, (∑ j, weight j * (partitionCellAverageTest partition j).1 s)
        ∂(μ.restrict R)) =
        ∑ j, weight j * (∫ s, (partitionCellAverageTest partition j).1 s
          ∂(μ.restrict R)) := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
    · intro j hj
      exact hintegrable j
  simp only [cellMean, setAverage_eq, smul_eq_mul]
  rw [hintegral, Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem quadraticForm_projectedCovariance
    {K I : Type*} [Fintype K] [Fintype I]
    (observation : Matrix K I ℝ) (covariance : Matrix I I ℝ)
    (weight : K → ℝ) :
    quadraticForm (observation * covariance * observationᵀ) weight =
      quadraticForm covariance (observationᵀ *ᵥ weight) := by
  rw [quadraticForm_eq_dotProduct_mulVec, quadraticForm_eq_dotProduct_mulVec]
  rw [← Matrix.mulVec_mulVec weight (observation * covariance) observationᵀ]
  rw [Matrix.dotProduct_mulVec]
  rw [← Matrix.vecMul_vecMul]
  rw [← Matrix.mulVec_transpose observation weight]
  rw [← Matrix.dotProduct_mulVec]

private theorem norm_sq_centeredTestIntegralLp_partitionWeighted_eq_quadraticForm
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K) (weight : Fin K → ℝ) :
    ‖centeredTestIntegralLp E covariance
        ((partitionWeightedCellTest partition weight).2.toLp
          (partitionWeightedCellTest partition weight).1)‖ ^ 2 =
      quadraticForm (partitionErrorCovariance E partition) weight := by
  let h : L2TestFunction μ := partitionWeightedCellTest partition weight
  let centered : Fin K → Ω → ℝ :=
    centeredFiniteError (partitionRegionalErrors E partition)
      (partitionRegionalErrorMean E partition)
  let score : Ω → ℝ := finiteWeightedScore weight centered
  have hLp : centeredTestIntegralLp E covariance (h.2.toLp h.1) =
      centeredTestIntegralL2 E covariance h := by
    exact centeredTestIntegralLp_toLp E covariance h
  have hcomponent : ∀ i, MemLp (centered i) 2 P := by
    intro i
    exact (partitionRegionalErrors_memLp_two E partition i).sub
      (memLp_const (partitionRegionalErrorMean E partition i))
  have hcomponent_zero : ∀ i, P[centered i] = 0 := by
    intro i
    change (∫ ω, partitionRegionalErrors E partition i ω -
      partitionRegionalErrorMean E partition i ∂P) = 0
    have herror : Integrable (partitionRegionalErrors E partition i) P :=
      (partitionRegionalErrors_memLp_two E partition i).integrable (by norm_num)
    rw [integral_sub herror (integrable_const _), integral_const]
    simp [partitionRegionalErrorMean]
  have hscore_mem : MemLp score 2 P := by
    dsimp [score]
    exact memLp_finiteWeightedScore weight centered hcomponent
  have hscore_zero : P[score] = 0 := by
    dsimp [score]
    exact integral_finiteWeightedScore_eq_zero weight centered hcomponent hcomponent_zero
  have hscore_ae : centeredTestIntegral μ P E.error h =ᵐ[P] score := by
    filter_upwards [centeredTestIntegral_partitionWeighted_ae_eq_score
      E partition weight] with ω hω
    change centeredTestIntegral μ P E.error (partitionWeightedCellTest partition weight) ω =
      finiteWeightedScore weight
        (centeredFiniteError (partitionRegionalErrors E partition)
          (partitionRegionalErrorMean E partition)) ω
    rw [← centeredIntegralProcess_apply]
    exact hω
  rw [show (partitionWeightedCellTest partition weight).2.toLp
      (partitionWeightedCellTest partition weight).1 = h.2.toLp h.1 by rfl, hLp]
  calc
    ‖centeredTestIntegralL2 E covariance h‖ ^ 2 =
        inner ℝ (centeredTestIntegralL2 E covariance h)
          (centeredTestIntegralL2 E covariance h) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ ω, inner ℝ (centeredTestIntegralL2 E covariance h ω)
        (centeredTestIntegralL2 E covariance h ω) ∂P := L2.inner_def _ _
    _ = ∫ ω, (score ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [centeredTestIntegralL2_coeFn_ae E covariance h,
        hscore_ae] with ω hcoe hscore
      rw [hcoe, hscore]
      rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = Var[score; P] := by
      rw [variance_eq_integral hscore_mem.aemeasurable, hscore_zero]
      simp
    _ = quadraticForm (partitionErrorCovariance E partition) weight := by
      dsimp [score, centered]
      exact variance_partitionWeightedScore_eq_quadraticForm E partition weight

/-- For every fixed spatial `L²` test, the true covariance quadratic form of
the deterministic observed-region weights induced by its literal regional
projection converges to the fixed test's centered-field variance.  This is
the quadratic-form version of the covariance convergence used for a fixed
common-refinement experiment in Appendix `lem:mean`. -/
theorem tendsto_trueQuadratic_regionalProjectionWeights
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (f : Point D → ℝ) (hf : MemLp f 2 μ) :
    Tendsto
      (fun n => quadraticForm (trueCovariance E n)
        (regionalProjectionWeights E f n))
      atTop
      (nhds (‖centeredTestIntegralLp E covariance (hf.toLp f)‖ ^ 2)) := by
  have hprojection : Tendsto
      (fun n => weightedRegionalCellTestLp E n (regionalProjectionWeights E f n))
      atTop (nhds (hf.toLp f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_zero] using
      (weightedRegionalCellTestLp_sub_tendsto_zero E f hf).norm
  have hcontinuous :=
    ((centeredTestIntegralContinuousLinearMap E).continuous.tendsto (hf.toLp f)).comp
      hprojection
  rw [centeredTestIntegralContinuousLinearMap_apply E covariance] at hcontinuous
  have htest : Tendsto
      (fun n => centeredTestIntegralLp E covariance
        (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n)))
      atTop (nhds (centeredTestIntegralLp E covariance (hf.toLp f))) := by
    apply hcontinuous.congr
    intro n
    exact centeredTestIntegralContinuousLinearMap_apply E covariance _
  have hnorm := htest.norm.pow 2
  refine hnorm.congr (fun n => ?_)
  rw [centeredTestIntegralLp_weightedRegionalCellTestLp,
    weightedRegionalCellTest_centeredIntegral_norm_sq_eq_trueQuadratic]

/-- For the literal finite projection of a fixed experiment, every covariance
quadratic form converges to the covariance quadratic form of that fixed
experiment.  This packages the source paragraph's ``design and covariance
matrices converge'' claim at the quadratic-form level, before finite
polarization turns it into matrix convergence. -/
theorem tendsto_quadraticForm_projectedCovariance
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K) (weight : Fin K → ℝ) :
    Tendsto
      (fun n => quadraticForm
        (projectionObservationMatrix E partition n * trueCovariance E n *
          (projectionObservationMatrix E partition n)ᵀ) weight)
      atTop (nhds (quadraticForm (partitionErrorCovariance E partition) weight)) := by
  have htest := tendsto_trueQuadratic_regionalProjectionWeights E covariance
    (partitionWeightedCellTest partition weight).1
    (partitionWeightedCellTest partition weight).2
  rw [norm_sq_centeredTestIntegralLp_partitionWeighted_eq_quadraticForm
    E covariance partition weight] at htest
  convert htest using 1
  funext n
  rw [quadraticForm_projectedCovariance,
    transpose_projectionObservationMatrix_mulVec_eq_regionalProjectionWeights]

/-- The covariance matrices of the literal projections of a fixed finite
partition converge entrywise to the finite partition covariance. -/
theorem tendsto_projectedCovariance
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K) :
    Tendsto
      (fun n => projectionObservationMatrix E partition n * trueCovariance E n *
        (projectionObservationMatrix E partition n)ᵀ)
      atTop (nhds (partitionErrorCovariance E partition)) := by
  apply tendsto_matrix_of_quadratic_tendsto
  · intro n
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (trueCovariance_posDef E covariance n).posSemidef.mul_mul_conjTranspose_same
        (projectionObservationMatrix E partition n)
  · exact (partitionErrorCovariance_posDef E covariance partition).posSemidef
  · intro weight
    exact tendsto_quadraticForm_projectedCovariance E covariance partition weight

/-- A positive-definite finite limit and positive-semidefinite approximants
give eventual positive definiteness.  The argument uses only determinant
continuity, so it applies to the projected covariance matrices without a
new rank or rate hypothesis. -/
private theorem eventually_posDef_of_tendsto_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℝ) (A₀ : Matrix ι ι ℝ)
    (hA : Tendsto A atTop (nhds A₀))
    (hpsd : ∀ n, (A n).PosSemidef) (hpd : A₀.PosDef) :
    ∀ᶠ n in atTop, (A n).PosDef := by
  have hdet : Tendsto (fun n => (A n).det) atTop (nhds A₀.det) :=
    (continuous_id.matrix_det.tendsto A₀).comp hA
  have hdet₀ : A₀.det ≠ 0 := by
    exact ((Matrix.isUnit_iff_isUnit_det A₀).mp hpd.isUnit).ne_zero
  have hnonzero : ∀ᶠ n in atTop, (A n).det ≠ 0 := by
    have hmem : A₀.det ∈ ({0}ᶜ : Set ℝ) := by simpa using hdet₀
    have hopen : ({0}ᶜ : Set ℝ) ∈ nhds A₀.det :=
      isOpen_compl_singleton.mem_nhds hmem
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hdet.eventually hopen
  filter_upwards [hnonzero] with n hn
  exact (hpsd n).posDef_iff_det_ne_zero.mpr hn

/-- The covariance of the finite projected observations is nonsingular
eventually.  It follows from the fixed finite covariance's source-derived
positive definiteness and the preceding covariance convergence. -/
theorem eventually_projectionObservationCovariance_posDef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K) :
    ∀ᶠ n in atTop,
      (projectionObservationMatrix E partition n * trueCovariance E n *
        (projectionObservationMatrix E partition n)ᵀ).PosDef := by
  apply eventually_posDef_of_tendsto_posDef
    (fun n => projectionObservationMatrix E partition n * trueCovariance E n *
      (projectionObservationMatrix E partition n)ᵀ)
    (partitionErrorCovariance E partition)
  · exact tendsto_projectedCovariance E covariance partition
  · intro n
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (trueCovariance_posDef E covariance n).posSemidef.mul_mul_conjTranspose_same
        (projectionObservationMatrix E partition n)
  · exact partitionErrorCovariance_posDef E covariance partition

/-- The finite GLS Gram matrix formed from the literal projected observations
of a fixed partition at observed resolution `n`. -/
@[expose] noncomputable def projectedGLSGram
    (E : FixedConditionalExperiment μ P) {K : ℕ}
    (partition : AERegionalPartition μ K) (n : ℕ) :
    Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ :=
  trueGLSGram
    (projectionObservationMatrix E partition n * trueCovariance E n *
      (projectionObservationMatrix E partition n)ᵀ)
    (projectionObservationMatrix E partition n *
      regionalDesign μ E.maps E.treatment E.controls n)

/-- The finite GLS Gram matrix of the fixed partition experiment itself. -/
@[expose] noncomputable def partitionGLSGram
    (E : FixedConditionalExperiment μ P) {K : ℕ}
    (partition : AERegionalPartition μ K) :
    Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ :=
  trueGLSGram (partitionErrorCovariance E partition)
    (partitionDesign partition E.treatment E.controls)

/-- The projected finite GLS Gram matrices converge to the GLS Gram matrix
of the fixed partition.  This is finite matrix continuity after the exact
projected design and covariance limits above. -/
theorem tendsto_projectedGLSGram
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K) :
    Tendsto (projectedGLSGram E partition) atTop
      (nhds (partitionGLSGram E partition)) := by
  let C : ℕ → Matrix (Fin K) (Fin K) ℝ := fun n =>
    projectionObservationMatrix E partition n * trueCovariance E n *
      (projectionObservationMatrix E partition n)ᵀ
  let D : ℕ → Matrix (Fin K) (Fin (E.q + 1)) ℝ := fun n =>
    projectionObservationMatrix E partition n *
      regionalDesign μ E.maps E.treatment E.controls n
  let C₀ : Matrix (Fin K) (Fin K) ℝ := partitionErrorCovariance E partition
  let D₀ : Matrix (Fin K) (Fin (E.q + 1)) ℝ :=
    partitionDesign partition E.treatment E.controls
  have hC : Tendsto C atTop (nhds C₀) := by
    simpa only [C, C₀] using tendsto_projectedCovariance E covariance partition
  have hD : Tendsto D atTop (nhds D₀) := by
    simpa only [D, D₀] using
      tendsto_projectionObservationMatrix_mul_regionalDesign E partition
  have hpd : C₀.PosDef := by
    simpa only [C₀] using partitionErrorCovariance_posDef E covariance partition
  have hdetunit : IsUnit C₀.det := (Matrix.isUnit_iff_isUnit_det C₀).mp hpd.isUnit
  have hcont : ContinuousAt Ring.inverse C₀.det := by
    simpa only [hdetunit.unit_spec] using
      NormedRing.inverse_continuousAt hdetunit.unit
  have hCinv : Tendsto (fun n => (C n)⁻¹) atTop (nhds C₀⁻¹) :=
    (continuousAt_matrix_inv C₀ hcont).tendsto.comp hC
  have hDt : Tendsto (fun n => (D n)ᵀ) atTop (nhds D₀ᵀ) :=
    (continuous_id.matrix_transpose.tendsto D₀).comp hD
  have hleft : Tendsto (fun n => (D n)ᵀ * (C n)⁻¹) atTop
      (nhds (D₀ᵀ * C₀⁻¹)) := by
    have hmul : Continuous (fun pair :
        Matrix (Fin (E.q + 1)) (Fin K) ℝ × Matrix (Fin K) (Fin K) ℝ =>
        pair.1 * pair.2) :=
      continuous_fst.matrix_mul continuous_snd
    have hpair : Tendsto (fun n => ((D n)ᵀ, (C n)⁻¹)) atTop
        (nhds (D₀ᵀ, C₀⁻¹)) := hDt.prodMk_nhds hCinv
    have hmul_tendsto : Tendsto (fun pair :
        Matrix (Fin (E.q + 1)) (Fin K) ℝ × Matrix (Fin K) (Fin K) ℝ =>
        pair.1 * pair.2) (nhds (D₀ᵀ, C₀⁻¹)) (nhds (D₀ᵀ * C₀⁻¹)) :=
      hmul.tendsto (D₀ᵀ, C₀⁻¹)
    have hcomp : Tendsto
        ((fun pair : Matrix (Fin (E.q + 1)) (Fin K) ℝ ×
          Matrix (Fin K) (Fin K) ℝ => pair.1 * pair.2) ∘
          fun n => ((D n)ᵀ, (C n)⁻¹)) atTop (nhds (D₀ᵀ * C₀⁻¹)) :=
      hmul_tendsto.comp hpair
    apply hcomp.congr
    intro n
    rfl
  have hright : Tendsto (fun n => ((D n)ᵀ * (C n)⁻¹) * D n) atTop
      (nhds ((D₀ᵀ * C₀⁻¹) * D₀)) := by
    have hmul : Continuous (fun pair :
        Matrix (Fin (E.q + 1)) (Fin K) ℝ ×
          Matrix (Fin K) (Fin (E.q + 1)) ℝ =>
        pair.1 * pair.2) :=
      continuous_fst.matrix_mul continuous_snd
    have hpair : Tendsto (fun n => ((D n)ᵀ * (C n)⁻¹, D n)) atTop
        (nhds (D₀ᵀ * C₀⁻¹, D₀)) := hleft.prodMk_nhds hD
    have hmul_tendsto : Tendsto (fun pair :
        Matrix (Fin (E.q + 1)) (Fin K) ℝ ×
          Matrix (Fin K) (Fin (E.q + 1)) ℝ =>
        pair.1 * pair.2) (nhds (D₀ᵀ * C₀⁻¹, D₀))
          (nhds ((D₀ᵀ * C₀⁻¹) * D₀)) :=
      hmul.tendsto (D₀ᵀ * C₀⁻¹, D₀)
    have hcomp : Tendsto
        ((fun pair : Matrix (Fin (E.q + 1)) (Fin K) ℝ ×
          Matrix (Fin K) (Fin (E.q + 1)) ℝ => pair.1 * pair.2) ∘
          fun n => ((D n)ᵀ * (C n)⁻¹, D n)) atTop
          (nhds ((D₀ᵀ * C₀⁻¹) * D₀)) :=
      hmul_tendsto.comp hpair
    apply hcomp.congr
    intro n
    rfl
  change Tendsto (fun n => ((D n)ᵀ * (C n)⁻¹) * D n) atTop
    (nhds ((D₀ᵀ * C₀⁻¹) * D₀))
  exact hright

/-- Coefficient covariance of true GLS on the finite projected observation
vector at observed resolution `n`. -/
@[expose] noncomputable def projectedGLSCoefficientCovariance
    (E : FixedConditionalExperiment μ P) {K : ℕ}
    (partition : AERegionalPartition μ K) (n : ℕ) :
    Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ :=
  (projectedGLSGram E partition n)⁻¹

/-- Coefficient covariance of true GLS in the fixed finite partition
experiment. -/
@[expose] noncomputable def partitionGLSCoefficientCovariance
    (E : FixedConditionalExperiment μ P) {K : ℕ}
    (partition : AERegionalPartition μ K) :
    Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ :=
  (partitionGLSGram E partition)⁻¹

omit [IsProbabilityMeasure P] in
/-- Literal expansion of the projected coefficient covariance into the
standard finite true-GLS expression. -/
@[simp] theorem projectedGLSCoefficientCovariance_eq_trueGLS
    (E : FixedConditionalExperiment μ P) {K : ℕ}
    (partition : AERegionalPartition μ K) (n : ℕ) :
    projectedGLSCoefficientCovariance E partition n =
      trueGLSCoefficientCovariance
        (projectionObservationMatrix E partition n * trueCovariance E n *
          (projectionObservationMatrix E partition n)ᵀ)
        (projectionObservationMatrix E partition n *
          regionalDesign μ E.maps E.treatment E.controls n) := rfl

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Literal expansion of the fixed-partition coefficient covariance into the
standard finite true-GLS expression. -/
@[simp] theorem partitionGLSCoefficientCovariance_eq_trueGLS
    (E : FixedConditionalExperiment μ P) {K : ℕ}
    (partition : AERegionalPartition μ K) :
    partitionGLSCoefficientCovariance E partition =
      trueGLSCoefficientCovariance (partitionErrorCovariance E partition)
        (partitionDesign partition E.treatment E.controls) := rfl

private theorem partitionGLSGram_posDef_of_rank
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K)
    (hrank : (partitionDesign partition E.treatment E.controls).rank = E.q + 1) :
    (partitionGLSGram E partition).PosDef := by
  unfold partitionGLSGram
  apply glsGram_posDef_of_covariance_posDef_and_rank
  · exact partitionErrorCovariance_posDef E covariance partition
  · simpa using hrank

private theorem tendsto_projectedGLSCoefficientCovariance_of_partitionGLSGram_posDef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K)
    (hgram : (partitionGLSGram E partition).PosDef) :
    Tendsto (projectedGLSCoefficientCovariance E partition) atTop
      (nhds (partitionGLSCoefficientCovariance E partition)) := by
  have hdetunit : IsUnit (partitionGLSGram E partition).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hgram.isUnit
  have hcont : ContinuousAt Ring.inverse (partitionGLSGram E partition).det := by
    simpa only [hdetunit.unit_spec] using
      NormedRing.inverse_continuousAt hdetunit.unit
  change Tendsto (fun n => (projectedGLSGram E partition n)⁻¹) atTop
    (nhds (partitionGLSGram E partition)⁻¹)
  exact (continuousAt_matrix_inv (partitionGLSGram E partition) hcont).tendsto.comp
    (tendsto_projectedGLSGram E covariance partition)

/-- Eventual positive semidefiniteness plus convergence to a positive-definite
finite limit gives eventual positive definiteness.  This is the tail form of
the determinant-continuity argument, needed because projected designs need not
have full rank at early observed resolutions. -/
private theorem eventually_posDef_of_tendsto_posDef_of_eventually_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℝ) (A₀ : Matrix ι ι ℝ)
    (hA : Tendsto A atTop (nhds A₀))
    (hpsd : ∀ᶠ n in atTop, (A n).PosSemidef) (hpd : A₀.PosDef) :
    ∀ᶠ n in atTop, (A n).PosDef := by
  have hdet : Tendsto (fun n => (A n).det) atTop (nhds A₀.det) :=
    (continuous_id.matrix_det.tendsto A₀).comp hA
  have hdet₀ : A₀.det ≠ 0 := by
    exact ((Matrix.isUnit_iff_isUnit_det A₀).mp hpd.isUnit).ne_zero
  have hnonzero : ∀ᶠ n in atTop, (A n).det ≠ 0 := by
    have hmem : A₀.det ∈ ({0}ᶜ : Set ℝ) := by simpa using hdet₀
    have hopen : ({0}ᶜ : Set ℝ) ∈ nhds A₀.det :=
      isOpen_compl_singleton.mem_nhds hmem
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hdet.eventually hopen
  filter_upwards [hpsd, hnonzero] with n hpsd hn
  exact hpsd.posDef_iff_det_ne_zero.mpr hn

/-- Once the fixed partition GLS Gram matrix is positive definite, the
projected GLS Gram matrices are positive definite eventually.  No uniform
rank or nesting claim is used: the tail follows from the source-derived
projected covariance nonsingularity and finite continuity. -/
private theorem eventually_projectedGLSGram_posDef_of_partitionGLSGram_posDef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K)
    (hgram : (partitionGLSGram E partition).PosDef) :
    ∀ᶠ n in atTop, (projectedGLSGram E partition n).PosDef := by
  apply eventually_posDef_of_tendsto_posDef_of_eventually_posSemidef
    (projectedGLSGram E partition) (partitionGLSGram E partition)
  · exact tendsto_projectedGLSGram E covariance partition
  · filter_upwards [eventually_projectionObservationCovariance_posDef
      E covariance partition] with n hcovariance
    unfold projectedGLSGram trueGLSGram
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hcovariance.inv.posSemidef.conjTranspose_mul_mul_same
        (projectionObservationMatrix E partition n *
          regionalDesign μ E.maps E.treatment E.controls n)
  · exact hgram

/-- On the common tail where both finite GLS problems are nonsingular, full
observed GLS has no larger coefficient covariance than GLS based only on the
fixed partition's projected linear combinations. -/
private theorem eventually_projectedCoefficientCovariance_sub_true_posSemidef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K)
    (hfixed : (partitionGLSGram E partition).PosDef) :
    ∀ᶠ n in atTop,
      (projectedGLSCoefficientCovariance E partition n -
        trueGLSCoefficientCovariance (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n)).PosSemidef := by
  filter_upwards [eventually_projectionObservationCovariance_posDef
      E covariance partition,
    eventually_trueGLSGram_posDef E covariance,
    eventually_projectedGLSGram_posDef_of_partitionGLSGram_posDef
      E covariance partition hfixed] with n hprojected_covariance htrue_gram
        hprojected_gram
  change (trueGLSCoefficientCovariance
      (projectionObservationMatrix E partition n * trueCovariance E n *
        (projectionObservationMatrix E partition n)ᵀ)
      (projectionObservationMatrix E partition n *
        regionalDesign μ E.maps E.treatment E.controls n) -
      trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n)).PosSemidef
  exact trueGLSCoefficientCovariance_mono_of_linearObservation
    (trueCovariance E n) (regionalDesign μ E.maps E.treatment E.controls n)
    (projectionObservationMatrix E partition n)
    (trueCovariance_posDef E covariance n) hprojected_covariance htrue_gram
    hprojected_gram

/-- The fixed-partition limsup comparison in the exact epsilon-tail form used
by Appendix `lem:mean`: full observed GLS is eventually no larger in every
coefficient quadratic form than projected GLS on any fixed finite experiment,
up to an arbitrary positive epsilon. -/
private theorem eventually_quadraticForm_trueGLS_le_partition_add
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {K : ℕ} (partition : AERegionalPartition μ K)
    (hfixed : (partitionGLSGram E partition).PosDef) :
    ∀ (x : Fin (E.q + 1) → ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        quadraticForm
          (trueGLSCoefficientCovariance (trueCovariance E n)
            (regionalDesign μ E.maps E.treatment E.controls n)) x ≤
          quadraticForm (partitionGLSCoefficientCovariance E partition) x + ε := by
  intro x ε hε
  have hcoefficient :=
    tendsto_projectedGLSCoefficientCovariance_of_partitionGLSGram_posDef
      E covariance partition hfixed
  have hcontinuous : Continuous (fun B : Matrix (Fin (E.q + 1))
      (Fin (E.q + 1)) ℝ => quadraticForm B x) := by
    unfold quadraticForm
    fun_prop
  have hquadratic : Tendsto
      (fun n => quadraticForm (projectedGLSCoefficientCovariance E partition n) x)
      atTop (nhds (quadraticForm (partitionGLSCoefficientCovariance E partition) x)) :=
    (hcontinuous.tendsto (partitionGLSCoefficientCovariance E partition)).comp
      hcoefficient
  have hprojected_lt : ∀ᶠ n in atTop,
      quadraticForm (projectedGLSCoefficientCovariance E partition n) x <
        quadraticForm (partitionGLSCoefficientCovariance E partition) x + ε :=
    (tendsto_order.1 hquadratic).2 _ (by linarith)
  filter_upwards [eventually_projectedCoefficientCovariance_sub_true_posSemidef
      E covariance partition hfixed, hprojected_lt] with n hcomparison hlt
  have hnonnegative := hcomparison.dotProduct_mulVec_nonneg x
  change 0 ≤ x ⬝ᵥ
    ((projectedGLSCoefficientCovariance E partition n -
      trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n)) *ᵥ x) at hnonnegative
  rw [sub_mulVec, dotProduct_sub] at hnonnegative
  have hle :
      quadraticForm
        (trueGLSCoefficientCovariance (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n)) x ≤
        quadraticForm (projectedGLSCoefficientCovariance E partition n) x := by
    rw [quadraticForm_eq_dotProduct_mulVec, quadraticForm_eq_dotProduct_mulVec]
    exact sub_nonneg.mp hnonnegative
  exact hle.trans hlt.le

/-- For a literal source common refinement whose design rank is inherited
from one of its observed resolutions, the projected coefficient covariance
converges to the coefficient covariance of that fixed experiment.  The rank
premise is exactly the existing observed-rank equality; it is transferred by
L-039 and is not stored as a new experiment assumption. -/
theorem FirstCommonRefinement.tendsto_projectedGLSCoefficientCovariance_of_observed_rank_eq
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {k : ℕ} (W : FirstCommonRefinement E.maps k) (i : Fin (k + 1))
    (hrank :
      (regionalDesign μ E.maps E.treatment E.controls i.1).rank = E.q + 1) :
    Tendsto (projectedGLSCoefficientCovariance E W.partition) atTop
      (nhds (partitionGLSCoefficientCovariance E W.partition)) := by
  have hfixed_rank :
      (partitionDesign W.partition E.treatment E.controls).rank = E.q + 1 :=
    W.partitionDesign_rank_eq_of_observed_rank_eq E i hrank
  have hfixed_gram : (partitionGLSGram E W.partition).PosDef :=
    partitionGLSGram_posDef_of_rank E covariance W.partition hfixed_rank
  exact tendsto_projectedGLSCoefficientCovariance_of_partitionGLSGram_posDef
    E covariance W.partition hfixed_gram

/-- Exact fixed-common-refinement upper comparison for the information-limit
argument.  Its observed-rank premise is a local source fact supplied from
`E.eventual_full_rank`; it is not a new hypothesis on the experiment. -/
theorem FirstCommonRefinement.eventually_quadraticForm_trueGLS_le_fixed_add_of_observed_rank_eq
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {k : ℕ} (W : FirstCommonRefinement E.maps k) (i : Fin (k + 1))
    (hrank :
      (regionalDesign μ E.maps E.treatment E.controls i.1).rank = E.q + 1) :
    ∀ (x : Fin (E.q + 1) → ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        quadraticForm
          (trueGLSCoefficientCovariance (trueCovariance E n)
            (regionalDesign μ E.maps E.treatment E.controls n)) x ≤
          quadraticForm
            (trueGLSCoefficientCovariance (partitionErrorCovariance E W.partition)
              (partitionDesign W.partition E.treatment E.controls)) x + ε := by
  have hfixed_rank :
      (partitionDesign W.partition E.treatment E.controls).rank = E.q + 1 :=
    W.partitionDesign_rank_eq_of_observed_rank_eq E i hrank
  have hfixed_gram : (partitionGLSGram E W.partition).PosDef :=
    partitionGLSGram_posDef_of_rank E covariance W.partition hfixed_rank
  intro x ε hε
  simpa only [partitionGLSCoefficientCovariance_eq_trueGLS] using
    (eventually_quadraticForm_trueGLS_le_partition_add
      E covariance W.partition hfixed_gram x ε hε)

end InfillGLSLean.ManuscriptSpecification.L043
