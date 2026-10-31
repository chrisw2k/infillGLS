module

public import «L-039-mean-source-common-refinement».SourceCommonRefinement
public import InfillGLSLean.FiniteConditionalError
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Positive definiteness of a finite common-refinement covariance

Source: `the source manuscript`, Appendix `lem:mean` (the finite common
refinement step in lines 554--567).

This file derives, rather than assumes, strict positive definiteness of the
finite covariance on a literal positive-cell common refinement.  It consumes
the source experiment's joint second moment and the existing strict variance
clause for nonzero L2 tests.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L041

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology ProbabilityTheory

universe u v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

open InfillGLSLean.ManuscriptSpecification.L039

/-- The normalized indicator of one cell of a finite positive-cell partition,
viewed as an L2 test function. -/
@[expose] noncomputable def partitionCellAverageTest {N : ℕ}
    (partition : AERegionalPartition μ N) (i : Fin N) : L2TestFunction μ :=
  ⟨(partition.cell i).indicator (fun _ => (μ.real (partition.cell i))⁻¹), by
    apply memLp_indicator_const 2 (partition.measurable_cell i).nullMeasurableSet
    right
    exact measure_ne_top μ (partition.cell i)⟩

/-- Public literal formula for a normalized refinement-cell test.  This is an
API-only `rfl` expansion used to identify the fixed-refinement design entries;
it does not alter the test, covariance condition, or manuscript statement. -/
@[simp] theorem partitionCellAverageTest_apply {N : ℕ}
    (partition : AERegionalPartition μ N) (i : Fin N) (s : Point D) :
    (partitionCellAverageTest partition i).1 s =
      (partition.cell i).indicator (fun _ => (μ.real (partition.cell i))⁻¹) s :=
  rfl

/-- The L2 step test associated with a finite coefficient vector and a
literal finite partition.  In the common-refinement application, `partition`
is the refinement returned by L-039. -/
@[expose] noncomputable def partitionWeightedCellTest {N : ℕ}
    (partition : AERegionalPartition μ N) (weight : Fin N → ℝ) : L2TestFunction μ :=
  ⟨fun s => ∑ i, weight i * (partitionCellAverageTest partition i).1 s, by
    exact memLp_finsetSum Finset.univ fun i _ =>
      (partitionCellAverageTest partition i).2.const_mul (weight i)⟩

/-- Public literal formula for a weighted finite step test.  This is an
API-only `rfl` expansion for the common-refinement covariance calculation;
it changes neither the test construction nor any manuscript condition. -/
@[simp] theorem partitionWeightedCellTest_apply {N : ℕ}
    (partition : AERegionalPartition μ N) (weight : Fin N → ℝ) (s : Point D) :
    (partitionWeightedCellTest partition weight).1 s =
      ∑ i, weight i * (partitionCellAverageTest partition i).1 s :=
  rfl

/-- The random vector of literal regional averages on an arbitrary finite
partition.  This is a derived notation only; it introduces no new observed
map or experiment. -/
@[expose] noncomputable def partitionRegionalErrors
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) : Fin N → Ω → ℝ :=
  fun i ω => cellMean μ (partition.cell i) (E.error ω)

/-- The fixed-law componentwise mean of `partitionRegionalErrors`. -/
@[expose] noncomputable def partitionRegionalErrorMean
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) : Fin N → ℝ :=
  fun i => ∫ ω, partitionRegionalErrors E partition i ω ∂P

/-- The finite covariance of the literal regional-error vector on a derived
partition.  For a common refinement, this is exactly the covariance denoted
by the refinement vector in the proof of Appendix `lem:mean`. -/
@[expose] noncomputable def partitionErrorCovariance
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) : Matrix (Fin N) (Fin N) ℝ :=
  finiteErrorCovariance (partitionRegionalErrors E partition) P

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
@[simp] theorem partitionRegionalErrors_apply
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (i : Fin N) (ω : Ω) :
    partitionRegionalErrors E partition i ω =
      cellMean μ (partition.cell i) (E.error ω) := rfl

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
@[simp] theorem partitionRegionalErrorMean_apply
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (i : Fin N) :
    partitionRegionalErrorMean E partition i =
      ∫ ω, partitionRegionalErrors E partition i ω ∂P := rfl

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
@[simp] theorem partitionErrorCovariance_eq
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) :
    partitionErrorCovariance E partition =
      finiteErrorCovariance (partitionRegionalErrors E partition) P := rfl

/-! ## Source Fubini and centering on a derived finite partition -/

/-- The spatial fixed-law mean is integrable, as a direct consequence of the
source joint second moment already converted to product integrability by
L-039. -/
private theorem conditional_error_mean_integrable
    (E : FixedConditionalExperiment μ P) :
    Integrable (conditionalErrorMean P E.error) μ := by
  change Integrable (fun s => ∫ ω, E.error ω s ∂P) μ
  simpa using (error_product_integrable E).integral_prod_right

/-- Fubini for one literal finite-partition cell.  This is the same
fixed-law compatibility used for observed regions, now applied to the
derived common-refinement cell without adding an observation map. -/
private theorem cellMean_conditionalErrorMean_eq_partitionRegionalErrorMean
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (i : Fin N) :
    cellMean μ (partition.cell i) (conditionalErrorMean P E.error) =
      partitionRegionalErrorMean E partition i := by
  let R : Set (Point D) := partition.cell i
  have hmeasure : P.prod (μ.restrict R) =
      (P.prod μ).restrict (Set.univ ×ˢ R) := by
    calc
      P.prod (μ.restrict R) = (P.restrict Set.univ).prod (μ.restrict R) := by
        rw [Measure.restrict_univ]
      _ = (P.prod μ).restrict (Set.univ ×ˢ R) := by
        rw [Measure.prod_restrict]
  have hrestricted : Integrable
      (fun z : Ω × Point D => E.error z.1 z.2) (P.prod (μ.restrict R)) := by
    rw [hmeasure]
    exact (error_product_integrable E).restrict
  change cellMean μ R (fun s => ∫ ω, E.error ω s ∂P) =
    ∫ ω, cellMean μ R (E.error ω) ∂P
  simp only [cellMean, setAverage_eq]
  rw [integral_smul]
  congr 1
  exact (integral_integral_swap hrestricted).symm

/-- Multiplying a constant indicator by a function is the indicator of the
pointwise product. -/
private theorem indicator_const_mul_eq_indicator
    (R : Set (Point D)) (a : ℝ) (g : Point D → ℝ) :
    (fun s => R.indicator (fun _ => a) s * g s) =
      R.indicator (fun s => a * g s) := by
  funext s
  by_cases hs : s ∈ R <;> simp [hs]

/-- One centered common-refinement regional average is the corresponding
centered spatial test integral, almost surely under the fixed law. -/
private theorem centeredTestIntegral_partitionCell_ae_eq
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (i : Fin N) :
    centeredIntegralProcess μ P E.error (partitionCellAverageTest partition i) =ᵐ[P]
      centeredFiniteError (partitionRegionalErrors E partition)
        (partitionRegionalErrorMean E partition) i := by
  let R : Set (Point D) := partition.cell i
  let a : ℝ := (μ.real R)⁻¹
  have hR : MeasurableSet R := partition.measurable_cell i
  have hm : Integrable (conditionalErrorMean P E.error) (μ.restrict R) :=
    (conditional_error_mean_integrable E).restrict
  have hmean := cellMean_conditionalErrorMean_eq_partitionRegionalErrorMean E partition i
  filter_upwards [error_spatial_integrable_ae E] with ω hω
  have hsub : Integrable (fun s => E.error ω s - conditionalErrorMean P E.error s)
      (μ.restrict R) := hω.integrableOn.sub hm
  rw [centeredIntegralProcess_apply, centeredTestIntegral_apply,
    centeredFiniteError_apply]
  change (∫ s, (partitionCellAverageTest partition i).1 s *
      (E.error ω s - conditionalErrorMean P E.error s) ∂μ) =
      partitionRegionalErrors E partition i ω -
        partitionRegionalErrorMean E partition i
  change (∫ s, R.indicator (fun _ => a) s *
      (E.error ω s - conditionalErrorMean P E.error s) ∂μ) =
      partitionRegionalErrors E partition i ω -
        partitionRegionalErrorMean E partition i
  rw [indicator_const_mul_eq_indicator, integral_indicator hR]
  rw [integral_const_mul, integral_sub hω.integrableOn hm]
  rw [mul_sub]
  have hregional : partitionRegionalErrors E partition i ω =
      a * (∫ s in R, E.error ω s ∂μ) := by
    simp [partitionRegionalErrors, cellMean, setAverage_eq, R, a, smul_eq_mul]
  rw [hregional]
  congr 1
  rw [← hmean]
  simp [cellMean, setAverage_eq, R, a, smul_eq_mul]

/-- The integrand for a normalized common-refinement cell test is integrable
for almost every outcome.  This keeps the following finite-sum Fubini step at
the exact a.e. strength supplied by the source. -/
private theorem partitionCell_centered_integrand_integrable_ae
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (i : Fin N) :
    ∀ᵐ ω ∂P, Integrable (fun s => (partitionCellAverageTest partition i).1 s *
      (E.error ω s - conditionalErrorMean P E.error s)) μ := by
  let R : Set (Point D) := partition.cell i
  let a : ℝ := (μ.real R)⁻¹
  have hR : MeasurableSet R := partition.measurable_cell i
  have hm : Integrable (conditionalErrorMean P E.error) (μ.restrict R) :=
    (conditional_error_mean_integrable E).restrict
  filter_upwards [error_spatial_integrable_ae E] with ω hω
  have hsub : Integrable (fun s => E.error ω s - conditionalErrorMean P E.error s)
      (μ.restrict R) := hω.integrableOn.sub hm
  change Integrable (fun s => R.indicator (fun _ => a) s *
    (E.error ω s - conditionalErrorMean P E.error s)) μ
  rw [indicator_const_mul_eq_indicator, integrable_indicator_iff hR]
  exact hsub.const_mul _

/-- The centered integral for the finite step test is almost everywhere the
coefficient-weighted centered vector of regional errors. -/
theorem centeredTestIntegral_partitionWeighted_ae_eq_score
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (weight : Fin N → ℝ) :
    centeredIntegralProcess μ P E.error (partitionWeightedCellTest partition weight) =ᵐ[P]
      finiteWeightedScore weight
        (centeredFiniteError (partitionRegionalErrors E partition)
          (partitionRegionalErrorMean E partition)) := by
  have hintegrable : ∀ᵐ ω ∂P, ∀ i,
      Integrable (fun s => (partitionCellAverageTest partition i).1 s *
        (E.error ω s - conditionalErrorMean P E.error s)) μ :=
    ae_all_iff.2 fun i =>
      partitionCell_centered_integrand_integrable_ae E partition i
  have hcell : ∀ᵐ ω ∂P, ∀ i,
      centeredIntegralProcess μ P E.error (partitionCellAverageTest partition i) ω =
        centeredFiniteError (partitionRegionalErrors E partition)
          (partitionRegionalErrorMean E partition) i ω :=
    ae_all_iff.2 fun i =>
      centeredTestIntegral_partitionCell_ae_eq E partition i
  filter_upwards [hintegrable, hcell] with ω hInt hCell
  rw [centeredIntegralProcess_apply, centeredTestIntegral_apply]
  change (∫ s, (∑ i, weight i * (partitionCellAverageTest partition i).1 s) *
      (E.error ω s - conditionalErrorMean P E.error s) ∂μ) =
        finiteWeightedScore weight
          (centeredFiniteError (partitionRegionalErrors E partition)
            (partitionRegionalErrorMean E partition)) ω
  have hsum : (fun s => (∑ i, weight i * (partitionCellAverageTest partition i).1 s) *
      (E.error ω s - conditionalErrorMean P E.error s)) =
      fun s => ∑ i, weight i * ((partitionCellAverageTest partition i).1 s *
        (E.error ω s - conditionalErrorMean P E.error s)) := by
    funext s
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, integral_finsetSum]
  · simp only [finiteWeightedScore_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    congr 1
    rw [← centeredTestIntegral_apply, ← centeredIntegralProcess_apply, hCell i]
  · intro i hi
    exact (hInt i).const_mul (weight i)

/-! ## Nonzero coefficient vectors give nonzero L2 tests -/

/-- A nonzero coefficient vector on positive, a.e.-disjoint cells yields a
nonzero spatial step test.  The proof first replaces the source cells by
literal disjoint representatives, so the allowed null overlaps are never
treated as pointwise disjointness. -/
theorem partitionWeightedCellTest_not_ae_zero {N : ℕ}
    (partition : AERegionalPartition μ N) (weight : Fin N → ℝ)
    (hweight : weight ≠ 0) :
    ¬ ((partitionWeightedCellTest partition weight).1 =ᵐ[μ] fun _ => 0) := by
  classical
  intro hzero
  obtain ⟨i, hi⟩ : ∃ i, weight i ≠ 0 := by
    by_contra h
    push Not at h
    apply hweight
    funext j
    exact h j
  obtain ⟨cells, hsubset, hcell, hmeas, hdisjoint⟩ :=
    exists_subordinate_pairwise_disjoint
      (fun j => (partition.measurable_cell j).nullMeasurableSet)
      (by
        intro j k hjk
        exact partition.aedisjoint_cell hjk)
  let g : Point D → ℝ := fun s => ∑ j, weight j *
    (cells j).indicator (fun _ => (μ.real (partition.cell j))⁻¹) s
  have hstep : (partitionWeightedCellTest partition weight).1 =ᵐ[μ] g := by
    change (fun s => ∑ j, weight j *
      (partition.cell j).indicator (fun _ => (μ.real (partition.cell j))⁻¹) s) =ᵐ[μ] g
    dsimp [g]
    have hcellwise : ∀ᵐ s ∂μ, ∀ j,
        (partition.cell j).indicator (fun _ => (μ.real (partition.cell j))⁻¹) s =
          (cells j).indicator (fun _ => (μ.real (partition.cell j))⁻¹) s :=
      ae_all_iff.2 fun j => indicator_ae_eq_of_ae_eq_set (hcell j)
    filter_upwards [hcellwise] with s hs
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j]
  have hzero' : g =ᵐ[μ] fun _ => 0 := hstep.symm.trans hzero
  have hvalue : ∀ s ∈ cells i,
      g s = weight i * (μ.real (partition.cell i))⁻¹ := by
    intro s hs
    dsimp [g]
    rw [Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hs]
    · intro j _ hji
      have hnot : s ∉ cells j :=
        (Set.disjoint_left.mp (hdisjoint hji.symm)) hs
      simp [Set.indicator_of_notMem hnot]
    · simp
  have hmeasure_cells : μ (cells i) = μ (partition.cell i) :=
    (MeasureTheory.measure_congr (hcell i)).symm
  have hcells_ne : μ (cells i) ≠ 0 := by
    rw [hmeasure_cells]
    exact (partition.positive_measure i).ne'
  have hnebot : (ae (μ.restrict (cells i))).NeBot :=
    ae_restrict_neBot.mpr hcells_ne
  have hzero_restrict : ∀ᵐ s ∂μ.restrict (cells i), g s = 0 :=
    ae_restrict_of_ae hzero'
  have hvalue_restrict : ∀ᵐ s ∂μ.restrict (cells i),
      g s = weight i * (μ.real (partition.cell i))⁻¹ :=
    ae_restrict_of_forall_mem (hmeas i) hvalue
  have hconstant_zero : ∀ᵐ s ∂μ.restrict (cells i),
      weight i * (μ.real (partition.cell i))⁻¹ = 0 := by
    filter_upwards [hzero_restrict, hvalue_restrict] with s hs hvalue_s
    rw [← hvalue_s]
    exact hs
  obtain ⟨s, hs⟩ := @Filter.Eventually.exists _ _
    (ae (μ.restrict (cells i))) hnebot hconstant_zero
  have hcell_real_pos : 0 < μ.real (partition.cell i) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (partition.positive_measure i).ne'
      (measure_ne_top μ (partition.cell i))
  exact (mul_ne_zero hi (inv_ne_zero hcell_real_pos.ne')) hs

/-- The preceding literal a.e.-nonvanishing result expressed through the
source's existing `NonzeroInL2` predicate, using only its public `rfl` API. -/
theorem partitionWeightedCellTest_nonzero {N : ℕ}
    (partition : AERegionalPartition μ N) (weight : Fin N → ℝ)
    (hweight : weight ≠ 0) :
    NonzeroInL2 μ (partitionWeightedCellTest partition weight) :=
  (nonzeroInL2_iff μ (partitionWeightedCellTest partition weight)).mpr
    (partitionWeightedCellTest_not_ae_zero partition weight hweight)

/-! ## Finite covariance and variance identities on the refinement -/

/-- The source joint second moment gives square integrability of every
literal refinement-cell average. -/
theorem partitionRegionalErrors_memLp_two
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (i : Fin N) :
    MemLp (partitionRegionalErrors E partition i) 2 P := by
  change MemLp (fun ω => cellMean μ (partition.cell i) (E.error ω)) 2 P
  exact error_cellMean_memLp_two E (partition.cell i)
    (partition.measurable_cell i) (partition.positive_measure i)

/-- Centering a finite vector by its componentwise fixed-law means leaves its
finite covariance matrix unchanged. -/
theorem centered_partitionRegionalErrors_covariance_eq
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) :
    finiteErrorCovariance
      (centeredFiniteError (partitionRegionalErrors E partition)
        (partitionRegionalErrorMean E partition)) P =
      partitionErrorCovariance E partition := by
  ext i j
  rw [partitionErrorCovariance_eq]
  simp only [finiteErrorCovariance_apply]
  change cov[(fun ω => partitionRegionalErrors E partition i ω -
      partitionRegionalErrorMean E partition i),
    (fun ω => partitionRegionalErrors E partition j ω -
      partitionRegionalErrorMean E partition j); P] =
      cov[partitionRegionalErrors E partition i, partitionRegionalErrors E partition j; P]
  rw [covariance_sub_const_left
      ((partitionRegionalErrors_memLp_two E partition i).integrable (by norm_num)),
    covariance_sub_const_right
      ((partitionRegionalErrors_memLp_two E partition j).integrable (by norm_num))]

/-- The finite centered regional-error score has variance equal to the
quadratic form of the literal refinement covariance. -/
theorem variance_partitionWeightedScore_eq_quadraticForm
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (weight : Fin N → ℝ) :
    Var[finiteWeightedScore weight
      (centeredFiniteError (partitionRegionalErrors E partition)
        (partitionRegionalErrorMean E partition)); P] =
      quadraticForm (partitionErrorCovariance E partition) weight := by
  have hcentered : ∀ i, MemLp
      (centeredFiniteError (partitionRegionalErrors E partition)
        (partitionRegionalErrorMean E partition) i) 2 P := by
    intro i
    exact (partitionRegionalErrors_memLp_two E partition i).sub
      (memLp_const (partitionRegionalErrorMean E partition i))
  rw [variance_finiteWeightedScore_eq_quadraticForm weight
    (centeredFiniteError (partitionRegionalErrors E partition)
      (partitionRegionalErrorMean E partition)) hcentered,
    centered_partitionRegionalErrors_covariance_eq]

/-- The centered finite score is in L2 under the source joint second moment. -/
theorem centered_partitionWeightedScore_memLp_two
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (weight : Fin N → ℝ) :
    MemLp (finiteWeightedScore weight
      (centeredFiniteError (partitionRegionalErrors E partition)
        (partitionRegionalErrorMean E partition))) 2 P := by
  apply memLp_finiteWeightedScore
  intro i
  exact (partitionRegionalErrors_memLp_two E partition i).sub
    (memLp_const (partitionRegionalErrorMean E partition i))

/-- The existing strict spatial-test variance is exactly the finite covariance
quadratic form for a weighted common-refinement step test. -/
theorem variance_centeredTestIntegral_partitionWeighted_eq_quadraticForm
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) (weight : Fin N → ℝ) :
    varianceUnder P
      (centeredTestIntegral μ P E.error (partitionWeightedCellTest partition weight)) =
        quadraticForm (partitionErrorCovariance E partition) weight := by
  have hscore_ae :
      centeredTestIntegral μ P E.error (partitionWeightedCellTest partition weight) =ᵐ[P]
        finiteWeightedScore weight
          (centeredFiniteError (partitionRegionalErrors E partition)
            (partitionRegionalErrorMean E partition)) := by
    filter_upwards [centeredTestIntegral_partitionWeighted_ae_eq_score E partition weight]
      with ω hω
    rw [← centeredIntegralProcess_apply]
    exact hω
  have hvariance_congr :
      varianceUnder P (centeredTestIntegral μ P E.error
        (partitionWeightedCellTest partition weight)) =
        varianceUnder P (finiteWeightedScore weight
          (centeredFiniteError (partitionRegionalErrors E partition)
            (partitionRegionalErrorMean E partition))) := by
    rw [varianceUnder_eq, varianceUnder_eq]
    have hmean :
        (∫ ω, centeredTestIntegral μ P E.error
          (partitionWeightedCellTest partition weight) ω ∂P) =
          ∫ ω, finiteWeightedScore weight
            (centeredFiniteError (partitionRegionalErrors E partition)
              (partitionRegionalErrorMean E partition)) ω ∂P :=
      integral_congr_ae hscore_ae
    rw [hmean]
    apply integral_congr_ae
    filter_upwards [hscore_ae] with ω hω
    rw [hω]
  rw [hvariance_congr, varianceUnder_eq, ← variance_eq_integral
    (centered_partitionWeightedScore_memLp_two E partition weight).aemeasurable]
  exact variance_partitionWeightedScore_eq_quadraticForm E partition weight

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The covariance matrix of a literal finite regional vector is Hermitian;
over the reals this is the usual covariance symmetry. -/
theorem partitionErrorCovariance_isHermitian
    (E : FixedConditionalExperiment μ P) {N : ℕ}
    (partition : AERegionalPartition μ N) :
    (partitionErrorCovariance E partition).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [partitionErrorCovariance_eq]
  simp only [finiteErrorCovariance_apply, star_trivial]
  exact covariance_comm _ _

/-- The covariance of the literal error vector on every finite positive-cell
partition is positive definite.  The strictness is not an added finite-vector
assumption: it is obtained by applying the manuscript's existing strict
variance clause to the nonzero L2 step test constructed above. -/
theorem partitionErrorCovariance_posDef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {N : ℕ} (partition : AERegionalPartition μ N) :
    (partitionErrorCovariance E partition).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact partitionErrorCovariance_isHermitian E partition
  · intro weight hweight
    have hpositive : 0 < quadraticForm (partitionErrorCovariance E partition) weight := by
      rw [← variance_centeredTestIntegral_partitionWeighted_eq_quadraticForm
        E partition weight]
      exact covariance.positive_test_variance
        (partitionWeightedCellTest partition weight)
        (partitionWeightedCellTest_nonzero partition weight hweight)
    simpa only [quadraticForm_eq_dotProduct_mulVec, star_trivial] using hpositive

/-- Specialization of positive definiteness to the literal finite common
refinement chosen by L-039. -/
theorem FirstCommonRefinement.partitionErrorCovariance_posDef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {k : ℕ} (W : FirstCommonRefinement E.maps k) :
    (partitionErrorCovariance E W.partition).PosDef :=
  InfillGLSLean.ManuscriptSpecification.L041.partitionErrorCovariance_posDef
    E covariance W.partition

/-- Every source `trueCovariance E n` is positive definite, without adding a
finite-dimensional covariance premise: its cells are the source partition at
resolution `n`, and the generic literal-partition theorem applies directly. -/
theorem trueCovariance_posDef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ) : (trueCovariance E n).PosDef := by
  rw [trueCovariance_eq]
  exact partitionErrorCovariance_posDef E covariance (E.maps.partition n)

end InfillGLSLean.ManuscriptSpecification.L041

end
