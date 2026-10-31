module

public import ManuscriptSpecification
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.Convex.Integral

/-!
# Nonnested regional averaging: exact source target

This proof module formalizes the manuscript's Lemma `lem:averaging` in
`the source manuscript`.  Its operator is the literal function that equals
the regional mean on each cell (up to the source's allowed null overlaps and
null uncovered set).  No nesting or mesh assumption is introduced here.
-/

/-!
The enclosing `module` maintains a stable module boundary. This
public boundary is visibility-only: it exports the already-proved exact
regional projection and `regionalAveraging_tendsto_L2` statements for the
source-faithful Appendix `lem:mean` integration, without changing any
definition, hypothesis, conclusion, or proof body. -/
public section

namespace InfillGLSLean.ManuscriptSpecification.L026

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

universe u

variable {D : CompactEuclideanDomain}
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]

/-- The spatial function obtained by replacing a function with its literal
set average on every cell of one finite regional partition.  On the null set
where source cells overlap or fail to cover, its arbitrary sum value is
irrelevant to the `L²` statement. -/
@[expose]
noncomputable def regionalProjection {N : ℕ}
    (partition : AERegionalPartition μ N) (f : Point D → ℝ) : Point D → ℝ :=
  fun x => ∑ i : Fin N,
    (partition.cell i).indicator (fun _ => cellMean μ (partition.cell i) f) x

@[simp]
theorem regionalProjection_apply {N : ℕ}
    (partition : AERegionalPartition μ N) (f : Point D → ℝ) (x : Point D) :
    regionalProjection partition f x =
      ∑ i : Fin N,
        (partition.cell i).indicator (fun _ => cellMean μ (partition.cell i) f) x := rfl

/-- Finite regional averaging is strongly measurable, independently of the
measurability of the input: each cellwise average is a scalar constant. -/
theorem stronglyMeasurable_regionalProjection {N : ℕ}
    (partition : AERegionalPartition μ N) (f : Point D → ℝ) :
    StronglyMeasurable (regionalProjection partition f) := by
  have hsum : StronglyMeasurable (∑ i : Fin N,
      (partition.cell i).indicator (fun _ => cellMean μ (partition.cell i) f)) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    exact stronglyMeasurable_const.indicator (partition.measurable_cell i)
  have heq : regionalProjection partition f =
      ∑ i : Fin N, (partition.cell i).indicator
        (fun _ => cellMean μ (partition.cell i) f) := by
    funext x
    simp [regionalProjection]
  rw [heq]
  exact hsum

/-- The source's unit-mass union condition says that the cells cover the
domain up to a `μ`-null set. -/
theorem cells_ae_cover {N : ℕ} (partition : AERegionalPartition μ N) :
    (⋃ i, partition.cell i) =ᵐ[μ] Set.univ := by
  rw [ae_eq_univ]
  rw [measure_compl (MeasurableSet.iUnion partition.measurable_cell) (by finiteness),
    IsProbabilityMeasure.measure_univ, partition.union_measure_one]
  norm_num

/-- The a.e.-disjoint source cells have literal disjoint measurable
representatives, with no change outside a null set. -/
theorem exists_disjointized_cells {N : ℕ} (partition : AERegionalPartition μ N) :
    ∃ cells : Fin N → Set (Point D),
      (∀ i, cells i ⊆ partition.cell i) ∧
      (∀ i, partition.cell i =ᵐ[μ] cells i) ∧
      (∀ i, MeasurableSet (cells i)) ∧
      Pairwise (Function.onFun Disjoint cells) := by
  exact exists_subordinate_pairwise_disjoint
    (fun i => (partition.measurable_cell i).nullMeasurableSet)
    (by
      intro i j hij
      exact partition.aedisjoint_cell hij)

/-- The same finite average, written using literal disjoint representatives
of the source cells. -/
noncomputable def disjointRegionalProjection {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (f : Point D → ℝ) : Point D → ℝ :=
  fun x => ∑ i : Fin N,
    (cells i).indicator (fun _ => cellMean μ (partition.cell i) f) x

theorem regionalProjection_ae_eq_disjointRegionalProjection {N : ℕ}
    (partition : AERegionalPartition μ N) (cells : Fin N → Set (Point D))
    (hcell : ∀ i, partition.cell i =ᵐ[μ] cells i) (f : Point D → ℝ) :
    regionalProjection partition f =ᵐ[μ]
      disjointRegionalProjection cells partition f := by
  unfold regionalProjection disjointRegionalProjection
  have hsum : (∑ i : Fin N,
      (partition.cell i).indicator (fun _ => cellMean μ (partition.cell i) f)) =ᵐ[μ]
      ∑ i : Fin N, (cells i).indicator (fun _ => cellMean μ (partition.cell i) f) := by
    exact eventuallyEq_sum fun i _ => indicator_ae_eq_of_ae_eq_set (hcell i)
  filter_upwards [hsum] with x hx
  simpa only [Finset.sum_apply] using hx

private noncomputable def disjointRegionalSquare {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (f : Point D → ℝ) : Point D → ℝ :=
  fun x => ∑ i : Fin N,
    (cells i).indicator (fun _ => (cellMean μ (partition.cell i) f) ^ 2) x

private theorem sq_disjointRegionalProjection {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hdisjoint : Pairwise (Function.onFun Disjoint cells)) (f : Point D → ℝ) :
    (fun x => (disjointRegionalProjection cells partition f x) ^ 2) =
      disjointRegionalSquare cells partition f := by
  classical
  funext x
  by_cases hx : ∃ i, x ∈ cells i
  · obtain ⟨i, hxi⟩ := hx
    have hnotmem : ∀ j : Fin N, j ≠ i → x ∉ cells j := by
      intro j hji hxj
      exact (Set.disjoint_left.mp (hdisjoint hji.symm)) hxi hxj
    have hprojection : disjointRegionalProjection cells partition f x =
        cellMean μ (partition.cell i) f := by
      unfold disjointRegionalProjection
      rw [Finset.sum_eq_single i]
      · simp [Set.indicator_of_mem hxi]
      · intro j _ hji
        simp [Set.indicator_of_notMem (hnotmem j hji)]
      · simp
    have hsquare : disjointRegionalSquare cells partition f x =
        (cellMean μ (partition.cell i) f) ^ 2 := by
      unfold disjointRegionalSquare
      rw [Finset.sum_eq_single i]
      · simp [Set.indicator_of_mem hxi]
      · intro j _ hji
        simp [Set.indicator_of_notMem (hnotmem j hji)]
      · simp
    rw [hprojection, hsquare]
  · have hnotmem : ∀ j : Fin N, x ∉ cells j := by
      intro j hxj
      exact hx ⟨j, hxj⟩
    unfold disjointRegionalProjection disjointRegionalSquare
    simp [hnotmem]

private theorem integral_disjointRegionalSquare {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hmeas : ∀ i, MeasurableSet (cells i)) (f : Point D → ℝ) :
    (∫ x, disjointRegionalSquare cells partition f x ∂μ) =
      ∑ i : Fin N, μ.real (cells i) * (cellMean μ (partition.cell i) f) ^ 2 := by
  classical
  unfold disjointRegionalSquare
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator (hmeas i), setIntegral_const]
    simp [smul_eq_mul]
  · intro i hi
    exact (integrable_const _).indicator (hmeas i)

/-- Jensen's inequality on one source cell.  This is the finite-cell
ingredient behind the manuscript's `L²` contraction assertion. -/
theorem cellMean_sq_le_cellMean_sq {N : ℕ} (partition : AERegionalPartition μ N)
    {f : Point D → ℝ} (hf : MemLp f 2 μ) (i : Fin N) :
    (cellMean μ (partition.cell i) f) ^ 2 ≤
      cellMean μ (partition.cell i) (fun x => (f x) ^ 2) := by
  have hf_int : Integrable f μ := hf.integrable (by norm_num)
  have hfsq_int : Integrable (fun x => (f x) ^ 2) μ := hf.integrable_sq
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
    exact (by norm_num : Even 2).convexOn_pow
  exact hconv.map_set_average_le (continuous_pow 2).continuousOn isClosed_univ
    (partition.positive_measure i).ne' (measure_ne_top μ (partition.cell i))
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    hf_int.integrableOn (by simpa [Function.comp_def] using hfsq_int.integrableOn)

private theorem weighted_cellMean_sq_le_setIntegral {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hcell : ∀ i, partition.cell i =ᵐ[μ] cells i)
    {f : Point D → ℝ} (hf : MemLp f 2 μ) (i : Fin N) :
    μ.real (cells i) * (cellMean μ (partition.cell i) f) ^ 2 ≤
      ∫ x in cells i, (f x) ^ 2 ∂μ := by
  calc
    μ.real (cells i) * (cellMean μ (partition.cell i) f) ^ 2 =
        μ.real (partition.cell i) * (cellMean μ (partition.cell i) f) ^ 2 := by
          rw [measureReal_congr (hcell i)]
    _ ≤ μ.real (partition.cell i) *
        cellMean μ (partition.cell i) (fun x => (f x) ^ 2) := by
          exact mul_le_mul_of_nonneg_left (cellMean_sq_le_cellMean_sq partition hf i)
            ENNReal.toReal_nonneg
    _ = ∫ x in partition.cell i, (f x) ^ 2 ∂μ := by
          simpa [cellMean, smul_eq_mul] using
            (measure_smul_setAverage (μ := μ) (fun x => (f x) ^ 2)
              (measure_ne_top μ (partition.cell i)))
    _ = ∫ x in cells i, (f x) ^ 2 ∂μ := by
          change (∫ x, (f x) ^ 2 ∂(μ.restrict (partition.cell i))) =
            ∫ x, (f x) ^ 2 ∂(μ.restrict (cells i))
          rw [Measure.restrict_congr_set (hcell i)]

private theorem sum_setIntegral_sq_eq_integral_sq {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hcell : ∀ i, partition.cell i =ᵐ[μ] cells i)
    (hmeas : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (Function.onFun Disjoint cells))
    {f : Point D → ℝ} (hf : MemLp f 2 μ) :
    (∑ i : Fin N, ∫ x in cells i, (f x) ^ 2 ∂μ) = ∫ x, (f x) ^ 2 ∂μ := by
  have hunion : (⋃ i, cells i) =ᵐ[μ] Set.univ :=
    (Filter.EventuallyEq.iUnion fun i => (hcell i).symm).trans (cells_ae_cover partition)
  have hrestrict : μ.restrict (⋃ i, cells i) = μ := by
    rw [Measure.restrict_congr_set hunion, Measure.restrict_univ]
  have hsplit :
      (∫ x in ⋃ i, cells i, (f x) ^ 2 ∂μ) =
        ∑' i : Fin N, ∫ x in cells i, (f x) ^ 2 ∂μ :=
    integral_iUnion_ae (fun i => (hmeas i).nullMeasurableSet) hdisjoint.aedisjoint
      hf.integrable_sq.integrableOn
  symm
  calc
    (∫ x, (f x) ^ 2 ∂μ) = ∫ x in ⋃ i, cells i, (f x) ^ 2 ∂μ := by
      change (∫ x, (f x) ^ 2 ∂μ) = ∫ x, (f x) ^ 2 ∂(μ.restrict (⋃ i, cells i))
      rw [hrestrict]
    _ = ∑' i : Fin N, ∫ x in cells i, (f x) ^ 2 ∂μ := hsplit
    _ = ∑ i : Fin N, ∫ x in cells i, (f x) ^ 2 ∂μ := by
      rw [tsum_fintype]

private theorem disjointRegionalProjection_sq_integral_le {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hcell : ∀ i, partition.cell i =ᵐ[μ] cells i)
    (hmeas : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (Function.onFun Disjoint cells))
    {f : Point D → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, (disjointRegionalProjection cells partition f x) ^ 2 ∂μ) ≤
      ∫ x, (f x) ^ 2 ∂μ := by
  calc
    (∫ x, (disjointRegionalProjection cells partition f x) ^ 2 ∂μ) =
        ∫ x, disjointRegionalSquare cells partition f x ∂μ := by
          rw [sq_disjointRegionalProjection cells partition hdisjoint]
    _ = ∑ i : Fin N, μ.real (cells i) * (cellMean μ (partition.cell i) f) ^ 2 :=
      integral_disjointRegionalSquare cells partition hmeas f
    _ ≤ ∑ i : Fin N, ∫ x in cells i, (f x) ^ 2 ∂μ := by
      apply Finset.sum_le_sum
      intro i hi
      exact weighted_cellMean_sq_le_setIntegral cells partition hcell hf i
    _ = ∫ x, (f x) ^ 2 ∂μ :=
      sum_setIntegral_sq_eq_integral_sq cells partition hcell hmeas hdisjoint hf

/-- Literal regional averaging is an `L²` contraction in squared-integral
form, under exactly the source's finite a.e.-partition conditions. -/
theorem regionalProjection_sq_integral_le {N : ℕ} (partition : AERegionalPartition μ N)
    {f : Point D → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, (regionalProjection partition f x) ^ 2 ∂μ) ≤ ∫ x, (f x) ^ 2 ∂μ := by
  rcases exists_disjointized_cells partition with ⟨cells, hsubset, hcell, hmeas, hdisjoint⟩
  have hprojection : regionalProjection partition f =ᵐ[μ]
      disjointRegionalProjection cells partition f :=
    regionalProjection_ae_eq_disjointRegionalProjection partition cells hcell f
  have hsq : (fun x => (regionalProjection partition f x) ^ 2) =ᵐ[μ]
      fun x => (disjointRegionalProjection cells partition f x) ^ 2 := by
    filter_upwards [hprojection] with x hx
    rw [hx]
  calc
    (∫ x, (regionalProjection partition f x) ^ 2 ∂μ) =
        ∫ x, (disjointRegionalProjection cells partition f x) ^ 2 ∂μ :=
      integral_congr_ae hsq
    _ ≤ ∫ x, (f x) ^ 2 ∂μ :=
      disjointRegionalProjection_sq_integral_le cells partition hcell hmeas hdisjoint hf

/-- Regional averaging commutes with subtraction for integrable inputs. -/
theorem regionalProjection_sub {N : ℕ} (partition : AERegionalPartition μ N)
    {f g : Point D → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    regionalProjection partition (f - g) = regionalProjection partition f -
      regionalProjection partition g := by
  have hmean : ∀ i : Fin N,
      cellMean μ (partition.cell i) (f - g) =
        cellMean μ (partition.cell i) f - cellMean μ (partition.cell i) g := by
    intro i
    unfold cellMean
    exact setAverage_sub hf.integrableOn hg.integrableOn
  funext x
  unfold regionalProjection
  simp_rw [hmean]
  simp only [Pi.sub_apply, Set.indicator_apply]
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext i
  by_cases hx : x ∈ partition.cell i <;> simp [hx]

/-- The source's regional-mean operator contracts pairwise `L²` errors. -/
theorem regionalProjection_error_sq_integral_le {N : ℕ}
    (partition : AERegionalPartition μ N) {f g : Point D → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, (regionalProjection partition f x - regionalProjection partition g x) ^ 2 ∂μ) ≤
      ∫ x, (f x - g x) ^ 2 ∂μ := by
  have hsub : regionalProjection partition (f - g) = regionalProjection partition f -
      regionalProjection partition g :=
    regionalProjection_sub partition (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
  calc
    (∫ x, (regionalProjection partition f x - regionalProjection partition g x) ^ 2 ∂μ) =
        ∫ x, (regionalProjection partition (f - g) x) ^ 2 ∂μ := by
          rw [hsub]
          simp only [Pi.sub_apply]
    _ ≤ ∫ x, ((f - g) x) ^ 2 ∂μ :=
      regionalProjection_sq_integral_le partition (hf.sub hg)
    _ = ∫ x, (f x - g x) ^ 2 ∂μ := rfl

/-! ## `L²` membership of the literal averaging operator -/

private theorem integrable_disjointRegionalSquare {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hmeas : ∀ i, MeasurableSet (cells i)) (f : Point D → ℝ) :
    Integrable (disjointRegionalSquare cells partition f) μ := by
  classical
  unfold disjointRegionalSquare
  apply integrable_finsetSum
  intro i hi
  exact (integrable_const _).indicator (hmeas i)

private theorem integrable_sq_disjointRegionalProjection {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hmeas : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (Function.onFun Disjoint cells)) (f : Point D → ℝ) :
    Integrable (fun x => (disjointRegionalProjection cells partition f x) ^ 2) μ := by
  rw [sq_disjointRegionalProjection cells partition hdisjoint]
  exact integrable_disjointRegionalSquare cells partition hmeas f

/-- A finite regional-average function belongs to `L²` whenever its input
does.  This is retained separately because the final density argument needs
the literal source operator, not an abstract conditional expectation. -/
theorem memLp_regionalProjection {N : ℕ} (partition : AERegionalPartition μ N)
    {f : Point D → ℝ} (hf : MemLp f 2 μ) :
    MemLp (regionalProjection partition f) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (stronglyMeasurable_regionalProjection partition f).aestronglyMeasurable).2
  rcases exists_disjointized_cells partition with ⟨cells, hsubset, hcell, hmeas, hdisjoint⟩
  have hprojection : regionalProjection partition f =ᵐ[μ]
      disjointRegionalProjection cells partition f :=
    regionalProjection_ae_eq_disjointRegionalProjection partition cells hcell f
  have hsq : (fun x => (disjointRegionalProjection cells partition f x) ^ 2) =ᵐ[μ]
      fun x => (regionalProjection partition f x) ^ 2 := by
    filter_upwards [hprojection] with x hx
    rw [hx]
  exact (integrable_sq_disjointRegionalProjection cells partition hmeas hdisjoint f).congr hsq

/-! ## Cellwise bounds for bounded continuous approximants -/

private theorem norm_cellMean_sub_le_of_forall {R : Set (Point D)}
    (hR_pos : 0 < μ R) (hR_meas : MeasurableSet R) {g : Point D → ℝ}
    (hg : Integrable g μ) (x : Point D) {ε : ℝ}
    (hbound : ∀ y ∈ R, ‖g y - g x‖ ≤ ε) :
    ‖cellMean μ R g - g x‖ ≤ ε := by
  have hmember : cellMean μ R (fun y => g y - g x) ∈ Metric.closedBall 0 ε := by
    refine (convex_closedBall (0 : ℝ) ε).set_average_mem Metric.isClosed_closedBall
      hR_pos.ne' (measure_ne_top μ R) ?_ (hg.sub (integrable_const _)).integrableOn
    refine (ae_restrict_iff' hR_meas).2 (Filter.Eventually.of_forall ?_)
    intro y hy
    simpa only [mem_closedBall_zero_iff] using hbound y hy
  have hmean : cellMean μ R g - g x = cellMean μ R (fun y => g y - g x) := by
    unfold cellMean
    calc
      (⨍ y in R, g y ∂μ) - g x =
          (⨍ y in R, g y ∂μ) - ⨍ _y in R, g x ∂μ := by
            rw [setAverage_const hR_pos.ne' (measure_ne_top μ R)]
      _ = ⨍ y in R, (fun y => g y - g x) y ∂μ := by
        simpa only [Pi.sub_apply] using
          (setAverage_sub (μ := μ) (s := R) (f := g) (g := fun _y => g x)
            hg.integrableOn (integrable_const _).integrableOn).symm
  rw [hmean]
  simpa only [mem_closedBall_zero_iff] using hmember

/-- The disjoint representative cells carrying regions whose *source* cell
has diameter larger than `h`.  It is a scalar indicator, so its integral is
exactly the aggregate large-cell mass occurring in `RegionalMaps`. -/
private noncomputable def badCellIndicator {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (h : ℝ) : Point D → ℝ :=
  fun x => ∑ i : Fin N,
    if h < Metric.diam (partition.cell i)
    then (cells i).indicator (fun _ => (1 : ℝ)) x else 0

private theorem integrable_badCellIndicator {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hmeas : ∀ i, MeasurableSet (cells i)) (h : ℝ) :
    Integrable (badCellIndicator cells partition h) μ := by
  classical
  unfold badCellIndicator
  apply integrable_finsetSum
  intro i hi
  by_cases hbad : h < Metric.diam (partition.cell i)
  · simp only [hbad, ↓reduceIte]
    exact (integrable_const _).indicator (hmeas i)
  · simp [hbad]

private theorem integral_badCellIndicator {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hmeas : ∀ i, MeasurableSet (cells i)) (h : ℝ) :
    (∫ x, badCellIndicator cells partition h x ∂μ) =
      ∑ i : Fin N, if h < Metric.diam (partition.cell i) then μ.real (cells i) else 0 := by
  classical
  unfold badCellIndicator
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hbad : h < Metric.diam (partition.cell i)
    · simp [hbad, integral_indicator (hmeas i), setIntegral_const, smul_eq_mul]
    · simp [hbad]
  · intro i hi
    by_cases hbad : h < Metric.diam (partition.cell i)
    · simp only [hbad, ↓reduceIte]
      exact (integrable_const _).indicator (hmeas i)
    · simp [hbad]

private theorem integral_badCellIndicator_eq_source {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hcell : ∀ i, partition.cell i =ᵐ[μ] cells i)
    (hmeas : ∀ i, MeasurableSet (cells i)) (h : ℝ) :
    (∫ x, badCellIndicator cells partition h x ∂μ) =
      ∑ i : Fin N,
        if h < Metric.diam (partition.cell i) then μ.real (partition.cell i) else 0 := by
  rw [integral_badCellIndicator cells partition hmeas h]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hbad : h < Metric.diam (partition.cell i)
  · simp [hbad, measureReal_congr (hcell i)]
  · simp [hbad]

private theorem badCellIndicator_nonneg {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (h : ℝ) (x : Point D) :
    0 ≤ badCellIndicator cells partition h x := by
  classical
  unfold badCellIndicator
  apply Finset.sum_nonneg
  intro i hi
  by_cases hbad : h < Metric.diam (partition.cell i)
  · simp only [hbad, ↓reduceIte]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · simp [hbad]

private theorem disjointRegionalProjection_eq_cellMean_of_mem {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hdisjoint : Pairwise (Function.onFun Disjoint cells))
    {f : Point D → ℝ} {i : Fin N} {x : Point D} (hxi : x ∈ cells i) :
    disjointRegionalProjection cells partition f x = cellMean μ (partition.cell i) f := by
  classical
  have hnotmem : ∀ j : Fin N, j ≠ i → x ∉ cells j := by
    intro j hji hxj
    exact (Set.disjoint_left.mp (hdisjoint hji.symm)) hxi hxj
  unfold disjointRegionalProjection
  rw [Finset.sum_eq_single i]
  · simp [Set.indicator_of_mem hxi]
  · intro j _ hji
    simp [Set.indicator_of_notMem (hnotmem j hji)]
  · simp

private theorem badCellIndicator_eq_of_mem {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hdisjoint : Pairwise (Function.onFun Disjoint cells))
    (h : ℝ) {i : Fin N} {x : Point D} (hxi : x ∈ cells i) :
    badCellIndicator cells partition h x =
      if h < Metric.diam (partition.cell i) then 1 else 0 := by
  classical
  have hnotmem : ∀ j : Fin N, j ≠ i → x ∉ cells j := by
    intro j hji hxj
    exact (Set.disjoint_left.mp (hdisjoint hji.symm)) hxi hxj
  unfold badCellIndicator
  rw [Finset.sum_eq_single i]
  · by_cases hbad : h < Metric.diam (partition.cell i)
    · simp [hbad, Set.indicator_of_mem hxi]
    · simp [hbad]
  · intro j _ hji
    by_cases hbad : h < Metric.diam (partition.cell j)
    · simp [hbad, Set.indicator_of_notMem (hnotmem j hji)]
    · simp [hbad]
  · simp

private theorem disjointRegionalProjection_error_sq_le_badCellIndicator {N : ℕ}
    (cells : Fin N → Set (Point D)) (partition : AERegionalPartition μ N)
    (hsubset : ∀ i, cells i ⊆ partition.cell i)
    (hcell : ∀ i, partition.cell i =ᵐ[μ] cells i)
    (hdisjoint : Pairwise (Function.onFun Disjoint cells))
    (g : Point D → ℝ) (hg : Integrable g μ) (B ε h : ℝ)
    (hB_nonneg : 0 ≤ B) (hε_nonneg : 0 ≤ ε)
    (hB : ∀ x, ‖g x‖ ≤ B)
    (hgood : ∀ (i : Fin N) (x y : Point D), x ∈ partition.cell i →
      y ∈ partition.cell i → Metric.diam (partition.cell i) ≤ h → ‖g y - g x‖ ≤ ε) :
    (fun x => (disjointRegionalProjection cells partition g x - g x) ^ 2) ≤ᵐ[μ]
      fun x => ε ^ 2 + (2 * B) ^ 2 * badCellIndicator cells partition h x := by
  have hunion : (⋃ i, cells i) =ᵐ[μ] Set.univ :=
    (Filter.EventuallyEq.iUnion fun i => (hcell i).symm).trans (cells_ae_cover partition)
  filter_upwards [hunion] with x hx
  have hxunion : x ∈ ⋃ i, cells i := by
    exact Eq.mpr hx trivial
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxunion
  have hprojection : disjointRegionalProjection cells partition g x =
      cellMean μ (partition.cell i) g :=
    disjointRegionalProjection_eq_cellMean_of_mem cells partition hdisjoint hxi
  by_cases hbad : h < Metric.diam (partition.cell i)
  · have hlocal : ‖cellMean μ (partition.cell i) g - g x‖ ≤ 2 * B := by
      apply norm_cellMean_sub_le_of_forall (partition.positive_measure i)
        (partition.measurable_cell i) hg
      intro y hy
      calc
        ‖g y - g x‖ ≤ ‖g y‖ + ‖g x‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hB y) (hB x)
        _ = 2 * B := by ring
    have hsq : (cellMean μ (partition.cell i) g - g x) ^ 2 ≤ (2 * B) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg (by norm_num) hB_nonneg)]
      simpa [Real.norm_eq_abs] using hlocal
    rw [hprojection, badCellIndicator_eq_of_mem cells partition hdisjoint h hxi]
    simp only [hbad, ↓reduceIte, mul_one]
    exact hsq.trans (le_add_of_nonneg_left (sq_nonneg ε))
  · have hdiam : Metric.diam (partition.cell i) ≤ h := le_of_not_gt hbad
    have hlocal : ‖cellMean μ (partition.cell i) g - g x‖ ≤ ε := by
      apply norm_cellMean_sub_le_of_forall (partition.positive_measure i)
        (partition.measurable_cell i) hg
      intro y hy
      exact hgood i x y (hsubset i hxi) hy hdiam
    have hsq : (cellMean μ (partition.cell i) g - g x) ^ 2 ≤ ε ^ 2 := by
      rw [sq_le_sq]
      simpa [Real.norm_eq_abs, abs_of_nonneg hε_nonneg] using hlocal
    rw [hprojection]
    exact hsq.trans (le_add_of_nonneg_right
      (mul_nonneg (sq_nonneg _) (badCellIndicator_nonneg cells partition h x)))

private theorem regionalProjection_error_sq_integral_le_continuous_bound {N : ℕ}
    (partition : AERegionalPartition μ N) (g : Point D → ℝ) (hg : Integrable g μ)
    (B ε h : ℝ) (hB_nonneg : 0 ≤ B) (hε_nonneg : 0 ≤ ε)
    (hB : ∀ x, ‖g x‖ ≤ B)
    (hgood : ∀ (i : Fin N) (x y : Point D), x ∈ partition.cell i →
      y ∈ partition.cell i → Metric.diam (partition.cell i) ≤ h → ‖g y - g x‖ ≤ ε) :
    (∫ x, (regionalProjection partition g x - g x) ^ 2 ∂μ) ≤
      ε ^ 2 + (2 * B) ^ 2 *
        (∑ i : Fin N,
          if h < Metric.diam (partition.cell i) then μ.real (partition.cell i) else 0) := by
  rcases exists_disjointized_cells partition with ⟨cells, hsubset, hcell, hmeas, hdisjoint⟩
  have hprojection : regionalProjection partition g =ᵐ[μ]
      disjointRegionalProjection cells partition g :=
    regionalProjection_ae_eq_disjointRegionalProjection partition cells hcell g
  have herr : (fun x => (regionalProjection partition g x - g x) ^ 2) =ᵐ[μ]
      fun x => (disjointRegionalProjection cells partition g x - g x) ^ 2 := by
    filter_upwards [hprojection] with x hx
    rw [hx]
  have hpoint := disjointRegionalProjection_error_sq_le_badCellIndicator
    cells partition hsubset hcell hdisjoint g hg B ε h hB_nonneg hε_nonneg hB hgood
  have hbad_int := integrable_badCellIndicator cells partition hmeas h
  have hupper_int : Integrable
      (fun x => ε ^ 2 + (2 * B) ^ 2 * badCellIndicator cells partition h x) μ := by
    exact (integrable_const _).add (hbad_int.const_mul _)
  calc
    (∫ x, (regionalProjection partition g x - g x) ^ 2 ∂μ) =
        ∫ x, (disjointRegionalProjection cells partition g x - g x) ^ 2 ∂μ :=
      integral_congr_ae herr
    _ ≤ ∫ x, ε ^ 2 + (2 * B) ^ 2 * badCellIndicator cells partition h x ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hupper_int hpoint
    _ = ε ^ 2 + (2 * B) ^ 2 *
        (∑ i : Fin N,
          if h < Metric.diam (partition.cell i) then μ.real (partition.cell i) else 0) := by
      rw [integral_add (integrable_const _) (hbad_int.const_mul _), integral_const,
        integral_const_mul, integral_badCellIndicator_eq_source cells partition hcell hmeas h]
      simp [smul_eq_mul]

private theorem largeCellMass_nonneg {N : ℕ} (partition : AERegionalPartition μ N)
    (h : ℝ) :
    0 ≤ ∑ i : Fin N,
      if h < Metric.diam (partition.cell i) then μ.real (partition.cell i) else 0 := by
  apply Finset.sum_nonneg
  intro i hi
  by_cases hbad : h < Metric.diam (partition.cell i)
  · simp [hbad, ENNReal.toReal_nonneg]
  · simp [hbad]

private theorem continuousMap_regionalProjection_error_sq_tendsto
    (maps : RegionalMaps μ) (g : C(Point D, ℝ)) :
    Tendsto
      (fun n => ∫ x, (regionalProjection (maps.partition n) (g : Point D → ℝ) x - g x) ^ 2 ∂μ)
      atTop (nhds 0) := by
  letI : CompactSpace (Point D) := isCompact_iff_compactSpace.mp D.compact_carrier
  have hg : MemLp (g : Point D → ℝ) 2 μ := g.memLp μ ℝ
  have huc : UniformContinuous (g : Point D → ℝ) :=
    CompactSpace.uniformContinuous_of_continuous g.continuous
  refine Metric.tendsto_atTop.mpr ?_
  intro η hη
  let a : ℝ := √(η / 2)
  have ha_pos : 0 < a := by
    dsimp [a]
    apply Real.sqrt_pos.2
    linarith
  obtain ⟨δ, hδ_pos, hδ⟩ := (Metric.uniformContinuous_iff_le.mp huc) a ha_pos
  let mass : ℕ → ℝ := fun n => ∑ i : Fin (maps.N n),
    if δ < Metric.diam ((maps.partition n).cell i)
    then μ.real ((maps.partition n).cell i) else 0
  have hmass : Tendsto mass atTop (nhds 0) := by
    simpa only [mass] using maps.large_cell_mass_tendsto δ hδ_pos
  have hscaled : Tendsto (fun n => (2 * ‖g‖) ^ 2 * mass n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hmass)
  have hscaled_event : ∀ᶠ n in atTop,
      dist ((2 * ‖g‖) ^ 2 * mass n) 0 < η / 2 :=
    (Metric.tendsto_nhds.mp hscaled) (η / 2) (by linarith)
  rcases (eventually_atTop.1 hscaled_event) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hmass_nonneg : 0 ≤ mass n := by
    dsimp [mass]
    exact largeCellMass_nonneg (maps.partition n) δ
  have hscaled_nonneg : 0 ≤ (2 * ‖g‖) ^ 2 * mass n :=
    mul_nonneg (sq_nonneg _) hmass_nonneg
  have hscaled_lt : (2 * ‖g‖) ^ 2 * mass n < η / 2 := by
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hscaled_nonneg] at hdist
    exact hdist
  have hgood : ∀ (i : Fin (maps.N n)) (x y : Point D),
      x ∈ (maps.partition n).cell i → y ∈ (maps.partition n).cell i →
      Metric.diam ((maps.partition n).cell i) ≤ δ → ‖g y - g x‖ ≤ a := by
    intro i x y hx hy hdiam
    have hdist : dist y x ≤ δ :=
      (Metric.dist_le_diam_of_mem
        (isCompact_univ.isBounded.subset (subset_univ _)) hy hx).trans hdiam
    rw [Real.norm_eq_abs]
    simpa only [Real.dist_eq] using hδ hdist
  have hbound := regionalProjection_error_sq_integral_le_continuous_bound
    (maps.partition n) (g : Point D → ℝ) (hg.integrable (by norm_num)) ‖g‖ a δ
    (norm_nonneg _) (Real.sqrt_nonneg _) (fun x => g.norm_coe_le_norm x) hgood
  have herror_nonneg : 0 ≤
      ∫ x, (regionalProjection (maps.partition n) (g : Point D → ℝ) x - g x) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have herror_lt :
      (∫ x, (regionalProjection (maps.partition n) (g : Point D → ℝ) x - g x) ^ 2 ∂μ) < η := by
    calc
      (∫ x, (regionalProjection (maps.partition n) (g : Point D → ℝ) x - g x) ^ 2 ∂μ) ≤
          a ^ 2 + (2 * ‖g‖) ^ 2 * mass n := by
            simpa only [mass] using hbound
      _ = η / 2 + (2 * ‖g‖) ^ 2 * mass n := by
        dsimp [a]
        rw [Real.sq_sqrt]
        linarith
      _ < η := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg herror_nonneg]
  exact herror_lt

/-! ## The literal spatial `L²` norm -/

private theorem lpNorm_two_eq_sqrt_integral_sq {f : Point D → ℝ}
    (hf : MemLp f 2 μ) :
    lpNorm f 2 μ = √(∫ x, (f x) ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp)
    hf.aestronglyMeasurable]
  simp [Real.sqrt_eq_rpow]

private theorem lpNorm_regionalProjection_error_le {N : ℕ}
    (partition : AERegionalPartition μ N) {f g : Point D → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    lpNorm (regionalProjection partition f - regionalProjection partition g) 2 μ ≤
      lpNorm (f - g) 2 μ := by
  rw [lpNorm_two_eq_sqrt_integral_sq
      ((memLp_regionalProjection partition hf).sub (memLp_regionalProjection partition hg)),
    lpNorm_two_eq_sqrt_integral_sq (hf.sub hg)]
  exact Real.sqrt_le_sqrt (regionalProjection_error_sq_integral_le partition hf hg)

private theorem continuousMap_regionalProjection_error_tendsto
    (maps : RegionalMaps μ) (g : C(Point D, ℝ)) :
    Tendsto
      (fun n => lpNorm
        (regionalProjection (maps.partition n) (g : Point D → ℝ) -
          (g : Point D → ℝ)) 2 μ)
      atTop (nhds 0) := by
  letI : CompactSpace (Point D) := isCompact_iff_compactSpace.mp D.compact_carrier
  have hsq := continuousMap_regionalProjection_error_sq_tendsto maps g
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  convert hroot using 1
  · funext n
    rw [lpNorm_two_eq_sqrt_integral_sq
      ((memLp_regionalProjection (maps.partition n) (g.memLp μ ℝ)).sub
        (g.memLp μ ℝ))]
    rfl
  · simp

private theorem lpNorm_sub_le_of_integral_norm_sq_le
    {f g : Point D → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {ε : ℝ} (hε : 0 < ε)
    (hfg : (∫ x, ‖f x - g x‖ ^ (2 : ℝ) ∂μ) ≤ (ε / 4) ^ 2) :
    lpNorm (f - g) 2 μ ≤ ε / 4 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp)
    (hf.sub hg).aestronglyMeasurable]
  calc
    (∫ x, ‖(f - g) x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) =
        √(∫ x, (f x - g x) ^ 2 ∂μ) := by
          simp [Real.sqrt_eq_rpow]
    _ ≤ √((ε / 4) ^ 2) :=
      Real.sqrt_le_sqrt (by simpa [Real.norm_eq_abs] using hfg)
    _ = ε / 4 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      linarith

private theorem regionalProjection_error_tendsto
    (maps : RegionalMaps μ) (f : Point D → ℝ) (hf : MemLp f 2 μ) :
    Tendsto (fun n => lpNorm (regionalProjection (maps.partition n) f - f) 2 μ)
      atTop (nhds 0) := by
  letI : CompactSpace (Point D) := isCompact_iff_compactSpace.mp D.compact_carrier
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hε_fourth : 0 < ε / 4 := by linarith
  have hε_sq : 0 < (ε / 4) ^ 2 := sq_pos_of_pos hε_fourth
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf
  obtain ⟨g, hfg_sq, hg⟩ := hf'.exists_boundedContinuous_integral_rpow_sub_le
    (p := (2 : ℝ)) (by norm_num) hε_sq
  have hfg_small : lpNorm (f - (g : Point D → ℝ)) 2 μ ≤ ε / 4 :=
    lpNorm_sub_le_of_integral_norm_sq_le hf (by simpa using hg) hε
      (by simpa using hfg_sq)
  have hcontinuous :=
    continuousMap_regionalProjection_error_tendsto maps g.toContinuousMap
  have hcontinuous_event : ∀ᶠ n in atTop,
      dist (lpNorm
        (regionalProjection (maps.partition n) (g : Point D → ℝ) -
          (g : Point D → ℝ)) 2 μ) 0 < ε / 4 :=
    (Metric.tendsto_nhds.mp hcontinuous) (ε / 4) hε_fourth
  rcases (eventually_atTop.1 hcontinuous_event) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hcontinuous_small : lpNorm
      (regionalProjection (maps.partition n) (g : Point D → ℝ) -
        (g : Point D → ℝ)) 2 μ < ε / 4 := by
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg lpNorm_nonneg] at hdist
    exact hdist
  have hprojection_small : lpNorm
      (regionalProjection (maps.partition n) f -
        regionalProjection (maps.partition n) (g : Point D → ℝ)) 2 μ ≤ ε / 4 :=
    (lpNorm_regionalProjection_error_le (maps.partition n) hf (by simpa using hg)).trans
      hfg_small
  have hreverse_small : lpNorm ((g : Point D → ℝ) - f) 2 μ ≤ ε / 4 := by
    rw [← lpNorm_sub_comm f (g : Point D → ℝ) 2 μ]
    exact hfg_small
  have hprojection_mem : MemLp
      (regionalProjection (maps.partition n) f -
        regionalProjection (maps.partition n) (g : Point D → ℝ)) 2 μ :=
    (memLp_regionalProjection (maps.partition n) hf).sub
      (memLp_regionalProjection (maps.partition n) (by simpa using hg))
  have hcontinuous_mem : MemLp
      (regionalProjection (maps.partition n) (g : Point D → ℝ) -
        (g : Point D → ℝ)) 2 μ :=
    (memLp_regionalProjection (maps.partition n) (by simpa using hg)).sub
      (by simpa using hg)
  have hsum_mem := hprojection_mem.add hcontinuous_mem
  have htriangle : lpNorm (regionalProjection (maps.partition n) f - f) 2 μ ≤
      lpNorm
        (regionalProjection (maps.partition n) f -
          regionalProjection (maps.partition n) (g : Point D → ℝ)) 2 μ +
        lpNorm
          (regionalProjection (maps.partition n) (g : Point D → ℝ) -
            (g : Point D → ℝ)) 2 μ +
        lpNorm ((g : Point D → ℝ) - f) 2 μ := by
    calc
      lpNorm (regionalProjection (maps.partition n) f - f) 2 μ =
          lpNorm
            ((regionalProjection (maps.partition n) f -
                regionalProjection (maps.partition n) (g : Point D → ℝ)) +
              (regionalProjection (maps.partition n) (g : Point D → ℝ) -
                (g : Point D → ℝ)) + ((g : Point D → ℝ) - f)) 2 μ := by
              congr 1
              funext x
              simp only [Pi.add_apply, Pi.sub_apply]
              ring
      _ ≤ lpNorm
          ((regionalProjection (maps.partition n) f -
              regionalProjection (maps.partition n) (g : Point D → ℝ)) +
            (regionalProjection (maps.partition n) (g : Point D → ℝ) -
              (g : Point D → ℝ))) 2 μ +
          lpNorm ((g : Point D → ℝ) - f) 2 μ :=
            lpNorm_add_le hsum_mem (by norm_num)
      _ ≤ (lpNorm
          (regionalProjection (maps.partition n) f -
            regionalProjection (maps.partition n) (g : Point D → ℝ)) 2 μ +
          lpNorm
            (regionalProjection (maps.partition n) (g : Point D → ℝ) -
              (g : Point D → ℝ)) 2 μ) +
          lpNorm ((g : Point D → ℝ) - f) 2 μ := by
            gcongr
            exact lpNorm_add_le hprojection_mem (by norm_num)
      _ = _ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg lpNorm_nonneg]
  calc
    lpNorm (regionalProjection (maps.partition n) f - f) 2 μ ≤
        lpNorm
          (regionalProjection (maps.partition n) f -
            regionalProjection (maps.partition n) (g : Point D → ℝ)) 2 μ +
          lpNorm
            (regionalProjection (maps.partition n) (g : Point D → ℝ) -
              (g : Point D → ℝ)) 2 μ +
          lpNorm ((g : Point D → ℝ) - f) 2 μ := htriangle
    _ < ε := by linarith

/-- The exact source-facing statement of manuscript Lemma `lem:averaging`.

The argument uses the `RegionalMaps` fields of the fixed conditional
experiment.  Quantifying over `FixedConditionalExperiment` deliberately
retains the paper's nonatomic Borel probability-measure hypothesis through
`E.nonatomic_spatial_measure`, even though that hypothesis is not needed by
this particular approximation argument. -/
theorem regionalAveraging_tendsto_L2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ) (hf : MemLp f 2 μ) :
    Tendsto
      (fun n => lpNorm (regionalProjection (E.maps.partition n) f - f) 2 μ)
      atTop (nhds 0) :=
  regionalProjection_error_tendsto E.maps f hf

end InfillGLSLean.ManuscriptSpecification.L026
