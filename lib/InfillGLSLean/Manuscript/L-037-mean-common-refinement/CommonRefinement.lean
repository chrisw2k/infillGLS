module

public import ManuscriptSpecification
public import Mathlib.MeasureTheory.Measure.AEDisjoint

/-!
# Finite common refinements for the nonnested partition argument

This file records only the finite set-theoretic part of the common-refinement
argument in Appendix `app:mean` of the manuscript.  The observed partitions
remain nonnested.  No covariance, information, or GLS conclusion is stated
here.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L037

open Filter MeasureTheory Set

universe u

variable {D : CompactEuclideanDomain}
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]

/-- One raw cell in the finite common refinement of two source partitions. -/
@[expose] def commonCell {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (index : Fin N × Fin M) : Set (Point D) :=
  left.cell index.1 ∩ right.cell index.2

/-- Indices of common-refinement cells that are not null.  The paper omits
exactly the complementary finite family of null intersections. -/
@[expose] def nonnullCommonIndex {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) :=
  { index : Fin N × Fin M // μ (commonCell left right index) ≠ 0 }

/-- A nonnull cell of the finite common refinement. -/
@[expose] def nonnullCommonCell {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (index : nonnullCommonIndex left right) :
    Set (Point D) :=
  commonCell left right index.1

omit [IsProbabilityMeasure μ] in
/-- Public expansion interface for one raw common-refinement cell.  This
stable theorem records the literal intersection used by downstream proofs. -/
theorem commonCell_eq_intersection {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (index : Fin N × Fin M) :
    commonCell left right index = left.cell index.1 ∩ right.cell index.2 := rfl

omit [IsProbabilityMeasure μ] in
/-- Public expansion interface for a retained common-refinement cell. -/
theorem nonnullCommonCell_eq_commonCell {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (index : nonnullCommonIndex left right) :
    nonnullCommonCell left right index = commonCell left right index.1 := rfl

omit [IsProbabilityMeasure μ] in
/-- Swapping the source partitions only swaps the two coordinates of a raw
intersection cell. -/
theorem commonCell_swap {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (i : Fin N) (j : Fin M) :
    commonCell left right (i, j) = commonCell right left (j, i) := by
  rw [commonCell_eq_intersection, commonCell_eq_intersection, Set.inter_comm]

/-- The positive cells of a binary common refinement are canonically
reindexed when the two source partitions are swapped. -/
@[expose] def swapNonnullCommonIndex {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) :
    nonnullCommonIndex left right ≃ nonnullCommonIndex right left where
  toFun index := ⟨(index.1.2, index.1.1), by
    rw [← commonCell_swap left right index.1.1 index.1.2]
    exact index.2⟩
  invFun index := ⟨(index.1.2, index.1.1), by
    rw [commonCell_swap left right index.1.2 index.1.1]
    exact index.2⟩
  left_inv index := by
    apply Subtype.ext
    rfl
  right_inv index := by
    apply Subtype.ext
    rfl

omit [IsProbabilityMeasure μ] in
/-- The cell indexed by the swapped positive-cell equivalence is literally
the same set, rather than merely equal almost everywhere. -/
theorem nonnullCommonCell_swap {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (index : nonnullCommonIndex left right) :
    nonnullCommonCell right left (swapNonnullCommonIndex left right index) =
      nonnullCommonCell left right index := by
  rw [nonnullCommonCell_eq_commonCell, nonnullCommonCell_eq_commonCell]
  exact (commonCell_swap left right index.1.1 index.1.2).symm

omit [IsProbabilityMeasure μ] in
/-- Every raw common-refinement cell is Borel. -/
theorem commonCell_measurable {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (index : Fin N × Fin M) :
    MeasurableSet (commonCell left right index) :=
  (left.measurable_cell index.1).inter (right.measurable_cell index.2)

/-- The cells of one source a.e.-partition cover the domain up to a null set. -/
theorem sourceCells_ae_cover {N : ℕ} (partition : AERegionalPartition μ N) :
    (⋃ i, partition.cell i) =ᵐ[μ] Set.univ := by
  rw [ae_eq_univ]
  rw [measure_compl (MeasurableSet.iUnion partition.measurable_cell) (by finiteness),
    IsProbabilityMeasure.measure_univ, partition.union_measure_one]
  norm_num

/-- The raw intersection family covers the domain up to a null set. -/
theorem commonCells_ae_cover {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) :
    (⋃ index : Fin N × Fin M, commonCell left right index) =ᵐ[μ] Set.univ := by
  have hset :
      (⋃ index : Fin N × Fin M, commonCell left right index) =
        (⋃ i, left.cell i) ∩ (⋃ j, right.cell j) := by
    ext x
    simp [commonCell]
  rw [hset]
  exact (inter_ae_eq_right_of_ae_eq_univ (sourceCells_ae_cover left)).trans
    (sourceCells_ae_cover right)

omit [IsProbabilityMeasure μ] in
/-- Raw common-refinement cells are pairwise a.e.-disjoint.  Null
intersections are intentionally retained at this stage; later reindexing may
omit them before forming regional averages. -/
theorem commonCells_pairwise_aedisjoint {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) :
    Pairwise (Function.onFun (AEDisjoint μ) (commonCell left right)) := by
  intro a b hab
  by_cases hleft : a.1 = b.1
  · have hright : a.2 ≠ b.2 := by
      intro hright
      apply hab
      exact Prod.ext hleft hright
    exact (right.aedisjoint_cell hright).mono Set.inter_subset_right Set.inter_subset_right
  · exact (left.aedisjoint_cell hleft).mono Set.inter_subset_left Set.inter_subset_left

/-- The literal deterministic coefficient that recovers a left-cell average
from an intersection-cell average.  It is the paper's
`μ(Rᵢ ∩ Sⱼ) / μ(Rᵢ)` weight. -/
noncomputable def leftRawCommonWeight {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (i : Fin N) (j : Fin M) : ℝ :=
  μ.real (commonCell left right (i, j)) / μ.real (left.cell i)

/-- The unfiltered, finite aggregation matrix from raw intersection-cell
averages to the averages on the left source partition.  Zero-mass columns are
retained here only to make the finite set-integral identity transparent. -/
noncomputable def leftRawAggregationMatrix {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) : Matrix (Fin N) (Fin N × Fin M) ℝ :=
  fun i index => if index.1 = i then leftRawCommonWeight left right i index.2 else 0

/-- The raw vector of all intersection-cell averages. -/
noncomputable def rawCommonRegionalValues {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (f : Point D → ℝ) : Fin N × Fin M → ℝ :=
  fun index => cellMean μ (commonCell left right index) f

/-- The intersection-cell averages after the paper's zero-mass intersections
have been omitted. -/
@[expose] noncomputable def nonnullCommonRegionalValues {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (f : Point D → ℝ) :
    nonnullCommonIndex left right → ℝ :=
  fun index => cellMean μ (nonnullCommonCell left right index) f

/-- Given any finite enumeration of the retained common-refinement cells,
this is the deterministic aggregation matrix to the left source partition.
Its nonzero entries are exactly the literal measure ratios from the paper. -/
@[expose] noncomputable def leftNumberedCommonAggregationMatrix {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) : Matrix (Fin N) (Fin K) ℝ :=
  fun i k =>
    if (e k).1.1 = i then
      μ.real (nonnullCommonCell left right (e k)) / μ.real (left.cell i)
    else 0

/-- The deterministic aggregation matrix to the right source partition from
the *same* chosen enumeration of positive intersection cells.  Its entries
are the literal weights `μ(Rᵢ ∩ Sⱼ) / μ(Sⱼ)`; no second enumeration or
postulated observation map is used. -/
@[expose] noncomputable def rightNumberedCommonAggregationMatrix {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) : Matrix (Fin M) (Fin K) ℝ :=
  fun j k =>
    if (e k).1.2 = j then
      μ.real (nonnullCommonCell left right (e k)) / μ.real (right.cell j)
    else 0

/-- The vector of retained common-refinement averages in a chosen finite
enumeration. -/
@[expose] noncomputable def numberedCommonRegionalValues {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (f : Point D → ℝ) : Fin K → ℝ :=
  fun k => nonnullCommonRegionalValues left right f (e k)

omit [IsProbabilityMeasure μ] in
/-- Public pointwise expansion of the retained common-refinement average. -/
theorem numberedCommonRegionalValues_apply {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (f : Point D → ℝ) (k : Fin K) :
    numberedCommonRegionalValues left right e f k =
      cellMean μ (nonnullCommonCell left right (e k)) f := rfl

omit [IsProbabilityMeasure μ] in
/-- If an externally named refinement has the binary positive common cells as
its cells, its regional-average vector is exactly the numbered vector above.
This consumes only the cell-identification conclusion of
`exists_numberedCommonRefinement`; it adds no refinement structure. -/
theorem numberedCommonRegionalValues_eq_refinementCellMeans {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (refinement : AERegionalPartition μ K)
    (hcell : ∀ k, refinement.cell k = nonnullCommonCell left right (e k))
    (f : Point D → ℝ) :
    numberedCommonRegionalValues left right e f =
      fun k => cellMean μ (refinement.cell k) f := by
  funext k
  rw [numberedCommonRegionalValues_apply, ← hcell k]

omit [IsProbabilityMeasure μ] in
/-- Public pointwise expansion of the left aggregation weights. -/
theorem leftNumberedCommonAggregationMatrix_apply {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (i : Fin N) (k : Fin K) :
    leftNumberedCommonAggregationMatrix left right e i k =
      if (e k).1.1 = i then
        μ.real (nonnullCommonCell left right (e k)) / μ.real (left.cell i)
      else 0 := rfl

omit [IsProbabilityMeasure μ] in
/-- Public pointwise expansion of the right aggregation weights from the same
positive-cell enumeration. -/
theorem rightNumberedCommonAggregationMatrix_apply {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (j : Fin M) (k : Fin K) :
    rightNumberedCommonAggregationMatrix left right e j k =
      if (e k).1.2 = j then
        μ.real (nonnullCommonCell left right (e k)) / μ.real (right.cell j)
      else 0 := rfl

omit [IsProbabilityMeasure μ] in
/-- Applying the raw aggregation matrix gives the finite weighted sum in the
single-cell identity below. -/
theorem leftRawAggregationMatrix_mulVec_apply {N M : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (f : Point D → ℝ) (i : Fin N) :
    (Matrix.mulVec (leftRawAggregationMatrix left right)
      (rawCommonRegionalValues left right f)) i =
      ∑ j : Fin M, leftRawCommonWeight left right i j *
        cellMean μ (commonCell left right (i, j)) f := by
  classical
  change (∑ index : Fin N × Fin M,
      (if index.1 = i then leftRawCommonWeight left right i index.2 else 0) *
        cellMean μ (commonCell left right index) f) = _
  rw [Fintype.sum_prod_type]
  simp_rw [ite_mul, zero_mul, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  rw [Fintype.sum_ite_eq']

/-- For one left cell, the intersections with every right cell cover it up to
a null set. -/
theorem leftCell_rawCommonCells_ae_cover {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (i : Fin N) :
    (⋃ j : Fin M, commonCell left right (i, j)) =ᵐ[μ] left.cell i := by
  have hset :
      (⋃ j : Fin M, commonCell left right (i, j)) =
        left.cell i ∩ (⋃ j : Fin M, right.cell j) := by
    ext x
    simp [commonCell]
  rw [hset]
  filter_upwards [sourceCells_ae_cover right] with x hx
  apply propext
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, by rw [hx]; trivial⟩

omit [IsProbabilityMeasure μ] in
/-- For one fixed left cell, its raw intersection cells are pairwise
a.e.-disjoint. -/
theorem leftCell_rawCommonCells_pairwise_aedisjoint {N M : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M) (i : Fin N) :
    Pairwise (Function.onFun (AEDisjoint μ) (fun j : Fin M => commonCell left right (i, j))) := by
  intro a b hab
  exact (right.aedisjoint_cell hab).mono Set.inter_subset_right Set.inter_subset_right

/-- The finite set-integral identity behind the paper's statement that a
coarser regional observation is a deterministic linear image of a common
refinement.  Integrability is exactly what Mathlib's a.e.-disjoint integral
additivity requires. -/
theorem cellMean_eq_sum_leftRawCommonWeight {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (f : Point D → ℝ) (hf : Integrable f μ)
    (i : Fin N) :
    cellMean μ (left.cell i) f =
      ∑ j : Fin M, leftRawCommonWeight left right i j *
        cellMean μ (commonCell left right (i, j)) f := by
  let s : Fin M → Set (Point D) := fun j => commonCell left right (i, j)
  have hmeasure : ∀ j, MeasurableSet (s j) := by
    intro j
    exact commonCell_measurable left right (i, j)
  have hdisjoint : Pairwise (Function.onFun (AEDisjoint μ) s) :=
    leftCell_rawCommonCells_pairwise_aedisjoint left right i
  have hintegral :
      (∫ x in left.cell i, f x ∂μ) = ∑ j : Fin M, ∫ x in s j, f x ∂μ := by
    calc
      (∫ x in left.cell i, f x ∂μ) = ∫ x in ⋃ j, s j, f x ∂μ :=
        setIntegral_congr_set (leftCell_rawCommonCells_ae_cover left right i).symm
      _ = ∑' j : Fin M, ∫ x in s j, f x ∂μ :=
        integral_iUnion_ae (fun j => (hmeasure j).nullMeasurableSet) hdisjoint hf.integrableOn
      _ = ∑ j : Fin M, ∫ x in s j, f x ∂μ := tsum_fintype _
  have haverage : ∀ j : Fin M,
      μ.real (s j) * cellMean μ (s j) f = ∫ x in s j, f x ∂μ := by
    intro j
    simpa [cellMean, smul_eq_mul] using
      (measure_smul_setAverage f (s := s j) (by finiteness))
  calc
    cellMean μ (left.cell i) f =
        (μ.real (left.cell i))⁻¹ * ∫ x in left.cell i, f x ∂μ := by
      simpa [cellMean, smul_eq_mul] using (setAverage_eq μ f (left.cell i))
    _ = ∑ j : Fin M, (μ.real (left.cell i))⁻¹ * ∫ x in s j, f x ∂μ := by
      rw [hintegral, Finset.mul_sum]
    _ = ∑ j : Fin M, leftRawCommonWeight left right i j *
        cellMean μ (commonCell left right (i, j)) f := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← haverage j]
      dsimp [leftRawCommonWeight, s]
      rw [div_eq_mul_inv]
      ring

/-- After omitting zero-mass intersections, every left regional average is
still the literal finite weighted sum of the positive common-refinement-cell
averages.  This is the exact linear-observation step used in the manuscript's
common-refinement argument. -/
theorem cellMean_eq_leftNumberedCommonAggregation {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (f : Point D → ℝ)
    (hf : Integrable f μ) (i : Fin N) :
    cellMean μ (left.cell i) f =
      (Matrix.mulVec (leftNumberedCommonAggregationMatrix left right e)
        (numberedCommonRegionalValues left right e f)) i := by
  classical
  let _ : DecidablePred (fun index : Fin N × Fin M =>
      μ (commonCell left right index) ≠ 0) := Classical.decPred _
  let _ : Fintype (nonnullCommonIndex left right) := by
    change Fintype { index : Fin N × Fin M // μ (commonCell left right index) ≠ 0 }
    exact Subtype.fintype _
  let F : Fin N × Fin M → ℝ := fun index =>
    leftRawAggregationMatrix left right i index * rawCommonRegionalValues left right f index
  have hzero : ∀ index : {index : Fin N × Fin M //
      ¬ μ (commonCell left right index) ≠ 0}, F index.1 = 0 := by
    intro index
    have hmeasure : μ (commonCell left right index.1) = 0 := not_ne_iff.mp index.2
    by_cases hrow : index.1.1 = i
    · have hindex : (i, index.1.2) = index.1 := Prod.ext hrow.symm rfl
      have hmeasure' : μ (commonCell left right (i, index.1.2)) = 0 := by
        rw [hindex]
        exact hmeasure
      change (if index.1.1 = i then
        leftRawCommonWeight left right i index.1.2 else 0) *
          cellMean μ (commonCell left right index.1) f = 0
      rw [ite_eq_left hrow]
      unfold leftRawCommonWeight
      change ((μ (commonCell left right (i, index.1.2))).toReal /
        (μ (left.cell i)).toReal) * cellMean μ (commonCell left right index.1) f = 0
      rw [hmeasure']
      simp
    · simp [F, leftRawAggregationMatrix, rawCommonRegionalValues, hrow]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun index : Fin N × Fin M => μ (commonCell left right index) ≠ 0) F
  have hnullsum : (∑ index : {index : Fin N × Fin M //
      ¬ μ (commonCell left right index) ≠ 0}, F index.1) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    exact hzero index
  rw [hnullsum, add_zero] at hsplit
  have hsubtype :
      (∑ index : nonnullCommonIndex left right, F index.1) = ∑ index : Fin N × Fin M, F index :=
    hsplit
  have hequiv :
      (∑ k : Fin K, F (e k).1) = ∑ index : nonnullCommonIndex left right, F index.1 :=
    Equiv.sum_comp e (fun index => F index.1)
  calc
    cellMean μ (left.cell i) f =
        (Matrix.mulVec (leftRawAggregationMatrix left right)
          (rawCommonRegionalValues left right f)) i := by
      rw [leftRawAggregationMatrix_mulVec_apply]
      exact cellMean_eq_sum_leftRawCommonWeight left right f hf i
    _ = ∑ index : Fin N × Fin M, F index := by
      rfl
    _ = ∑ k : Fin K, F (e k).1 := (hequiv.trans hsubtype).symm
    _ = (Matrix.mulVec (leftNumberedCommonAggregationMatrix left right e)
          (numberedCommonRegionalValues left right e f)) i := by
      dsimp [F]
      simp only [leftRawAggregationMatrix, leftRawCommonWeight, rawCommonRegionalValues, Matrix.mulVec, dotProduct,
        leftNumberedCommonAggregationMatrix, numberedCommonRegionalValues,
        nonnullCommonRegionalValues, nonnullCommonCell]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hrow : (e k).1.1 = i
      · simp [hrow, commonCell]
      · simp [hrow]

omit [IsProbabilityMeasure μ] in
/-- Swapping the two source partitions and reindexing by
`swapNonnullCommonIndex` leaves the vector of literal positive-cell averages
unchanged. -/
theorem numberedCommonRegionalValues_swap {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (f : Point D → ℝ) :
    numberedCommonRegionalValues right left
        (e.trans (swapNonnullCommonIndex left right)) f =
      numberedCommonRegionalValues left right e f := by
  funext k
  rw [numberedCommonRegionalValues_apply, numberedCommonRegionalValues_apply]
  change cellMean μ
      (nonnullCommonCell right left (swapNonnullCommonIndex left right (e k))) f =
    cellMean μ (nonnullCommonCell left right (e k)) f
  rw [nonnullCommonCell_swap]

omit [IsProbabilityMeasure μ] in
/-- The right aggregation matrix from one positive-cell enumeration is the
left aggregation matrix for the swapped source partitions after the canonical
positive-cell reindexing. -/
theorem rightNumberedCommonAggregationMatrix_eq_leftNumberedCommonAggregationMatrix_swap
    {N M K : ℕ} (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) :
    rightNumberedCommonAggregationMatrix left right e =
      leftNumberedCommonAggregationMatrix right left
        (e.trans (swapNonnullCommonIndex left right)) := by
  ext j k
  rw [rightNumberedCommonAggregationMatrix_apply,
    leftNumberedCommonAggregationMatrix_apply]
  change
    (if (e k).1.2 = j then
      μ.real (nonnullCommonCell left right (e k)) / μ.real (right.cell j)
    else 0) =
      (if (e k).1.2 = j then
        μ.real (nonnullCommonCell right left
          (swapNonnullCommonIndex left right (e k))) / μ.real (right.cell j)
      else 0)
  rw [nonnullCommonCell_swap]

/-- After omitting zero-mass intersections, every right regional average is
the literal finite weighted sum of the same positive common-refinement-cell
averages used for the left regional averages. -/
theorem cellMean_eq_rightNumberedCommonAggregation {N M K : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (f : Point D → ℝ)
    (hf : Integrable f μ) (j : Fin M) :
    cellMean μ (right.cell j) f =
      (Matrix.mulVec (rightNumberedCommonAggregationMatrix left right e)
        (numberedCommonRegionalValues left right e f)) j := by
  have hleft := cellMean_eq_leftNumberedCommonAggregation right left
    (e.trans (swapNonnullCommonIndex left right)) f hf j
  rw [← rightNumberedCommonAggregationMatrix_eq_leftNumberedCommonAggregationMatrix_swap,
    numberedCommonRegionalValues_swap] at hleft
  exact hleft

/-- A finite deterministic linear observation transforms the finite error
covariance by congruence.  This is the covariance calculation needed after
the completely derived regional-average aggregation identity above. -/
theorem finiteErrorCovariance_linearObservation {Ω ι κ : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (error : κ → Ω → ℝ)
    (herror : ∀ k, MemLp (error k) 2 P) :
    finiteErrorCovariance
        (fun i ω => (Matrix.mulVec A (fun k => error k ω)) i) P =
      A * finiteErrorCovariance error P * Matrix.transpose A := by
  ext i j
  change ProbabilityTheory.covariance (fun ω => ∑ k, A i k * error k ω)
    (fun ω => ∑ k, A j k * error k ω) P =
      ((A * finiteErrorCovariance error P) * Matrix.transpose A) i j
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum]
  · simp_rw [ProbabilityTheory.covariance_const_mul_left,
      ProbabilityTheory.covariance_const_mul_right]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, finiteErrorCovariance_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    calc
      ∑ l, A i l * (A j k * ProbabilityTheory.covariance (error l) (error k) P) =
          ∑ l, (A i l * ProbabilityTheory.covariance (error l) (error k) P) * A j k := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = (∑ l, A i l * ProbabilityTheory.covariance (error l) (error k) P) * A j k := by
        exact (Finset.sum_mul Finset.univ
          (fun l => A i l * ProbabilityTheory.covariance (error l) (error k) P) (A j k)).symm
  · intro k
    exact (herror k).const_mul (A i k)
  · intro k
    exact (herror k).const_mul (A j k)

/-- The exact covariance bridge for the two-partition common refinement:
under the stated integrability facts, the covariance of the literal left
regional averages is the deterministic congruence of the covariance of the
positive common-refinement averages.  No observation map is postulated. -/
theorem finiteErrorCovariance_leftRegionalValues_eq_commonCongruence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {N M K : ℕ} (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (field : Ω → Point D → ℝ)
    (hspatial : ∀ ω, Integrable (field ω) μ)
    (hcommon : ∀ k, MemLp
      (fun ω => numberedCommonRegionalValues left right e (field ω) k) 2 P) :
    finiteErrorCovariance (fun i ω => cellMean μ (left.cell i) (field ω)) P =
      leftNumberedCommonAggregationMatrix left right e *
        finiteErrorCovariance
          (fun k ω => numberedCommonRegionalValues left right e (field ω) k) P *
        Matrix.transpose (leftNumberedCommonAggregationMatrix left right e) := by
  have hvalues :
      (fun i ω => cellMean μ (left.cell i) (field ω)) =
        (fun i ω =>
          (Matrix.mulVec (leftNumberedCommonAggregationMatrix left right e)
            (fun k => numberedCommonRegionalValues left right e (field ω) k)) i) := by
    funext i ω
    exact cellMean_eq_leftNumberedCommonAggregation left right e (field ω) (hspatial ω) i
  rw [hvalues]
  exact finiteErrorCovariance_linearObservation
    (leftNumberedCommonAggregationMatrix left right e)
    (fun k ω => numberedCommonRegionalValues left right e (field ω) k) hcommon

/-- The exact right-partition covariance bridge from the same two-partition
positive common-refinement enumeration.  Its matrix is the literal
measure-weighted right regional-average map, derived above rather than
assumed as an observation operator. -/
theorem finiteErrorCovariance_rightRegionalValues_eq_commonCongruence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {N M K : ℕ} (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (field : Ω → Point D → ℝ)
    (hspatial : ∀ ω, Integrable (field ω) μ)
    (hcommon : ∀ k, MemLp
      (fun ω => numberedCommonRegionalValues left right e (field ω) k) 2 P) :
    finiteErrorCovariance (fun j ω => cellMean μ (right.cell j) (field ω)) P =
      rightNumberedCommonAggregationMatrix left right e *
        finiteErrorCovariance
          (fun k ω => numberedCommonRegionalValues left right e (field ω) k) P *
        Matrix.transpose (rightNumberedCommonAggregationMatrix left right e) := by
  have hvalues :
      (fun j ω => cellMean μ (right.cell j) (field ω)) =
        (fun j ω =>
          (Matrix.mulVec (rightNumberedCommonAggregationMatrix left right e)
            (fun k => numberedCommonRegionalValues left right e (field ω) k)) j) := by
    funext j ω
    exact cellMean_eq_rightNumberedCommonAggregation left right e (field ω) (hspatial ω) j
  rw [hvalues]
  exact finiteErrorCovariance_linearObservation
    (rightNumberedCommonAggregationMatrix left right e)
    (fun k ω => numberedCommonRegionalValues left right e (field ω) k) hcommon

/-- Omitting the finitely many null intersections preserves the a.e. cover.
This is the exact positive-cell step in the paper's finite common-refinement
construction; no observed partition is assumed nested. -/
theorem nonnullCommonCells_ae_cover {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) :
    (⋃ index : nonnullCommonIndex left right, nonnullCommonCell left right index) =ᵐ[μ]
      Set.univ := by
  let zeroIndex := { index : Fin N × Fin M // μ (commonCell left right index) = 0 }
  let zeroCells : Set (Point D) :=
    ⋃ index : zeroIndex, commonCell left right index.1
  have hzero : μ zeroCells = 0 := by
    apply measure_iUnion_null
    intro index
    exact index.2
  have hraw := commonCells_ae_cover left right
  have hzeroae : zeroCells =ᵐ[μ] (∅ : Set (Point D)) := ae_eq_empty.mpr hzero
  filter_upwards [hraw, hzeroae] with x hxraw hxzero
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    have hxraw_mem : x ∈ (⋃ index : Fin N × Fin M, commonCell left right index) := by
      rw [hxraw]
      trivial
    rcases Set.mem_iUnion.mp hxraw_mem with ⟨index, hxindex⟩
    by_cases hnonnull : μ (commonCell left right index) ≠ 0
    · exact Set.mem_iUnion.mpr ⟨⟨index, hnonnull⟩, hxindex⟩
    · have hxzeroCell : x ∈ zeroCells :=
        Set.mem_iUnion.mpr ⟨⟨index, not_ne_iff.mp hnonnull⟩, hxindex⟩
      have : x ∈ (∅ : Set (Point D)) := by
        rw [← hxzero]
        exact hxzeroCell
      simp at this

omit [IsProbabilityMeasure μ] in
/-- Every retained common-refinement cell is Borel. -/
theorem nonnullCommonCell_measurable {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (index : nonnullCommonIndex left right) :
    MeasurableSet (nonnullCommonCell left right index) :=
  commonCell_measurable left right index.1

omit [IsProbabilityMeasure μ] in
/-- Every retained common-refinement cell has strictly positive measure. -/
theorem nonnullCommonCell_positive {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) (index : nonnullCommonIndex left right) :
    0 < μ (nonnullCommonCell left right index) :=
  pos_iff_ne_zero.mpr index.2

omit [IsProbabilityMeasure μ] in
/-- The retained positive cells remain pairwise a.e.-disjoint. -/
theorem nonnullCommonCells_pairwise_aedisjoint {N M : ℕ}
    (left : AERegionalPartition μ N) (right : AERegionalPartition μ M) :
    Pairwise (Function.onFun (AEDisjoint μ) (nonnullCommonCell left right)) := by
  intro a b hab
  have hraw : a.1 ≠ b.1 := by
    intro h
    apply hab
    exact Subtype.ext h
  change AEDisjoint μ (commonCell left right a.1) (commonCell left right b.1)
  exact commonCells_pairwise_aedisjoint left right hraw

/-- The positive intersection cells can be reindexed by `Fin K`, hence form a
new finite a.e.-partition in the source's own sense.  This is only a finite
enumeration of the nonnull intersections; it makes no nesting claim about the
two source partitions. -/
theorem exists_numberedCommonRefinement {N M : ℕ} (left : AERegionalPartition μ N)
    (right : AERegionalPartition μ M) :
    ∃ (K : ℕ) (refinement : AERegionalPartition μ K)
      (e : Fin K ≃ nonnullCommonIndex left right),
      ∀ i, refinement.cell i = nonnullCommonCell left right (e i) := by
  classical
  let _ : Finite (nonnullCommonIndex left right) := by
    change Finite { index : Fin N × Fin M // μ (commonCell left right index) ≠ 0 }
    infer_instance
  let _ : Fintype (nonnullCommonIndex left right) := Fintype.ofFinite _
  let e : Fin (Fintype.card (nonnullCommonIndex left right)) ≃ nonnullCommonIndex left right :=
    (Fintype.equivFin (nonnullCommonIndex left right)).symm
  let refinement : AERegionalPartition μ (Fintype.card (nonnullCommonIndex left right)) :=
    { cell := fun i => nonnullCommonCell left right (e i)
      measurable_cell := by
        intro i
        exact nonnullCommonCell_measurable left right (e i)
      aedisjoint_cell := by
        intro i j hij
        apply nonnullCommonCells_pairwise_aedisjoint left right
        intro heq
        exact hij (e.injective heq)
      union_measure_one := by
        have hsets :
            (⋃ i : Fin (Fintype.card (nonnullCommonIndex left right)),
              nonnullCommonCell left right (e i)) =
              ⋃ index : nonnullCommonIndex left right, nonnullCommonCell left right index := by
          ext x
          constructor
          · simp only [Set.mem_iUnion]
            rintro ⟨i, hxi⟩
            exact ⟨e i, hxi⟩
          · simp only [Set.mem_iUnion]
            rintro ⟨index, hxindex⟩
            refine ⟨e.symm index, ?_⟩
            simpa using hxindex
        have hcover :
            (⋃ i : Fin (Fintype.card (nonnullCommonIndex left right)),
              nonnullCommonCell left right (e i)) =ᵐ[μ] Set.univ := by
          rw [hsets]
          exact nonnullCommonCells_ae_cover left right
        exact (measure_congr hcover).trans IsProbabilityMeasure.measure_univ
      positive_measure := by
        intro i
        exact nonnullCommonCell_positive left right (e i) }
  exact ⟨Fintype.card (nonnullCommonIndex left right), refinement, e, fun _ => rfl⟩

end InfillGLSLean.ManuscriptSpecification.L037

end
