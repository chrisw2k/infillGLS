module

public import «L-037-mean-common-refinement».GaussMarkov
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Convex.Integral

/-! The finite GLS bridge is imported through its canonical task-qualified
module path, avoiding duplicate declaration loading when downstream modules
also import `L-037-mean-common-refinement.GaussMarkov`. The imported
mathematics is unchanged. -/

/-!
# Source-faithful finite common refinements for Appendix `lem:mean`

This module extends L-037 only by deriving finite iteration and the
almost-everywhere integrability facts supplied by the fixed source experiment.
It introduces no refinement, observation, rank, or nesting assumption.

Source: `the source manuscript`, Appendix `app:mean`, lines 554--567.
Dependencies: L-037 finite binary common refinements and finite GLS comparison.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L039

open Filter MeasureTheory Set Matrix ProbabilityTheory
open scoped BigOperators ENNReal Topology

universe u v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

open InfillGLSLean.ManuscriptSpecification.L037

/-! ## Source joint-second-moment bridge -/

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The source regressor second-moment condition makes the fixed treatment
function spatially square-integrable. -/
theorem treatment_memLp_two
    (E : FixedConditionalExperiment μ P) : MemLp E.treatment 2 μ := by
  have hsq_measurable : Measurable (fun s => E.treatment s ^ 2) :=
    E.treatment_measurable.pow measurable_const
  have hpoint : ∀ s : Point D,
      ENNReal.ofReal (E.treatment s ^ 2) ≤
        ENNReal.ofReal (E.treatment s ^ 2 +
          ∑ j : Fin E.q, E.controls j s ^ 2) := by
    intro s
    exact ENNReal.ofReal_le_ofReal
      (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => sq_nonneg (E.controls j s)))
  have hfinite :
      (∫⁻ s, ENNReal.ofReal (E.treatment s ^ 2) ∂μ) < ∞ :=
    lt_of_le_of_lt (lintegral_mono hpoint) E.regressor_second_moment
  have hsq_integrable : Integrable (fun s => E.treatment s ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hsq_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => sq_nonneg (E.treatment s))).mp hfinite.ne
  exact (memLp_two_iff_integrable_sq E.treatment_measurable.aestronglyMeasurable).mpr
    hsq_integrable

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Each fixed control is likewise spatially square-integrable under the
same literal source regressor second-moment condition. -/
theorem control_memLp_two
    (E : FixedConditionalExperiment μ P) (j : Fin E.q) : MemLp (E.controls j) 2 μ := by
  have hsq_measurable : Measurable (fun s => E.controls j s ^ 2) :=
    (E.controls_measurable j).pow measurable_const
  have hpoint : ∀ s : Point D,
      ENNReal.ofReal (E.controls j s ^ 2) ≤
        ENNReal.ofReal (E.treatment s ^ 2 +
          ∑ k : Fin E.q, E.controls k s ^ 2) := by
    intro s
    apply ENNReal.ofReal_le_ofReal
    calc
      E.controls j s ^ 2 ≤ ∑ k : Fin E.q, E.controls k s ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (E.controls k s)) (Finset.mem_univ j)
      _ ≤ E.treatment s ^ 2 + ∑ k : Fin E.q, E.controls k s ^ 2 :=
        le_add_of_nonneg_left (sq_nonneg (E.treatment s))
  have hfinite :
      (∫⁻ s, ENNReal.ofReal (E.controls j s ^ 2) ∂μ) < ∞ :=
    lt_of_le_of_lt (lintegral_mono hpoint) E.regressor_second_moment
  have hsq_integrable : Integrable (fun s => E.controls j s ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hsq_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => sq_nonneg (E.controls j s))).mp hfinite.ne
  exact (memLp_two_iff_integrable_sq
    (E.controls_measurable j).aestronglyMeasurable).mpr hsq_integrable

omit [IsProbabilityMeasure P] in
/-- The treatment is integrable as required by literal regional averaging. -/
theorem treatment_integrable (E : FixedConditionalExperiment μ P) :
    Integrable E.treatment μ :=
  (treatment_memLp_two E).integrable (by norm_num)

omit [IsProbabilityMeasure P] in
/-- Every fixed control is integrable as required by literal regional
averaging. -/
theorem control_integrable (E : FixedConditionalExperiment μ P) (j : Fin E.q) :
    Integrable (E.controls j) μ :=
  (control_memLp_two E j).integrable (by norm_num)

omit [IsProbabilityMeasure P] in
/-- The source's iterated conditional second-moment field is an ordinary
integrable square on the product experiment.  This is a direct Tonelli/Fubini
translation of `conditional_error_second_moment`; it adds no pointwise
integrability hypothesis. -/
theorem error_square_product_integrable
    (E : FixedConditionalExperiment μ P) :
    Integrable (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) (P.prod μ) := by
  have hsq_measurable : Measurable (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) :=
    E.error_jointly_measurable.pow measurable_const
  have hsq_ennreal_measurable : Measurable
      (fun z : Ω × Point D => ENNReal.ofReal (E.error z.1 z.2 ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp hsq_measurable
  have hsq_lintegral :
      (∫⁻ z : Ω × Point D,
        ENNReal.ofReal (E.error z.1 z.2 ^ 2) ∂(P.prod μ)) < ∞ := by
    rw [lintegral_prod _ hsq_ennreal_measurable.aemeasurable]
    exact E.conditional_error_second_moment
  exact
    (lintegral_ofReal_ne_top_iff_integrable hsq_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => sq_nonneg (E.error z.1 z.2))).mp
      hsq_lintegral.ne

/-- The same source field is integrable on the product experiment. -/
theorem error_product_integrable
    (E : FixedConditionalExperiment μ P) :
    Integrable (fun z : Ω × Point D => E.error z.1 z.2) (P.prod μ) := by
  have hmemLp : MemLp (fun z : Ω × Point D => E.error z.1 z.2) 2 (P.prod μ) :=
    (memLp_two_iff_integrable_sq E.error_jointly_measurable.aestronglyMeasurable).mpr
      (error_square_product_integrable E)
  exact hmemLp.integrable (by norm_num)

/-- For almost every outcome under the fixed conditional law, the entire
spatial error section is integrable.  The source supplies precisely this a.e.
statement, not an unjustified `∀ ω` strengthening. -/
theorem error_spatial_integrable_ae
    (E : FixedConditionalExperiment μ P) :
    ∀ᵐ ω ∂P, Integrable (E.error ω) μ := by
  exact (integrable_prod_iff E.error_jointly_measurable.aestronglyMeasurable).mp
    (error_product_integrable E) |>.1

omit [IsProbabilityMeasure P] in
/-- The squared spatial error is integrable for almost every outcome. -/
theorem error_square_spatial_integrable_ae
    (E : FixedConditionalExperiment μ P) :
    ∀ᵐ ω ∂P, Integrable (fun s => E.error ω s ^ 2) μ := by
  have hsq_measurable : Measurable (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) :=
    E.error_jointly_measurable.pow measurable_const
  exact (integrable_prod_iff hsq_measurable.aestronglyMeasurable).mp
    (error_square_product_integrable E) |>.1

omit [IsProbabilityMeasure μ] in
/-- The absolute value of a literal regional average is bounded by the
regional average of the absolute value. -/
private theorem abs_cellMean_le_cellMean_abs
    (R : Set (Point D)) (f : Point D → ℝ) :
    |cellMean μ R f| ≤ cellMean μ R (fun s => |f s|) := by
  have hinv : 0 ≤ (μ.real R)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  simp only [cellMean, setAverage_eq, smul_eq_mul, abs_mul]
  rw [abs_of_nonneg hinv]
  simpa only [Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left
      (norm_integral_le_integral_norm (μ := μ.restrict R) f) hinv

/-- Jensen's inequality for a literal regional average.  It is stated in the
form needed to transfer the source's joint second moment to regional errors. -/
private theorem sq_cellMean_le_cellMean_sq
    (R : Set (Point D)) (hRpos : 0 < μ R)
    (f : Point D → ℝ) (hf : Integrable f μ)
    (hfsq : Integrable (fun s => f s ^ 2) μ) :
    (cellMean μ R f) ^ 2 ≤ cellMean μ R (fun s => f s ^ 2) := by
  have habs :
      (cellMean μ R (fun s => |f s|)) ^ 2 ≤
        cellMean μ R (fun s => |f s| ^ 2) := by
    apply (convexOn_pow 2).map_set_average_le (continuousOn_pow 2) isClosed_Ici
    · exact ne_of_gt hRpos
    · finiteness
    · filter_upwards with s
      exact abs_nonneg (f s)
    · exact hf.abs.integrableOn
    · change IntegrableOn (fun s => |f s| ^ 2) R μ
      simpa only [sq_abs] using hfsq.integrableOn
  have hnonneg : 0 ≤ cellMean μ R (fun s => |f s|) := by
    rw [cellMean, setAverage_eq]
    simp only [smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg fun s => abs_nonneg (f s))
  have hsq_abs :
      |cellMean μ R f| ^ 2 ≤ (cellMean μ R (fun s => |f s|)) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr (abs_cellMean_le_cellMean_abs R f)
  simpa only [sq_abs] using hsq_abs.trans (by
    simpa only [sq_abs] using habs)

omit [IsProbabilityMeasure P] in
/-- A product-integrable random spatial field has an integrable set integral
for every measurable spatial cell.  This is the exact Fubini bridge used
below; it remains an a.e. statement where the source only supplies one. -/
private theorem integrable_setIntegral_of_integrable_product
    (field : Ω → Point D → ℝ)
    (hfield : Integrable (fun z : Ω × Point D => field z.1 z.2) (P.prod μ))
    (R : Set (Point D)) (hR : MeasurableSet R) :
    Integrable (fun ω => ∫ s in R, field ω s ∂μ) P := by
  let S : Set (Ω × Point D) := Prod.snd ⁻¹' R
  have hS : MeasurableSet S := hR.preimage measurable_snd
  have hindicator := (hfield.indicator hS).integral_prod_left
  convert hindicator using 1
  funext ω
  rw [← integral_indicator hR]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ R <;> simp [S, hs]

/-- A positive-measure regional average of the source error is square
integrable under the fixed conditional law.  It is derived from the literal
joint second-moment field, Fubini, and Jensen; no extra regional moment
assumption is introduced. -/
theorem error_cellMean_memLp_two
    (E : FixedConditionalExperiment μ P)
    (R : Set (Point D)) (hR : MeasurableSet R) (hRpos : 0 < μ R) :
    MemLp (fun ω => cellMean μ R (E.error ω)) 2 P := by
  have hset_integrable :
      Integrable (fun ω => ∫ s in R, E.error ω s ∂μ) P :=
    integrable_setIntegral_of_integrable_product E.error
      (error_product_integrable E) R hR
  have hcell_integrable :
      Integrable (fun ω => cellMean μ R (E.error ω)) P := by
    have hrewrite :
        (fun ω => cellMean μ R (E.error ω)) =
          (fun ω => (μ.real R)⁻¹ * ∫ s in R, E.error ω s ∂μ) := by
      funext ω
      rw [cellMean, setAverage_eq]
      simp only [smul_eq_mul]
    rw [hrewrite]
    exact hset_integrable.const_mul _
  have hset_square_integrable :
      Integrable (fun ω => ∫ s in R, E.error ω s ^ 2 ∂μ) P :=
    integrable_setIntegral_of_integrable_product
      (fun ω s => E.error ω s ^ 2) (error_square_product_integrable E) R hR
  have hcell_square_integrable :
      Integrable (fun ω => cellMean μ R (fun s => E.error ω s ^ 2)) P := by
    have hrewrite :
        (fun ω => cellMean μ R (fun s => E.error ω s ^ 2)) =
          (fun ω => (μ.real R)⁻¹ * ∫ s in R, E.error ω s ^ 2 ∂μ) := by
      funext ω
      rw [cellMean, setAverage_eq]
      simp only [smul_eq_mul]
    rw [hrewrite]
    exact hset_square_integrable.const_mul _
  have hsq_integrable :
      Integrable (fun ω => (cellMean μ R (E.error ω)) ^ 2) P := by
    refine Integrable.mono' hcell_square_integrable
      (hcell_integrable.aestronglyMeasurable.pow 2) ?_
    filter_upwards [error_spatial_integrable_ae E,
      error_square_spatial_integrable_ae E] with ω hω hωsq
    change |(cellMean μ R (E.error ω)) ^ 2| ≤
      cellMean μ R (fun s => E.error ω s ^ 2)
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_cellMean_le_cellMean_sq R hRpos (E.error ω) hω hωsq
  exact (memLp_two_iff_integrable_sq hcell_integrable.aestronglyMeasurable).mpr
    hsq_integrable

/-- Every actual regional error observation in the source experiment is in
`L²(P)`.  This discharges the moment premise of L-037's finite covariance
congruence for source partition cells. -/
theorem regionalRandomValues_memLp_two
    (E : FixedConditionalExperiment μ P) (n : ℕ) (i : Fin (E.maps.N n)) :
    MemLp (regionalRandomValues μ E.maps E.error n i) 2 P := by
  change MemLp
    (fun ω => cellMean μ ((E.maps.partition n).cell i) (E.error ω)) 2 P
  exact error_cellMean_memLp_two E ((E.maps.partition n).cell i)
    ((E.maps.partition n).measurable_cell i) ((E.maps.partition n).positive_measure i)

/-- The positive-cell averages of any L-037 binary common refinement are in
`L²(P)` for the actual source error field.  The conclusion comes entirely
from the returned refinement cells and the source joint second moment. -/
theorem numberedCommonRegionalValues_error_memLp_two
    (E : FixedConditionalExperiment μ P)
    {N M K : ℕ} (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (refinement : AERegionalPartition μ K)
    (hcell : ∀ k, refinement.cell k = nonnullCommonCell left right (e k))
    (k : Fin K) :
    MemLp (fun ω => numberedCommonRegionalValues left right e (E.error ω) k) 2 P := by
  simp_rw [numberedCommonRegionalValues_apply]
  apply error_cellMean_memLp_two E (nonnullCommonCell left right (e k))
  · rw [← hcell k]
    exact refinement.measurable_cell k
  · rw [← hcell k]
    exact refinement.positive_measure k

/-! ## Folding the literal binary construction over a finite prefix -/

/-- A derived common-refinement witness for the first `k + 1` observed
partitions.  `aggregation i` is not an assumption or a new observation map:
the construction below builds it by composing L-037's literal
intersection-measure matrices. -/
structure FirstCommonRefinement (maps : RegionalMaps μ) (k : ℕ) where
  K : ℕ
  partition : AERegionalPartition μ K
  aggregation : (i : Fin (k + 1)) → Matrix (Fin (maps.N i.1)) (Fin K) ℝ
  aggregation_apply : ∀ (i : Fin (k + 1)) (f : Point D → ℝ), Integrable f μ →
    ∀ r : Fin (maps.N i.1),
      cellMean μ ((maps.partition i.1).cell r) f =
        (Matrix.mulVec (aggregation i)
          (fun j => cellMean μ (partition.cell j) f)) r

/-- A literal refinement step between two successive finite-prefix common
refinements.  This proposition carries only the deterministic aggregation
matrix already constructed in `FirstCommonRefinement.extend`; it is not a new
nesting assumption on the observed partitions. -/
def FirstCommonRefinement.RefinesThrough
    {maps : RegionalMaps μ} {k : ℕ}
    (W : FirstCommonRefinement maps k)
    (Wnext : FirstCommonRefinement maps (k + 1)) : Prop :=
  ∃ aggregation : Matrix (Fin W.K) (Fin Wnext.K) ℝ,
    ∀ (f : Point D → ℝ), Integrable f μ →
      ∀ r : Fin W.K,
        cellMean μ (W.partition.cell r) f =
          (Matrix.mulVec aggregation
            (fun j => cellMean μ (Wnext.partition.cell j) f)) r

/-- The first observed partition is its own common refinement, with the
identity aggregation matrix. -/
noncomputable def firstCommonRefinementZero (maps : RegionalMaps μ) :
    FirstCommonRefinement maps 0 where
  K := maps.N 0
  partition := maps.partition 0
  aggregation := Fin.cases
    (1 : Matrix (Fin (maps.N 0)) (Fin (maps.N 0)) ℝ)
    (fun i => Fin.elim0 i)
  aggregation_apply := by
    intro i f hf
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    intro r
    simp

/-- One binary L-037 refinement extends a derived common refinement of the
first `k + 1` partitions to one of the first `k + 2`.  Earlier aggregation
matrices are composed with the literal left matrix; the new final partition
uses the literal right matrix for the same intersection-cell enumeration. -/
theorem FirstCommonRefinement.extend
    {maps : RegionalMaps μ} {k : ℕ} (W : FirstCommonRefinement maps k) :
    ∃ Wnext : FirstCommonRefinement maps (k + 1), W.RefinesThrough Wnext := by
  classical
  let last : AERegionalPartition μ (maps.N (k + 1)) := maps.partition (k + 1)
  obtain ⟨K, refinement, e, hcell⟩ :=
    exists_numberedCommonRefinement W.partition last
  let leftAggregation : Matrix (Fin W.K) (Fin K) ℝ :=
    leftNumberedCommonAggregationMatrix W.partition last e
  let rightAggregation : Matrix (Fin (maps.N (k + 1))) (Fin K) ℝ :=
    rightNumberedCommonAggregationMatrix W.partition last e
  have hvalues (f : Point D → ℝ) :
      numberedCommonRegionalValues W.partition last e f =
        fun j => cellMean μ (refinement.cell j) f :=
    numberedCommonRegionalValues_eq_refinementCellMeans
      W.partition last e refinement hcell f
  have hleft (f : Point D → ℝ) (hf : Integrable f μ) :
      (fun l => cellMean μ (W.partition.cell l) f) =
        Matrix.mulVec leftAggregation
          (fun j => cellMean μ (refinement.cell j) f) := by
    funext l
    have h := cellMean_eq_leftNumberedCommonAggregation W.partition last e f hf l
    rw [hvalues f] at h
    exact h
  let nextAggregation : (i : Fin (k + 1 + 1)) →
      Matrix (Fin (maps.N i.1)) (Fin K) ℝ := fun i =>
    Fin.lastCases
      (by simpa using rightAggregation)
      (fun old => by simpa using W.aggregation old * leftAggregation) i
  have hnextAggregation : ∀ (i : Fin (k + 1 + 1)) (f : Point D → ℝ),
      Integrable f μ → ∀ r : Fin (maps.N i.1),
      cellMean μ ((maps.partition i.1).cell r) f =
        (Matrix.mulVec (nextAggregation i)
          (fun j => cellMean μ (refinement.cell j) f)) r := by
    intro i f hf
    refine Fin.lastCases ?_ ?_ i
    · intro r
      have h := cellMean_eq_rightNumberedCommonAggregation W.partition last e f hf r
      rw [hvalues f] at h
      simpa [nextAggregation, rightAggregation] using h
    · intro old r
      have hcalc : cellMean μ ((maps.partition old.1).cell r) f =
          (Matrix.mulVec (W.aggregation old * leftAggregation)
            (fun j => cellMean μ (refinement.cell j) f)) r := by
        calc
          cellMean μ ((maps.partition old.1).cell r) f =
              (Matrix.mulVec (W.aggregation old)
                (fun l => cellMean μ (W.partition.cell l) f)) r :=
            W.aggregation_apply old f hf r
          _ = (Matrix.mulVec (W.aggregation old)
              (Matrix.mulVec leftAggregation
                (fun j => cellMean μ (refinement.cell j) f))) r := by
            rw [hleft f hf]
          _ = (Matrix.mulVec (W.aggregation old * leftAggregation)
              (fun j => cellMean μ (refinement.cell j) f)) r := by
            rw [Matrix.mulVec_mulVec]
      simpa [nextAggregation] using hcalc
  let Wnext : FirstCommonRefinement maps (k + 1) := {
    K := K
    partition := refinement
    aggregation := nextAggregation
    aggregation_apply := hnextAggregation }
  refine ⟨Wnext, leftAggregation, ?_⟩
  intro f hf r
  simpa [Wnext] using congrFun (hleft f hf) r

/-- Every finite prefix of the source's observed (not assumed nested)
partition sequence has a common refinement with literal aggregation maps to
each observed partition in that prefix. -/
theorem nonempty_firstCommonRefinement
    (maps : RegionalMaps μ) (k : ℕ) : Nonempty (FirstCommonRefinement maps k) := by
  induction k with
  | zero => exact ⟨firstCommonRefinementZero maps⟩
  | succ k ih =>
      rcases ih with ⟨W⟩
      rcases W.extend with ⟨Wnext, _⟩
      exact ⟨Wnext⟩

/-- A fixed, noncomputable choice of the recursively constructed finite
common refinement.  The choice selects only a finite enumeration of literal
positive intersections; the aggregation maps in its witness are those
constructed by `FirstCommonRefinement.extend`, never extra data from the
source experiment. -/
noncomputable def firstCommonRefinement (maps : RegionalMaps μ) :
    (k : ℕ) → FirstCommonRefinement maps k
  | 0 => firstCommonRefinementZero maps
  | k + 1 => Classical.choose (FirstCommonRefinement.extend (firstCommonRefinement maps k))

/-- Consecutive chosen finite-prefix common refinements are related by the
literal aggregation retained by `FirstCommonRefinement.extend`.  This is a
choice-specification lemma, so it exposes no additional data or hypothesis. -/
theorem firstCommonRefinement_step (maps : RegionalMaps μ) (k : ℕ) :
    (firstCommonRefinement maps k).RefinesThrough
      (firstCommonRefinement maps (k + 1)) := by
  change (firstCommonRefinement maps k).RefinesThrough
    (Classical.choose (FirstCommonRefinement.extend (firstCommonRefinement maps k)))
  exact Classical.choose_spec
    (FirstCommonRefinement.extend (firstCommonRefinement maps k))

/-- The deterministic aggregation retained by a literal refinement step.
Choosing its existential witness is only a way to name the matrix constructed
by the binary common-refinement proof. -/
noncomputable def FirstCommonRefinement.RefinesThrough.aggregation
    {maps : RegionalMaps μ} {k : ℕ}
    {W : FirstCommonRefinement maps k}
    {Wnext : FirstCommonRefinement maps (k + 1)}
    (h : W.RefinesThrough Wnext) : Matrix (Fin W.K) (Fin Wnext.K) ℝ :=
  Classical.choose h

omit [IsProbabilityMeasure μ] in
/-- Pointwise literal cell-average identity for the named aggregation of a
`RefinesThrough` proof. -/
theorem FirstCommonRefinement.RefinesThrough.aggregation_apply
    {maps : RegionalMaps μ} {k : ℕ}
    {W : FirstCommonRefinement maps k}
    {Wnext : FirstCommonRefinement maps (k + 1)}
    (h : W.RefinesThrough Wnext)
    (f : Point D → ℝ) (hf : Integrable f μ) (r : Fin W.K) :
    cellMean μ (W.partition.cell r) f =
      (Matrix.mulVec h.aggregation
        (fun j => cellMean μ (Wnext.partition.cell j) f)) r :=
  Classical.choose_spec h f hf r

/-! ## Derived aggregation of literal regional designs -/

/-- Regional values on one standalone partition.  This is the same literal
cell-average construction as `regionalValues`, without inventing a new
sequence of observations. -/
@[expose] noncomputable def partitionRegionalValues {N : ℕ}
    (partition : AERegionalPartition μ N) (f : Point D → ℝ) : Fin N → ℝ :=
  fun i => cellMean μ (partition.cell i) f

/-- The `[X\ W]` design formed from literal regional averages on one
standalone finite partition. -/
@[expose] noncomputable def partitionDesign {N q : ℕ}
    (partition : AERegionalPartition μ N) (treatment : Point D → ℝ)
    (controls : Fin q → Point D → ℝ) : Matrix (Fin N) (Fin (q + 1)) ℝ :=
  fun i j => Fin.cases (partitionRegionalValues partition treatment i)
    (fun c => partitionRegionalValues partition (controls c) i) j

omit [IsProbabilityMeasure μ] in
@[simp] theorem partitionRegionalValues_apply {N : ℕ}
    (partition : AERegionalPartition μ N) (f : Point D → ℝ) (i : Fin N) :
    partitionRegionalValues partition f i = cellMean μ (partition.cell i) f := rfl

omit [IsProbabilityMeasure μ] in
@[simp] theorem partitionDesign_apply {N q : ℕ}
    (partition : AERegionalPartition μ N) (treatment : Point D → ℝ)
    (controls : Fin q → Point D → ℝ) (i : Fin N) (j : Fin (q + 1)) :
    partitionDesign partition treatment controls i j =
      Fin.cases (partitionRegionalValues partition treatment i)
        (fun c => partitionRegionalValues partition (controls c) i) j := rfl

omit [IsProbabilityMeasure P] in
/-- The design on an earlier finite-prefix common refinement is the literal
aggregation of the design on its next refinement.  This is a derived
consequence of `RefinesThrough`, not a relation imposed on observed maps. -/
theorem FirstCommonRefinement.RefinesThrough.partitionDesign_eq_aggregation
    {maps : RegionalMaps μ} {k : ℕ}
    {W : FirstCommonRefinement maps k}
    {Wnext : FirstCommonRefinement maps (k + 1)}
    (h : W.RefinesThrough Wnext)
    (E : FixedConditionalExperiment μ P) :
    partitionDesign W.partition E.treatment E.controls =
      h.aggregation * partitionDesign Wnext.partition E.treatment E.controls := by
  ext r j
  refine Fin.cases ?_ ?_ j
  · have hvalue := h.aggregation_apply E.treatment (treatment_integrable E) r
    simpa only [partitionDesign_apply, Fin.cases_zero, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, partitionRegionalValues] using hvalue
  · intro c
    have hvalue := h.aggregation_apply (E.controls c) (control_integrable E c) r
    simpa only [partitionDesign_apply, Fin.cases_succ, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, partitionRegionalValues] using hvalue

omit [IsProbabilityMeasure μ] in
/-- Each observed regional-value vector in a finite prefix is the explicit
aggregation of the literal values on its derived common refinement. -/
theorem FirstCommonRefinement.regionalValues_eq_aggregation
    {maps : RegionalMaps μ} {k : ℕ} (W : FirstCommonRefinement maps k)
    (i : Fin (k + 1)) (f : Point D → ℝ) (hf : Integrable f μ) :
    regionalValues μ maps f i.1 =
      Matrix.mulVec (W.aggregation i) (partitionRegionalValues W.partition f) := by
  funext r
  exact W.aggregation_apply i f hf r

omit [IsProbabilityMeasure P] in
/-- The source design at every observed level in a finite prefix is the
literal deterministic aggregation of the common-refinement design.  The
integrability of treatment and controls is derived above from the source
regressor second-moment field. -/
theorem FirstCommonRefinement.regionalDesign_eq_aggregation
    {maps : RegionalMaps μ} {k : ℕ} (W : FirstCommonRefinement maps k)
    (E : FixedConditionalExperiment μ P) (hmaps : E.maps = maps)
    (i : Fin (k + 1)) :
    regionalDesign μ maps E.treatment E.controls i.1 =
      W.aggregation i * partitionDesign W.partition E.treatment E.controls := by
  subst maps
  ext r j
  refine Fin.cases ?_ ?_ j
  · have hvalue := W.regionalValues_eq_aggregation i E.treatment (treatment_integrable E)
    have hentry := congrFun hvalue r
    simpa only [regionalDesign_apply, partitionDesign_apply, Fin.cases_zero,
      Matrix.mul_apply, Matrix.mulVec, dotProduct,
      regionalValues, partitionRegionalValues] using hentry
  · intro c
    have hvalue := W.regionalValues_eq_aggregation i (E.controls c) (control_integrable E c)
    have hentry := congrFun hvalue r
    simpa only [regionalDesign_apply, regionalControls_apply, partitionDesign_apply,
      Fin.cases_succ, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      regionalValues, partitionRegionalValues] using hentry

omit [IsProbabilityMeasure P] in
/-- Full column rank of any observed design transfers to the design on a
common refinement that literally aggregates to it.  Thus no new
common-refinement rank condition is being inserted: this is a finite-rank
consequence of the source's observed-design condition. -/
theorem FirstCommonRefinement.partitionDesign_rank_eq_of_observed_rank_eq
    (E : FixedConditionalExperiment μ P) {k : ℕ}
    (W : FirstCommonRefinement E.maps k) (i : Fin (k + 1))
    (hobserved :
      (regionalDesign μ E.maps E.treatment E.controls i.1).rank = E.q + 1) :
    (partitionDesign W.partition E.treatment E.controls).rank = E.q + 1 := by
  have hdesign := W.regionalDesign_eq_aggregation E rfl i
  have hlower : E.q + 1 ≤
      (partitionDesign W.partition E.treatment E.controls).rank := by
    calc
      E.q + 1 = (regionalDesign μ E.maps E.treatment E.controls i.1).rank :=
        hobserved.symm
      _ = (W.aggregation i *
          partitionDesign W.partition E.treatment E.controls).rank :=
        congrArg Matrix.rank hdesign
      _ ≤ (partitionDesign W.partition E.treatment E.controls).rank :=
        Matrix.rank_mul_le_right _ _
  exact le_antisymm (Matrix.rank_le_width _) hlower

omit [IsProbabilityMeasure P] in
/-- Covariance is invariant under almost-everywhere replacement of either
random variable.  This elementary fact lets the source's a.e. sectional
integrability feed the finite covariance endpoints without falsely promoting
it to an everywhere statement. -/
private theorem covariance_congr_ae
    {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    ProbabilityTheory.covariance X Y P = ProbabilityTheory.covariance X' Y' P := by
  unfold ProbabilityTheory.covariance
  have hmeanX : (∫ ω, X ω ∂P) = ∫ ω, X' ω ∂P := integral_congr_ae hX
  have hmeanY : (∫ ω, Y ω ∂P) = ∫ ω, Y' ω ∂P := integral_congr_ae hY
  rw [hmeanX, hmeanY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω hωX hωY
  rw [hωX, hωY]

/-- The finite covariance on an earlier common refinement is the exact
congruence of the covariance on its next refinement under the literal
aggregation retained by `RefinesThrough`.  This derives the required
almost-everywhere error identity from the source experiment and does not
upgrade it to an everywhere spatial-integrability assertion. -/
theorem FirstCommonRefinement.RefinesThrough.finiteErrorCovariance_eq_aggregation
    (E : FixedConditionalExperiment μ P) {k : ℕ}
    {W : FirstCommonRefinement E.maps k}
    {Wnext : FirstCommonRefinement E.maps (k + 1)}
    (h : W.RefinesThrough Wnext) :
    finiteErrorCovariance
        (fun r ω => cellMean μ (W.partition.cell r) (E.error ω)) P =
      h.aggregation *
        finiteErrorCovariance
          (fun s ω => cellMean μ (Wnext.partition.cell s) (E.error ω)) P *
        Matrix.transpose h.aggregation := by
  ext r s
  rw [finiteErrorCovariance_apply]
  have hr :
      (fun ω => cellMean μ (W.partition.cell r) (E.error ω)) =ᵐ[P]
        (fun ω =>
          (Matrix.mulVec h.aggregation
            (fun j => cellMean μ (Wnext.partition.cell j) (E.error ω))) r) := by
    filter_upwards [error_spatial_integrable_ae E] with ω hω
    exact h.aggregation_apply (E.error ω) hω r
  have hs :
      (fun ω => cellMean μ (W.partition.cell s) (E.error ω)) =ᵐ[P]
        (fun ω =>
          (Matrix.mulVec h.aggregation
            (fun j => cellMean μ (Wnext.partition.cell j) (E.error ω))) s) := by
    filter_upwards [error_spatial_integrable_ae E] with ω hω
    exact h.aggregation_apply (E.error ω) hω s
  rw [covariance_congr_ae hr hs]
  have hcommon : ∀ j, MemLp
      (fun ω => cellMean μ (Wnext.partition.cell j) (E.error ω)) 2 P := by
    intro j
    exact error_cellMean_memLp_two E (Wnext.partition.cell j)
      (Wnext.partition.measurable_cell j) (Wnext.partition.positive_measure j)
  have hlinear := finiteErrorCovariance_linearObservation h.aggregation
    (fun j ω => cellMean μ (Wnext.partition.cell j) (E.error ω)) hcommon
  simpa only [finiteErrorCovariance_apply] using congrFun (congrFun hlinear r) s

/-- L-037's covariance congruence remains valid under the source's actual
almost-everywhere spatial-integrability conclusion.  The aggregation matrix
is still exactly the literal intersection-measure matrix exported by L-037. -/
theorem finiteErrorCovariance_leftRegionalValues_eq_commonCongruence_ae
    {N M K : ℕ} (left : AERegionalPartition μ N) (right : AERegionalPartition μ M)
    (e : Fin K ≃ nonnullCommonIndex left right) (field : Ω → Point D → ℝ)
    (hspatial : ∀ᵐ ω ∂P, Integrable (field ω) μ)
    (hcommon : ∀ k, MemLp
      (fun ω => numberedCommonRegionalValues left right e (field ω) k) 2 P) :
    finiteErrorCovariance (fun i ω => cellMean μ (left.cell i) (field ω)) P =
      leftNumberedCommonAggregationMatrix left right e *
        finiteErrorCovariance
          (fun k ω => numberedCommonRegionalValues left right e (field ω) k) P *
        Matrix.transpose (leftNumberedCommonAggregationMatrix left right e) := by
  ext i j
  rw [finiteErrorCovariance_apply]
  have hi :
      (fun ω => cellMean μ (left.cell i) (field ω)) =ᵐ[P]
        (fun ω =>
          (Matrix.mulVec (leftNumberedCommonAggregationMatrix left right e)
            (fun k => numberedCommonRegionalValues left right e (field ω) k)) i) := by
    filter_upwards [hspatial] with ω hω
    exact cellMean_eq_leftNumberedCommonAggregation left right e (field ω) hω i
  have hj :
      (fun ω => cellMean μ (left.cell j) (field ω)) =ᵐ[P]
        (fun ω =>
          (Matrix.mulVec (leftNumberedCommonAggregationMatrix left right e)
            (fun k => numberedCommonRegionalValues left right e (field ω) k)) j) := by
    filter_upwards [hspatial] with ω hω
    exact cellMean_eq_leftNumberedCommonAggregation left right e (field ω) hω j
  rw [covariance_congr_ae hi hj]
  have hlinear := finiteErrorCovariance_linearObservation
    (leftNumberedCommonAggregationMatrix left right e)
    (fun k ω => numberedCommonRegionalValues left right e (field ω) k) hcommon
  simpa only [finiteErrorCovariance_apply] using congrFun (congrFun hlinear i) j

/-- For any finite-prefix refinement constructed above, every source true
covariance matrix in that prefix is exactly the deterministic congruence of
the covariance of the one literal common-refinement error vector.  This is
the source-level content of the "linear image" sentence in Appendix
`lem:mean`; its only moment input is derived from the source joint second
moment. -/
theorem FirstCommonRefinement.trueCovariance_eq_aggregation
    (E : FixedConditionalExperiment μ P) {k : ℕ}
    (W : FirstCommonRefinement E.maps k)
    (i : Fin (k + 1)) :
    trueCovariance E i.1 =
      W.aggregation i *
        finiteErrorCovariance
          (fun j ω => cellMean μ (W.partition.cell j) (E.error ω)) P *
        Matrix.transpose (W.aggregation i) := by
  rw [trueCovariance_eq]
  ext r s
  rw [finiteErrorCovariance_apply]
  have hr :
      regionalRandomValues μ E.maps E.error i.1 r =ᵐ[P]
        (fun ω =>
          (Matrix.mulVec (W.aggregation i)
            (fun j => cellMean μ (W.partition.cell j) (E.error ω))) r) := by
    change (fun ω => cellMean μ ((E.maps.partition i.1).cell r) (E.error ω)) =ᵐ[P] _
    filter_upwards [error_spatial_integrable_ae E] with ω hω
    exact W.aggregation_apply i (E.error ω) hω r
  have hs :
      regionalRandomValues μ E.maps E.error i.1 s =ᵐ[P]
        (fun ω =>
          (Matrix.mulVec (W.aggregation i)
            (fun j => cellMean μ (W.partition.cell j) (E.error ω))) s) := by
    change (fun ω => cellMean μ ((E.maps.partition i.1).cell s) (E.error ω)) =ᵐ[P] _
    filter_upwards [error_spatial_integrable_ae E] with ω hω
    exact W.aggregation_apply i (E.error ω) hω s
  rw [covariance_congr_ae hr hs]
  have hcommon : ∀ j, MemLp
      (fun ω => cellMean μ (W.partition.cell j) (E.error ω)) 2 P := by
    intro j
    exact error_cellMean_memLp_two E (W.partition.cell j)
      (W.partition.measurable_cell j) (W.partition.positive_measure j)
  have hlinear := finiteErrorCovariance_linearObservation (W.aggregation i)
    (fun j ω => cellMean μ (W.partition.cell j) (E.error ω)) hcommon
  simpa only [finiteErrorCovariance_apply] using congrFun (congrFun hlinear r) s

/-!
The declarations below are added in small, independently compiled steps.  The
final API is intentionally a derived witness rather than a new experiment
field: all cells are literal finite intersections and all aggregation matrices
use their literal intersection-measure weights.
-/

end InfillGLSLean.ManuscriptSpecification.L039

end
