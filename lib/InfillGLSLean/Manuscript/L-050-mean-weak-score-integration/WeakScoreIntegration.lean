module

public import «L-044-mean-true-gls-weak».TrueGLSWeak
public import «L-047-mean-information-assembly».InformationAssembly
public import «L-049-mean-projected-design-limit».ProjectedDesignLimit

/-!
# Source integration of the true-GLS weak-score step

This task integrates the exact true-GLS weak-score paragraph of Appendix
`lem:mean`, `the source manuscript:563--580`.  The source only provides
finite GLS nonsingularity after an eventual full-rank index.  Accordingly the
public conclusion is stated on a reindexed tail; no claim is made about a
possibly singular finite prefix.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L050

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal RealInnerProductSpace

open InfillGLSLean.ManuscriptSpecification.L037
open InfillGLSLean.ManuscriptSpecification.L041
open InfillGLSLean.ManuscriptSpecification.L042
open InfillGLSLean.ManuscriptSpecification.L044
open InfillGLSLean.ManuscriptSpecification.L047
open InfillGLSLean.ManuscriptSpecification.L049
open InfillGLSLean.MeanHilbertRiesz

universe v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The local spatial-test-score range is dense because it is definitionally
the range of L-036's corestricted centered spatial-integral map.  This derives
the density input required by L-044 rather than postulating a bridge between
two equivalent local presentations of the covariance Hilbert space. -/
theorem dense_span_range_spatialTestScore
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E) :
    Dense (Submodule.span ℝ (Set.range (spatialTestScore E cov)) :
      Set (covarianceHilbertSpace E cov)) := by
  have hrange : Set.range (spatialTestScore E cov) =
      Set.range (centeredTestIntegralToCovarianceHilbertSpace E cov) := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h,
        (spatialTestScore_eq_centeredTestIntegralToCovarianceHilbertSpace E cov h).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h,
        spatialTestScore_eq_centeredTestIntegralToCovarianceHilbertSpace E cov h⟩
  have hdense : Dense (Set.range (spatialTestScore E cov)) := by
    rw [hrange]
    exact denseRange_centeredTestIntegralToCovarianceHilbertSpace E cov
  exact hdense.mono Submodule.subset_span

/-- Tail-indexed form of L-044's weak-score support theorem.  Its proof is
the same finite normalized-row calculation and Hilbert dense-span argument,
with every finite score and test evaluated at `n + start`.  This form is
needed because the manuscript guarantees finite GLS positive definiteness
only after the eventual full-rank index. -/
private theorem normalizedTrueGLSRegionalScore_tail_weakly_tendsto_zero_of_matrix_limit
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (start : ℕ) (lower : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ)
    (hlower_psd : lower.PosSemidef)
    (horder : ∀ n,
      (trueGLSCoefficientCovariance (trueCovariance E (n + start))
        (regionalDesign μ E.maps E.treatment E.controls (n + start)) - lower).PosSemidef)
    (hlimit : Tendsto (fun n => trueGLSCoefficientCovariance
      (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start))) atTop (nhds lower))
    (hdiag : Tendsto (fun n => trueGLSCoefficientCovariance
      (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start)) 0 0)
      atTop (nhds 0))
    (hpositive : ∀ n, 0 < trueGLSCoefficientCovariance
      (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start)) 0 0)
    (hcovariance : ∀ n, (trueCovariance E (n + start)).PosDef)
    (hgram : ∀ n, (trueGLSGram (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start))).PosDef)
    (hdesign_limit : ∀ h : Lp ℝ 2 μ, ∃ rlimit : Fin (E.q + 1) → ℝ,
      Tendsto (fun n => Matrix.transpose
        (regionalDesign μ E.maps E.treatment E.controls (n + start)) *ᵥ
          regionalProjectionWeights E (fun s => h s) (n + start)) atTop (nhds rlimit))
    (hdense : Dense (Submodule.span ℝ (Set.range (spatialTestScore E cov)) :
      Set (covarianceHilbertSpace E cov)))
    (v : covarianceHilbertSpace E cov) :
    Tendsto (fun n => inner ℝ
      (normalizedTrueGLSRegionalScore E cov (n + start) 0) v) atTop (nhds 0) := by
  have hbound : ∀ n, ‖normalizedTrueGLSRegionalScore E cov (n + start) 0‖ ≤ 1 := by
    intro n
    have hnorm := normalizedTrueGLSRegionalScore_norm_sq_eq_one E cov (n + start) 0
      (hcovariance n) (hgram n) (hpositive n)
    nlinarith [norm_nonneg (normalizedTrueGLSRegionalScore E cov (n + start) 0)]
  apply inner_tendsto_zero_of_dense_span
    (fun n => normalizedTrueGLSRegionalScore E cov (n + start) 0)
    (Set.range (spatialTestScore E cov)) hdense 1 zero_le_one hbound ?_ v
  intro w hw
  obtain ⟨h, rfl⟩ := hw
  apply inner_tendsto_zero_of_tendsto_projected_test
    (fun n => normalizedTrueGLSRegionalScore E cov (n + start) 0)
    (fun n => regionalCellTestScore E cov (n + start)
      (regionalProjectionWeights E (fun s => h s) (n + start)))
    (spatialTestScore E cov h) 1 zero_le_one hbound ?_ ?_
  · obtain ⟨rlimit, hrlimit⟩ := hdesign_limit h
    have halgebra := normalized_row_dot_tendsto_zero_of_lower_order lower
      (fun n => trueGLSCoefficientCovariance (trueCovariance E (n + start))
        (regionalDesign μ E.maps E.treatment E.controls (n + start)))
      hlower_psd horder hlimit 0 hdiag hpositive
      (fun n => Matrix.transpose
        (regionalDesign μ E.maps E.treatment E.controls (n + start)) *ᵥ
          regionalProjectionWeights E (fun s => h s) (n + start))
      rlimit hrlimit
    apply halgebra.congr'
    filter_upwards [] with n
    rw [normalizedTrueGLSRegionalScore_inner_weightedRegionalCellTestLp_eq
      E cov (n + start) 0
      (regionalProjectionWeights E (fun s => h s) (n + start)) (hcovariance n)]
    rfl
  · exact (tendsto_add_atTop_iff_nat start).mpr
      (regionalCellTestScore_regionalProjection_sub_tendsto_zero E cov h)

/-- Exact source-level weak-score conclusion in the true-covariance GLS
paragraph of Appendix `lem:mean`.  It discards only the finite prefix before
full rank, derives all normalized-row inputs from L-047/L-049/L-041/L-042,
and concludes weak convergence against every fixed covariance-Hilbert vector.
It deliberately stops before evaluating this limit at the mean representer. -/
theorem exists_reindexed_normalizedTrueGLSRegionalScore_weakly_tendsto_zero
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∃ start : ℕ, ∀ v : covarianceHilbertSpace E covariance,
      Tendsto (fun n => inner ℝ
        (normalizedTrueGLSRegionalScore E covariance (n + start) 0) v)
        atTop (nhds 0) := by
  rcases exists_commonRefinement_information_limit_tendsto_observed_and_treatment_row_column_zero
      E covariance with
    ⟨sourceStart, B, hB, _, _, horder_source, hlimit_source, _, _⟩
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  let start : ℕ := max sourceStart rankStart
  have hsource_le : sourceStart ≤ start := by
    exact le_max_left _ _
  have hrank_le : rankStart ≤ start := by
    exact le_max_right _ _
  have hcovariance : ∀ n, (trueCovariance E (n + start)).PosDef := by
    intro n
    exact trueCovariance_posDef E covariance (n + start)
  have hgram : ∀ n, (trueGLSGram (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start))).PosDef := by
    intro n
    exact trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
      (hcovariance n) (hfull (n + start)
        (le_trans hrank_le (Nat.le_add_left start n)))
  have hpositive : ∀ n, 0 < trueGLSCoefficientCovariance
      (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start)) 0 0 := by
    intro n
    change 0 < (trueGLSGram (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start)))⁻¹ 0 0
    exact (hgram n).inv.diag_pos
  have horder : ∀ n,
      (trueGLSCoefficientCovariance (trueCovariance E (n + start))
        (regionalDesign μ E.maps E.treatment E.controls (n + start)) - B).PosSemidef := by
    intro n
    rw [← observedTrueGLSCoefficientCovariance_eq]
    exact horder_source (n + start)
      (le_trans hsource_le (Nat.le_add_left start n))
  have hlimit : Tendsto (fun n => trueGLSCoefficientCovariance
      (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start)))
      atTop (nhds B) := by
    have hshift := (tendsto_add_atTop_iff_nat start).mpr hlimit_source
    simpa only [observedTrueGLSCoefficientCovariance_eq] using hshift
  have hdiag : Tendsto (fun n => trueGLSCoefficientCovariance
      (trueCovariance E (n + start))
      (regionalDesign μ E.maps E.treatment E.controls (n + start)) 0 0)
      atTop (nhds 0) := by
    have hshift := (tendsto_add_atTop_iff_nat start).mpr
      (observedTrueGLSTreatmentVariance_tendsto_zero E covariance)
    simpa only [observedTrueGLSTreatmentVariance_eq,
      observedTrueGLSCoefficientCovariance_eq] using hshift
  have hdesign_limit : ∀ h : Lp ℝ 2 μ, ∃ rlimit : Fin (E.q + 1) → ℝ,
      Tendsto (fun n => Matrix.transpose
        (regionalDesign μ E.maps E.treatment E.controls (n + start)) *ᵥ
          regionalProjectionWeights E (fun s => h s) (n + start)) atTop (nhds rlimit) := by
    intro h
    refine ⟨projectedDesignLimit E h, ?_⟩
    exact (tendsto_add_atTop_iff_nat start).mpr
      (tendsto_transpose_regionalDesign_mulVec_regionalProjectionWeights E h)
  refine ⟨start, ?_⟩
  intro v
  exact normalizedTrueGLSRegionalScore_tail_weakly_tendsto_zero_of_matrix_limit
    E covariance start B hB horder hlimit hdiag hpositive hcovariance hgram
    hdesign_limit (dense_span_range_spatialTestScore E covariance) v

end InfillGLSLean.ManuscriptSpecification.L050

end
