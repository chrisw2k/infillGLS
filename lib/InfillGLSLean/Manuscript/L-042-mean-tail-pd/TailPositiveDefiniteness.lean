module

public import «L-041-common-refinement-pd».CommonRefinementPD

/-!
# Eventual finite positive-definiteness prerequisites for Appendix `lem:mean`

This module derives the finite GLS prerequisites that are already implicit in
the source experiment: a full-column-rank regional design and a positive
definite covariance yield a positive definite GLS Gram matrix.  The only
strict-true-covariance input is deliberately explicit below; L-041 is the
separate source-faithful proof of that fact from `positive_test_variance`.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L042

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

universe u v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

open InfillGLSLean.ManuscriptSpecification.L037
open InfillGLSLean.ManuscriptSpecification.L041

/-- A real finite matrix having rank equal to its number of columns has an
injective `mulVec` map.  This is the precise finite full-column-rank fact
used in the GLS Gram argument. -/
theorem mulVec_injective_of_rank_eq_card
    {ι p : Type*} [Fintype ι] [Fintype p]
    (A : Matrix ι p ℝ) (hrank : A.rank = Fintype.card p) :
    Function.Injective A.mulVec := by
  change Function.Injective A.mulVecLin
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.finrank_eq_zero.mp
  have hsum := A.mulVecLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ A.mulVecLin.range = Fintype.card p := by
    simpa only [Matrix.rank] using hrank
  have hdomain : Module.finrank ℝ (p → ℝ) = Fintype.card p :=
    Module.finrank_fintype_fun_eq_card ℝ
  omega

/-- Positive definiteness of `Σ` and full column rank of `D` give positive
definiteness of `DᵀΣ⁻¹D`.  This is a finite linear-algebra consequence, not a
new statistical assumption. -/
theorem glsGram_posDef_of_covariance_posDef_and_rank
    {ι p : Type*} [Fintype ι] [DecidableEq ι] [Fintype p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (hcovariance : covariance.PosDef)
    (hrank : design.rank = Fintype.card p) :
    (trueGLSGram covariance design).PosDef := by
  simpa [trueGLSGram] using hcovariance.inv.conjTranspose_mul_mul_same
    (mulVec_injective_of_rank_eq_card design hrank)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The source's displayed eventual full-rank condition is exactly
injectivity of the regional design's coefficient map. -/
theorem regionalDesign_mulVec_injective_of_full_rank
    (E : FixedConditionalExperiment μ P) {n : ℕ}
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    Function.Injective (regionalDesign μ E.maps E.treatment E.controls n).mulVec := by
  apply mulVec_injective_of_rank_eq_card
  simpa using hrank

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- At every source-full-rank resolution, the working GLS Gram matrix is
positive definite.  Its covariance premise is the existing `kernel_posDef`
field, so no new covariance condition is inserted. -/
theorem workingGLSGram_posDef_of_full_rank
    (E : FixedConditionalExperiment μ P) {n : ℕ}
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (trueGLSGram (E.kernel n)
      (regionalDesign μ E.maps E.treatment E.controls n)).PosDef := by
  apply glsGram_posDef_of_covariance_posDef_and_rank
  · exact E.kernel_posDef n
  · simpa using hrank

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The source's eventual full-rank clause yields eventual positive
definiteness of the working GLS Gram matrices. -/
theorem eventually_workingGLSGram_posDef
    (E : FixedConditionalExperiment μ P) :
    ∀ᶠ n in atTop,
      (trueGLSGram (E.kernel n)
        (regionalDesign μ E.maps E.treatment E.controls n)).PosDef := by
  obtain ⟨n₀, hn₀⟩ := E.eventual_full_rank
  filter_upwards [eventually_atTop.2 ⟨n₀, hn₀⟩] with n hn
  exact workingGLSGram_posDef_of_full_rank E hn

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Given strict positive definiteness of the exact true covariance at one
resolution, the source-full-rank condition gives the corresponding true GLS
Gram positive definiteness.  The covariance premise here is intentionally
explicit: L-041 derives it from the source's strict test-variance clause. -/
theorem trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank
    (E : FixedConditionalExperiment μ P) {n : ℕ}
    (hcovariance : (trueCovariance E n).PosDef)
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (trueGLSGram (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n)).PosDef := by
  apply glsGram_posDef_of_covariance_posDef_and_rank
  · exact hcovariance
  · simpa using hrank

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Combining an eventual strict-true-covariance result with the unchanged
source full-rank clause yields all eventual true-GLS Gram prerequisites.
This theorem does not posit strict covariance; it transports the proof that
L-041 supplies. -/
theorem eventually_trueGLSGram_posDef_of_eventually_trueCovariance_posDef
    (E : FixedConditionalExperiment μ P)
    (hcovariance : ∀ᶠ n in atTop, (trueCovariance E n).PosDef) :
    ∀ᶠ n in atTop,
      (trueGLSGram (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n)).PosDef := by
  obtain ⟨n₀, hn₀⟩ := E.eventual_full_rank
  filter_upwards [hcovariance, eventually_atTop.2 ⟨n₀, hn₀⟩] with n hSigma hrank
  exact trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E hSigma hrank

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The existing working covariance positive-definiteness field also yields
literal invertibility at every resolution. -/
theorem workingCovariance_isUnit
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    IsUnit (E.kernel n) :=
  (E.kernel_posDef n).isUnit

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Strict positive definiteness of the true covariance gives its ordinary
finite invertibility; no inverse is defined by this result. -/
theorem trueCovariance_isUnit_of_posDef
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (hcovariance : (trueCovariance E n).PosDef) :
    IsUnit (trueCovariance E n) :=
  hcovariance.isUnit

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Eventual bundle of the finite source prerequisites needed by the
common-refinement GLS comparison and information-limit arguments.  It keeps
the strict true-covariance proof as an explicit supplied result, rather than
replacing it by an assumption inside `FixedConditionalExperiment`. -/
theorem eventually_finite_gls_prerequisites_of_eventually_trueCovariance_posDef
    (E : FixedConditionalExperiment μ P)
    (hcovariance : ∀ᶠ n in atTop, (trueCovariance E n).PosDef) :
    ∀ᶠ n in atTop,
      (E.kernel n).PosDef ∧
      (trueCovariance E n).PosDef ∧
      (trueGLSGram (E.kernel n)
        (regionalDesign μ E.maps E.treatment E.controls n)).PosDef ∧
      (trueGLSGram (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n)).PosDef := by
  obtain ⟨n₀, hn₀⟩ := E.eventual_full_rank
  filter_upwards [hcovariance, eventually_atTop.2 ⟨n₀, hn₀⟩] with n hSigma hrank
  exact ⟨E.kernel_posDef n, hSigma,
    workingGLSGram_posDef_of_full_rank E hrank,
    trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E hSigma hrank⟩

/-- At every source-full-rank resolution, the exact strict test-variance
assumption proves positive definiteness of the true GLS Gram matrix.  The
strict covariance premise is not added here: it is the L-041 consequence of
the manuscript's existing `CovarianceAssumption`. -/
theorem trueGLSGram_posDef_of_full_rank
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) {n : ℕ}
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (trueGLSGram (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n)).PosDef := by
  exact trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
    (trueCovariance_posDef E covariance n) hrank

/-- The paper's covariance clause and its existing eventual full-rank clause
give eventual positive definiteness of the true GLS Gram matrices. -/
theorem eventually_trueGLSGram_posDef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∀ᶠ n in atTop,
      (trueGLSGram (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n)).PosDef := by
  apply eventually_trueGLSGram_posDef_of_eventually_trueCovariance_posDef E
  exact Filter.Eventually.of_forall (trueCovariance_posDef E covariance)

/-- Final source-level bundle of the finite positive-definiteness
prerequisites: it uses only `kernel_posDef`, `eventual_full_rank`, and the
paper's existing covariance clause.  It introduces no extra condition on the
observed partitions or their common refinements. -/
theorem eventually_finite_gls_prerequisites
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∀ᶠ n in atTop,
      (E.kernel n).PosDef ∧
      (trueCovariance E n).PosDef ∧
      (trueGLSGram (E.kernel n)
        (regionalDesign μ E.maps E.treatment E.controls n)).PosDef ∧
      (trueGLSGram (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n)).PosDef := by
  apply eventually_finite_gls_prerequisites_of_eventually_trueCovariance_posDef E
  exact Filter.Eventually.of_forall (trueCovariance_posDef E covariance)

end InfillGLSLean.ManuscriptSpecification.L042
