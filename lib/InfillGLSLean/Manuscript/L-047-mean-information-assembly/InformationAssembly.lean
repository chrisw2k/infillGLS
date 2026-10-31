module

public import «L-039-mean-source-common-refinement».SourceCommonRefinement
public import «L-040-mean-information-limit».InformationLimit
public import «L-041-common-refinement-pd».CommonRefinementPD
public import «L-042-mean-tail-pd».TailPositiveDefiniteness
public import «L-027-api-fwl-integration».FWLIntegration
public import «L-043-mean-refinement-convergence».RefinementConvergence

/-!
# Global common-refinement information-limit assembly for Appendix `lem:mean`

This module assembles the exact finite-dimensional argument in
`the source manuscript:559--563`.  It deliberately does not treat observed
partitions as nested.  The only deferred input is the epsilon-tail
fixed-refinement comparison produced by L-043; it is a theorem premise here,
not an assumption added to the manuscript experiment.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L047

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal

open InfillGLSLean.ManuscriptSpecification.L037
open InfillGLSLean.ManuscriptSpecification.L027
open InfillGLSLean.ManuscriptSpecification.L039
open InfillGLSLean.ManuscriptSpecification.L040
open InfillGLSLean.ManuscriptSpecification.L041
open InfillGLSLean.ManuscriptSpecification.L042
open InfillGLSLean.ManuscriptSpecification.L043

universe u v

/-! ## Tail assembly independent of the spatial construction -/

/-- The tail form of L-040's fixed-refinement comparison theorem.  The source
only gives finite GLS positive definiteness after its displayed eventual
full-rank index, so this is the exact form needed by Appendix `lem:mean`.
It changes no observed experiment: a finite initial segment is discarded only
for an at-top limit. -/
theorem tendsto_observed_of_eventual_fixed_refinement_comparisons
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (observed refinement : ℕ → Matrix ι ι ℝ) (limit : Matrix ι ι ℝ)
    (start : ℕ)
    (hobserved_psd : ∀ n, start ≤ n → (observed n).PosSemidef)
    (hlimit_psd : limit.PosSemidef)
    (hlower : ∀ n, start ≤ n → (observed n - limit).PosSemidef)
    (hrefinement : Tendsto refinement atTop (nhds limit))
    (hupper : ∀ k (x : ι → ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        x ⬝ᵥ ((observed n) *ᵥ x) ≤ x ⬝ᵥ ((refinement k) *ᵥ x) + ε) :
    Tendsto observed atTop (nhds limit) := by
  let tail : ℕ → Matrix ι ι ℝ := fun n => observed (n + start)
  have htail_psd : ∀ n, (tail n).PosSemidef := by
    intro n
    exact hobserved_psd (n + start) (Nat.le_add_left start n)
  have htail_lower : ∀ n, (tail n - limit).PosSemidef := by
    intro n
    exact hlower (n + start) (Nat.le_add_left start n)
  have htail_upper : ∀ k (x : ι → ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        x ⬝ᵥ ((tail n) *ᵥ x) ≤ x ⬝ᵥ ((refinement k) *ᵥ x) + ε := by
    intro k x ε hε
    rcases (eventually_atTop.1 (hupper k x ε hε)) with ⟨N, hN⟩
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    exact hN (n + start) (le_trans hn (Nat.le_add_right n start))
  have htail :=
    tendsto_observed_of_fixed_refinement_comparisons
      tail refinement limit htail_psd hlimit_psd htail_lower hrefinement htail_upper
  exact (tendsto_add_atTop_iff_nat start).mp (by simpa [tail] using htail)

/-- The tail form of the paper's "first row and column vanish" conclusion.
The diagonal is the source's `v_n`; only its already-proved convergence to
zero is used. -/
theorem row_and_column_eq_zero_of_eventual_lower_order_and_tendsto_diagonal_zero
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (upper : ℕ → Matrix ι ι ℝ) (start : ℕ)
    (hB : B.PosSemidef)
    (hlower : ∀ n, start ≤ n → (upper n - B).PosSemidef)
    (i : ι) (hdiag : Tendsto (fun n => upper n i i) atTop (nhds 0)) :
    (∀ j, B i j = 0) ∧ (∀ j, B j i = 0) := by
  let tail : ℕ → Matrix ι ι ℝ := fun n => upper (n + start)
  have htail_lower : ∀ n, (tail n - B).PosSemidef := by
    intro n
    exact hlower (n + start) (Nat.le_add_left start n)
  have htail_diag : Tendsto (fun n => tail n i i) atTop (nhds 0) := by
    exact (tendsto_add_atTop_iff_nat start).mpr hdiag
  have hrow : ∀ j, B i j = 0 := by
    intro j
    exact lower_row_eq_zero_of_tendsto_upper_diagonal_zero B tail hB htail_lower i j htail_diag
  constructor
  · exact hrow
  · intro j
    have hsymm : Matrix.transpose B = B := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.eq
    calc
      B j i = (Matrix.transpose B) i j := rfl
      _ = B i j := by rw [hsymm]
      _ = 0 := hrow j

/-! ## Finite aggregation interface -/

/-- One exact deterministic aggregation step reverses the precision order of
the corresponding true-GLS coefficient covariance matrices.  This is merely
L-037's finite Gauss--Markov theorem with the source's design and covariance
equalities made explicit, so it does not introduce a statistical premise. -/
theorem trueGLSCoefficientCovariance_mono_of_exact_aggregation
    {ι κ p : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype p] [DecidableEq p]
    (fineCovariance : Matrix ι ι ℝ) (fineDesign : Matrix ι p ℝ)
    (aggregation : Matrix κ ι ℝ)
    (coarseCovariance : Matrix κ κ ℝ) (coarseDesign : Matrix κ p ℝ)
    (hcovariance : coarseCovariance =
      aggregation * fineCovariance * Matrix.transpose aggregation)
    (hdesign : coarseDesign = aggregation * fineDesign)
    (hfine_covariance : fineCovariance.PosDef)
    (hcoarse_covariance : coarseCovariance.PosDef)
    (hfine_gram : (trueGLSGram fineCovariance fineDesign).PosDef)
    (hcoarse_gram : (trueGLSGram coarseCovariance coarseDesign).PosDef) :
    (trueGLSCoefficientCovariance coarseCovariance coarseDesign -
      trueGLSCoefficientCovariance fineCovariance fineDesign).PosSemidef := by
  have hmono := trueGLSCoefficientCovariance_mono_of_linearObservation
    fineCovariance fineDesign aggregation hfine_covariance
    (by simpa [hcovariance] using hcoarse_covariance)
    hfine_gram
    (by simpa [hcovariance, hdesign] using hcoarse_gram)
  simpa [hcovariance, hdesign] using hmono

/-- Successive positive-semidefinite decreases telescope to every later
index.  This is the only order-theoretic induction needed to turn the literal
nested common-refinement steps into the decreasing sequence used by L-040. -/
theorem posSemidef_sub_of_eventual_successor_decrease
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (B : ℕ → Matrix ι ι ℝ) (start : ℕ)
    (hstep : ∀ n, start ≤ n → (B n - B (n + 1)).PosSemidef) :
    ∀ m n, start ≤ m → m ≤ n → (B m - B n).PosSemidef := by
  intro m n hm hmn
  induction n, hmn using Nat.le_induction with
  | base =>
      simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
  | succ n hmn ih =>
      have hstep' : (B n - B (n + 1)).PosSemidef :=
        hstep n (le_trans hm hmn)
      have hsum : ((B m - B n) + (B n - B (n + 1))).PosSemidef := ih.add hstep'
      have heq : B m - B (Nat.succ n) =
          (B m - B n) + (B n - B (n + 1)) := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.add_apply]
        rw [show Nat.succ n = n + 1 by omega]
        ring
      rw [heq]
      exact hsum

/-! ## Source-defined coefficient covariance sequences -/

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- `B_n` in Appendix `lem:mean`: the coefficient covariance of hypothetical
GLS under the true regional-error covariance at observed resolution `n`. -/
@[expose] noncomputable def observedTrueGLSCoefficientCovariance
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ :=
  trueGLSCoefficientCovariance (trueCovariance E n)
    (regionalDesign μ E.maps E.treatment E.controls n)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the retained true-GLS coefficient
covariance `B_n`. This Lean 4.35 visibility bridge preserves its literal
definition and adds no source premise. -/
theorem observedTrueGLSCoefficientCovariance_eq
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    observedTrueGLSCoefficientCovariance E n =
      trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) :=
  rfl

/-- The coefficient covariance of true GLS on one literal finite common
refinement.  This is the "inverse information matrix" used in the descending
common-refinement chain in the paper. -/
noncomputable def commonRefinementTrueGLSCoefficientCovariance
    (E : FixedConditionalExperiment μ P) {k : ℕ}
    (W : FirstCommonRefinement E.maps k) :
    Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ :=
  trueGLSCoefficientCovariance (partitionErrorCovariance E W.partition)
    (partitionDesign W.partition E.treatment E.controls)

/-- The recursively chosen nested common-refinement coefficient covariance
sequence. Its recursive construction is L-039's literal first-prefix
intersection construction, not a hypothesis that observed partitions nest. -/
noncomputable def commonRefinementCoefficientCovarianceSequence
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ :=
  commonRefinementTrueGLSCoefficientCovariance E
    (firstCommonRefinement E.maps n)

omit [IsProbabilityMeasure P] in
/-- At a source-full-rank observed resolution, the corresponding literal
common-refinement design is also full column rank.  This is L-039's finite
rank transfer, stated here in the notation used by the global assembly. -/
theorem commonRefinement_design_rank_eq_of_observed_rank
    (E : FixedConditionalExperiment μ P) {k : ℕ}
    (W : FirstCommonRefinement E.maps k)
    (i : Fin (k + 1))
    (hobserved :
      (regionalDesign μ E.maps E.treatment E.controls i.1).rank = E.q + 1) :
    (partitionDesign W.partition E.treatment E.controls).rank = E.q + 1 :=
  W.partitionDesign_rank_eq_of_observed_rank_eq E i hobserved

/-- Strict positive definiteness of the true-GLS Gram matrix on a literal
common refinement follows from the paper's existing strict spatial-average
variance assumption and from full rank transferred from an observed design. -/
theorem commonRefinement_trueGLSGram_posDef_of_observed_rank
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {k : ℕ} (W : FirstCommonRefinement E.maps k)
    (i : Fin (k + 1))
    (hobserved :
      (regionalDesign μ E.maps E.treatment E.controls i.1).rank = E.q + 1) :
    (trueGLSGram (partitionErrorCovariance E W.partition)
      (partitionDesign W.partition E.treatment E.controls)).PosDef := by
  apply glsGram_posDef_of_covariance_posDef_and_rank
  · exact partitionErrorCovariance_posDef E covariance W.partition
  · simpa using commonRefinement_design_rank_eq_of_observed_rank E W i hobserved

/-- On the same tail, each common-refinement coefficient covariance is
positive semidefinite. -/
theorem commonRefinement_coefficientCovariance_posSemidef_of_observed_rank
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {k : ℕ} (W : FirstCommonRefinement E.maps k)
    (i : Fin (k + 1))
    (hobserved :
      (regionalDesign μ E.maps E.treatment E.controls i.1).rank = E.q + 1) :
    (commonRefinementTrueGLSCoefficientCovariance E W).PosSemidef := by
  unfold commonRefinementTrueGLSCoefficientCovariance
  exact (commonRefinement_trueGLSGram_posDef_of_observed_rank E covariance W i
    hobserved).inv.posSemidef

omit [IsProbabilityMeasure P] in
/-- The source's eventual observed full-rank field transfers to the recursively
chosen common refinement at the same prefix index. -/
theorem commonRefinement_sequence_design_rank_eq_on_tail
    (E : FixedConditionalExperiment μ P) (start : ℕ)
    (hfull : ∀ n ≥ start,
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (n : ℕ) (hn : start ≤ n) :
    (partitionDesign (firstCommonRefinement E.maps n).partition
      E.treatment E.controls).rank = E.q + 1 := by
  have hlast :
      (regionalDesign μ E.maps E.treatment E.controls (Fin.last n).1).rank = E.q + 1 := by
    simpa using hfull n hn
  exact commonRefinement_design_rank_eq_of_observed_rank E
    (firstCommonRefinement E.maps n) (Fin.last n) hlast

/-- Positive semidefiniteness of the recursively chosen common-refinement
coefficient covariance sequence on the exact eventual-full-rank tail. -/
theorem commonRefinement_sequence_coefficientCovariance_posSemidef_on_tail
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (start : ℕ)
    (hfull : ∀ n ≥ start,
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (n : ℕ) (hn : start ≤ n) :
    (commonRefinementCoefficientCovarianceSequence E n).PosSemidef := by
  unfold commonRefinementCoefficientCovarianceSequence
  apply commonRefinement_coefficientCovariance_posSemidef_of_observed_rank E covariance
    (firstCommonRefinement E.maps n) (Fin.last n)
  simpa using hfull n hn

/-- One literal common-refinement extension can only decrease the true-GLS
coefficient covariance. The aggregation is L-039's retained binary
intersection map; the positive-definiteness and rank facts are all derived
from the source experiment. -/
theorem commonRefinement_sequence_successor_decrease_on_tail
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (start : ℕ)
    (hfull : ∀ n ≥ start,
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (n : ℕ) (hn : start ≤ n) :
    (commonRefinementCoefficientCovarianceSequence E n -
      commonRefinementCoefficientCovarianceSequence E (n + 1)).PosSemidef := by
  let W : FirstCommonRefinement E.maps n := firstCommonRefinement E.maps n
  let Wnext : FirstCommonRefinement E.maps (n + 1) :=
    firstCommonRefinement E.maps (n + 1)
  have hstep : W.RefinesThrough Wnext := by
    simpa [W, Wnext] using firstCommonRefinement_step E.maps n
  have hcovariance : partitionErrorCovariance E W.partition =
      hstep.aggregation * partitionErrorCovariance E Wnext.partition *
        Matrix.transpose hstep.aggregation := by
    change finiteErrorCovariance
        (fun r ω => cellMean μ (W.partition.cell r) (E.error ω)) P =
      hstep.aggregation *
        finiteErrorCovariance
          (fun s ω => cellMean μ (Wnext.partition.cell s) (E.error ω)) P *
        Matrix.transpose hstep.aggregation
    exact hstep.finiteErrorCovariance_eq_aggregation E
  have hdesign : partitionDesign W.partition E.treatment E.controls =
      hstep.aggregation * partitionDesign Wnext.partition E.treatment E.controls :=
    hstep.partitionDesign_eq_aggregation E
  have hW_rank :
      (partitionDesign W.partition E.treatment E.controls).rank = E.q + 1 := by
    apply commonRefinement_design_rank_eq_of_observed_rank E W (Fin.last n)
    simpa [W] using hfull n hn
  have hWnext_rank :
      (partitionDesign Wnext.partition E.treatment E.controls).rank = E.q + 1 := by
    apply commonRefinement_design_rank_eq_of_observed_rank E Wnext (Fin.last (n + 1))
    simpa [Wnext] using hfull (n + 1) (by omega)
  have hW_covariance : (partitionErrorCovariance E W.partition).PosDef :=
    partitionErrorCovariance_posDef E covariance W.partition
  have hWnext_covariance : (partitionErrorCovariance E Wnext.partition).PosDef :=
    partitionErrorCovariance_posDef E covariance Wnext.partition
  have hW_gram :
      (trueGLSGram (partitionErrorCovariance E W.partition)
        (partitionDesign W.partition E.treatment E.controls)).PosDef := by
    apply commonRefinement_trueGLSGram_posDef_of_observed_rank E covariance W (Fin.last n)
    simpa [W] using hfull n hn
  have hWnext_gram :
      (trueGLSGram (partitionErrorCovariance E Wnext.partition)
        (partitionDesign Wnext.partition E.treatment E.controls)).PosDef := by
    apply commonRefinement_trueGLSGram_posDef_of_observed_rank E covariance Wnext
      (Fin.last (n + 1))
    simpa [Wnext] using hfull (n + 1) (by omega)
  have hmono := trueGLSCoefficientCovariance_mono_of_exact_aggregation
    (partitionErrorCovariance E Wnext.partition)
    (partitionDesign Wnext.partition E.treatment E.controls)
    hstep.aggregation
    (partitionErrorCovariance E W.partition)
    (partitionDesign W.partition E.treatment E.controls)
    hcovariance hdesign hWnext_covariance hW_covariance hWnext_gram hW_gram
  change (commonRefinementTrueGLSCoefficientCovariance E W -
    commonRefinementTrueGLSCoefficientCovariance E Wnext).PosSemidef
  simpa [commonRefinementTrueGLSCoefficientCovariance] using hmono

/-- The nested common-refinement true-GLS coefficient covariance sequence is
decreasing in positive-semidefinite order once the source's existing
eventual-full-rank tail begins. -/
theorem commonRefinement_sequence_decreasing_on_tail
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (start : ℕ)
    (hfull : ∀ n ≥ start,
      (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    ∀ m n, start ≤ m → m ≤ n →
      (commonRefinementCoefficientCovarianceSequence E m -
        commonRefinementCoefficientCovarianceSequence E n).PosSemidef := by
  apply posSemidef_sub_of_eventual_successor_decrease
    (commonRefinementCoefficientCovarianceSequence E) start
  intro n hn
  exact commonRefinement_sequence_successor_decrease_on_tail E covariance
    start hfull n hn

/-- At a source-full-rank observed resolution, its true-GLS coefficient
covariance is positive semidefinite. -/
theorem observed_coefficientCovariance_posSemidef_of_rank
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {n : ℕ}
    (hrank : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    (observedTrueGLSCoefficientCovariance E n).PosSemidef := by
  unfold observedTrueGLSCoefficientCovariance
  exact (trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
    (trueCovariance_posDef E covariance n) hrank).inv.posSemidef

/-- Every observed experiment in a finite prefix is a deterministic linear
image of that prefix's literal common refinement.  Finite Gauss--Markov
minimality therefore gives the exact positive-semidefinite order used for the
paper's statement that the observed covariance matrix lies above the
common-refinement covariance matrix. -/
theorem observed_coefficientCovariance_sub_commonRefinement_posSemidef
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    {k : ℕ} (W : FirstCommonRefinement E.maps k)
    (i : Fin (k + 1))
    (hrank :
      (regionalDesign μ E.maps E.treatment E.controls i.1).rank = E.q + 1) :
    (observedTrueGLSCoefficientCovariance E i.1 -
      commonRefinementTrueGLSCoefficientCovariance E W).PosSemidef := by
  have hfine_covariance : (partitionErrorCovariance E W.partition).PosDef :=
    partitionErrorCovariance_posDef E covariance W.partition
  have hcoarse_covariance : (trueCovariance E i.1).PosDef :=
    trueCovariance_posDef E covariance i.1
  have hfine_gram :
      (trueGLSGram (partitionErrorCovariance E W.partition)
        (partitionDesign W.partition E.treatment E.controls)).PosDef :=
    commonRefinement_trueGLSGram_posDef_of_observed_rank E covariance W i hrank
  have hcoarse_gram :
      (trueGLSGram (trueCovariance E i.1)
        (regionalDesign μ E.maps E.treatment E.controls i.1)).PosDef :=
    trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
      hcoarse_covariance hrank
  have hmono := trueGLSCoefficientCovariance_mono_of_exact_aggregation
    (partitionErrorCovariance E W.partition)
    (partitionDesign W.partition E.treatment E.controls)
    (W.aggregation i)
    (trueCovariance E i.1)
    (regionalDesign μ E.maps E.treatment E.controls i.1)
    (W.trueCovariance_eq_aggregation E i)
    (W.regionalDesign_eq_aggregation E rfl i)
    hfine_covariance hcoarse_covariance hfine_gram hcoarse_gram
  simpa [observedTrueGLSCoefficientCovariance,
    commonRefinementTrueGLSCoefficientCovariance] using hmono

/-- The source-faithful first-prefix common-refinement construction has a
positive-semidefinite information-limit matrix `B`. Every tail common
refinement and every tail observed true-GLS experiment dominates `B` in
positive-semidefinite order. The finite initial segment is excluded only
because the manuscript itself states full rank eventually. -/
theorem exists_commonRefinement_information_limit
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∃ (start : ℕ) (B : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ),
      B.PosSemidef ∧
        (∀ n, start ≤ n →
          (commonRefinementCoefficientCovarianceSequence E n - B).PosSemidef) ∧
        Tendsto (commonRefinementCoefficientCovarianceSequence E) atTop (nhds B) ∧
        (∀ n, start ≤ n →
          (observedTrueGLSCoefficientCovariance E n - B).PosSemidef) ∧
        (∀ n, start ≤ n →
          (observedTrueGLSCoefficientCovariance E n).PosSemidef) := by
  rcases E.eventual_full_rank with ⟨start, hfull⟩
  have hpsd : ∀ n, start ≤ n →
      (commonRefinementCoefficientCovarianceSequence E n).PosSemidef := by
    intro n hn
    exact commonRefinement_sequence_coefficientCovariance_posSemidef_on_tail
      E covariance start hfull n hn
  have hdecreasing : ∀ m n, start ≤ m → m ≤ n →
      (commonRefinementCoefficientCovarianceSequence E m -
        commonRefinementCoefficientCovarianceSequence E n).PosSemidef :=
    commonRefinement_sequence_decreasing_on_tail E covariance start hfull
  rcases exists_coefficientCovariance_limit_of_eventually_decreasing
      (commonRefinementCoefficientCovarianceSequence E) start hpsd hdecreasing with
    ⟨B, hB, hcommon_lower, hcommon_tendsto⟩
  refine ⟨start, B, hB, hcommon_lower, hcommon_tendsto, ?_, ?_⟩
  · intro n hn
    let W : FirstCommonRefinement E.maps n := firstCommonRefinement E.maps n
    have hobserved_common :
        (observedTrueGLSCoefficientCovariance E n -
          commonRefinementTrueGLSCoefficientCovariance E W).PosSemidef := by
      have hlast :
          (regionalDesign μ E.maps E.treatment E.controls (Fin.last n).1).rank = E.q + 1 := by
        simpa using hfull n hn
      simpa [W] using
        observed_coefficientCovariance_sub_commonRefinement_posSemidef
          E covariance W (Fin.last n) hlast
    have hcommon :
        (commonRefinementTrueGLSCoefficientCovariance E W - B).PosSemidef := by
      simpa [commonRefinementCoefficientCovarianceSequence, W] using
        hcommon_lower n hn
    have hsum := hobserved_common.add hcommon
    have heq : observedTrueGLSCoefficientCovariance E n - B =
        (observedTrueGLSCoefficientCovariance E n -
          commonRefinementTrueGLSCoefficientCovariance E W) +
          (commonRefinementTrueGLSCoefficientCovariance E W - B) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply]
      ring
    rw [heq]
    exact hsum
  · intro n hn
    exact observed_coefficientCovariance_posSemidef_of_rank E covariance (hfull n hn)

/-- The paper's `v_n`: the treatment-coordinate diagonal entry of the true
GLS coefficient covariance `B_n`. This is a definition only, matching
`the source manuscript:535--536`. -/
@[expose] noncomputable def observedTrueGLSTreatmentVariance
    (E : FixedConditionalExperiment μ P) (n : ℕ) : ℝ :=
  observedTrueGLSCoefficientCovariance E n 0 0

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the paper's retained `v_n`. This
Lean 4.35 visibility bridge preserves the exact treatment diagonal and adds
no covariance, rank, or asymptotic premise. -/
theorem observedTrueGLSTreatmentVariance_eq
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    observedTrueGLSTreatmentVariance E n =
      observedTrueGLSCoefficientCovariance E n 0 0 :=
  rfl

/-- The working-covariance FWL outcome weight at one observed resolution.
This is the paper's `\omega_n` (not its proof-only true-GLS counterpart). -/
@[expose] noncomputable def observedWorkingGLSOutcomeWeight
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    Fin (E.maps.N n) → ℝ :=
  glsOutcomeWeight (E.kernel n)
    (regionalControls μ E.maps E.controls n)
    (regionalValues μ E.maps E.treatment n)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the paper's retained working FWL row.
Lean 4.35 requires this unchanged definition to be exposed when an exported
source bridge uses its literal `glsOutcomeWeight` body. -/
theorem observedWorkingGLSOutcomeWeight_eq
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    observedWorkingGLSOutcomeWeight E n =
      glsOutcomeWeight (E.kernel n)
        (regionalControls μ E.maps E.controls n)
        (regionalValues μ E.maps E.treatment n) := rfl

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- On a source-full-rank resolution, the literal working GLS outcome weight
has exactly the `1 / Q_n` working-covariance energy from `eq:weights`. -/
theorem observedWorkingGLSOutcomeWeight_quadraticForm_eq_inv_information
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    quadraticForm (E.kernel n) (observedWorkingGLSOutcomeWeight E n) =
      1 / E.information n := by
  let controls := regionalControls μ E.maps E.controls n
  let treatment := regionalValues μ E.maps E.treatment n
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign treatment controls).rank = E.q + 1 := by
    change (InfillGLSLean.L023.sourceDesign
      (regionalValues μ E.maps E.treatment n)
      (regionalControls μ E.maps E.controls n)).rank = E.q + 1 at hfull
    exact hfull
  have hprecision : (E.kernel n)⁻¹ |>.PosDef := (E.kernel_posDef n).inv
  rcases InfillGLSLean.L023.sourceDesign_fwl_nonsingularity_and_relevance_of_full_rank
    treatment controls (E.kernel n)⁻¹ hprecision hfull_source with ⟨_, hresidual⟩
  have hinformation :
      E.information n = InfillGLSLean.controlInformation (E.kernel n)⁻¹ controls treatment :=
    information_eq_controlInformation_of_full_rank E n hfull
  change quadraticForm (E.kernel n)
      (glsOutcomeWeight (E.kernel n)
        (regionalControls μ E.maps E.controls n)
        (regionalValues μ E.maps E.treatment n)) = 1 / E.information n
  rw [glsOutcomeWeight_quadraticForm_eq_inv_information (E.kernel n)
    (E.kernel_posDef n) controls treatment hresidual, hinformation]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The working FWL outcome weight is an unbiased treatment-coordinate row:
its score on the complete observed design is the first standard coordinate.
This is only the two exact `eq:weight-identities` specialized to
`[X_n\;W_n]`. -/
theorem transpose_regionalDesign_mulVec_observedWorkingGLSOutcomeWeight_eq_first
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    Matrix.transpose (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
        observedWorkingGLSOutcomeWeight E n =
      fun j => if j = 0 then 1 else 0 := by
  classical
  let controls := regionalControls μ E.maps E.controls n
  let treatment := regionalValues μ E.maps E.treatment n
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign treatment controls).rank = E.q + 1 := by
    change (InfillGLSLean.L023.sourceDesign
      (regionalValues μ E.maps E.treatment n)
      (regionalControls μ E.maps E.controls n)).rank = E.q + 1 at hfull
    exact hfull
  have hprecision : (E.kernel n)⁻¹ |>.PosDef := (E.kernel_posDef n).inv
  rcases InfillGLSLean.L023.sourceDesign_fwl_nonsingularity_and_relevance_of_full_rank
    treatment controls (E.kernel n)⁻¹ hprecision hfull_source with ⟨hgram, hresidual⟩
  ext j
  refine Fin.cases ?_ ?_ j
  · have hunit := glsOutcomeWeight_dot_treatment_eq_one
      (E.kernel n) (E.kernel_posDef n) controls treatment hgram hresidual
    have hunit' : dotProduct treatment
        (glsOutcomeWeight (E.kernel n) controls treatment) = 1 := by
      rw [dotProduct_comm]
      exact hunit
    simpa [Matrix.mulVec, Matrix.transpose_apply, regionalDesign_apply,
      Fin.cases_zero, dotProduct, observedWorkingGLSOutcomeWeight,
      controls, treatment] using hunit'
  · intro c
    have hcontrols := glsOutcomeWeight_controls_transpose_eq_zero
      (E.kernel n) controls treatment hgram
    change (Matrix.transpose controls *ᵥ observedWorkingGLSOutcomeWeight E n) c = 0
    change (Matrix.transpose controls *ᵥ glsOutcomeWeight (E.kernel n) controls treatment) c = 0
    simpa using congrFun hcontrols c

/-- The source covariance sandwich and diverging information force the
paper's true-GLS treatment variance `v_n` to vanish.  The only comparison is
finite Gauss--Markov minimality against the literal working GLS treatment
weight; no rate, rank, or covariance premise beyond the manuscript's existing
tail fields is introduced. -/
theorem observedTrueGLSTreatmentVariance_tendsto_zero
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    Tendsto (observedTrueGLSTreatmentVariance E) atTop (nhds 0) := by
  have hinv : Tendsto (fun n => (E.information n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp E.information_tendsto
  have henvelope : Tendsto
      (fun n => (2 * covariance.sigmaSquared) / E.information n)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  have hnonnegative : ∀ᶠ n in atTop, 0 ≤ observedTrueGLSTreatmentVariance E n := by
    filter_upwards [eventually_ge_atTop rankStart] with n hn
    change 0 ≤ observedTrueGLSCoefficientCovariance E n 0 0
    exact (observed_coefficientCovariance_posSemidef_of_rank E covariance
      (hfull n hn)).diag_nonneg
  have hdelta_half : ∀ᶠ n in atTop, covariance.delta n < (1 / 2 : ℝ) :=
    (tendsto_order.mp covariance.delta_tendsto_zero).2 (1 / 2 : ℝ) (by norm_num)
  have hinformation_pos : ∀ᶠ n in atTop, 0 < E.information n :=
    E.information_tendsto.eventually (eventually_gt_atTop (0 : ℝ))
  have hupper : ∀ᶠ n in atTop,
      observedTrueGLSTreatmentVariance E n ≤
        (2 * covariance.sigmaSquared) / E.information n := by
    filter_upwards [eventually_ge_atTop covariance.start, hdelta_half,
      eventually_ge_atTop rankStart, hinformation_pos] with n hstart hdelta hnrank hinfo
    rcases covariance.sandwich n hstart with ⟨_, _, _, hsandwich_upper⟩
    have htrueCovariance : (trueCovariance E n).PosDef :=
      trueCovariance_posDef E covariance n
    have htrueGram :
        (trueGLSGram (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n)).PosDef :=
      trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
        htrueCovariance (hfull n hnrank)
    have hfeasible : Matrix.transpose
        (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
          observedWorkingGLSOutcomeWeight E n =
        Pi.single (0 : Fin (E.q + 1)) 1 := by
      rw [transpose_regionalDesign_mulVec_observedWorkingGLSOutcomeWeight_eq_first
        E n (hfull n hnrank)]
      ext j
      by_cases hj : j = 0
      · subst j
        simp
      · simp [hj]
    have hminimal : observedTrueGLSTreatmentVariance E n ≤
        quadraticForm (trueCovariance E n) (observedWorkingGLSOutcomeWeight E n) := by
      change trueGLSCoefficientCovariance (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) 0 0 ≤ _
      exact trueGLSCoefficientCovariance_diag_le_quadraticForm_of_feasible
        (trueCovariance E n) (regionalDesign μ E.maps E.treatment E.controls n)
        htrueCovariance htrueGram 0 (observedWorkingGLSOutcomeWeight E n) hfeasible
    have hweight : quadraticForm (E.kernel n) (observedWorkingGLSOutcomeWeight E n) =
        1 / E.information n :=
      observedWorkingGLSOutcomeWeight_quadraticForm_eq_inv_information E n
        (hfull n hnrank)
    have hworking_upper : quadraticForm (trueCovariance E n)
        (observedWorkingGLSOutcomeWeight E n) ≤
        (covariance.sigmaSquared / (1 - covariance.delta n)) / E.information n :=
      quadraticForm_le_scale_div_information hsandwich_upper
        (observedWorkingGLSOutcomeWeight E n) hweight
    have hdenom : 0 < 1 - covariance.delta n := by linarith
    have hfactor : covariance.sigmaSquared / (1 - covariance.delta n) ≤
        2 * covariance.sigmaSquared := by
      apply (div_le_iff₀ hdenom).2
      nlinarith [covariance.sigmaSquared_pos]
    exact hminimal.trans (hworking_upper.trans
      (div_le_div_of_nonneg_right hfactor hinfo.le))
  exact squeeze_zero' hnonnegative hupper henvelope

/-- Global information-limit assembly, conditional only on the epsilon-tail
fixed-refinement comparison that L-043 proves from projected regional
averages. The premise is exactly the paper's limsup comparison for every
fixed common refinement; it is not stored in `FixedConditionalExperiment` or
introduced as a new manuscript assumption. -/
theorem exists_commonRefinement_information_limit_and_tendsto_observed
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (hupper : ∀ k (x : Fin (E.q + 1) → ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        x ⬝ᵥ ((observedTrueGLSCoefficientCovariance E n) *ᵥ x) ≤
          x ⬝ᵥ ((commonRefinementCoefficientCovarianceSequence E k) *ᵥ x) + ε) :
    ∃ (start : ℕ) (B : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ),
      B.PosSemidef ∧
        (∀ n, start ≤ n →
          (commonRefinementCoefficientCovarianceSequence E n - B).PosSemidef) ∧
        Tendsto (commonRefinementCoefficientCovarianceSequence E) atTop (nhds B) ∧
        (∀ n, start ≤ n →
          (observedTrueGLSCoefficientCovariance E n - B).PosSemidef) ∧
        Tendsto (observedTrueGLSCoefficientCovariance E) atTop (nhds B) := by
  rcases exists_commonRefinement_information_limit E covariance with
    ⟨start, B, hB, hcommon_lower, hcommon_tendsto, hobserved_lower, hobserved_psd⟩
  refine ⟨start, B, hB, hcommon_lower, hcommon_tendsto, hobserved_lower, ?_⟩
  exact tendsto_observed_of_eventual_fixed_refinement_comparisons
    (observedTrueGLSCoefficientCovariance E)
    (commonRefinementCoefficientCovarianceSequence E) B start
    hobserved_psd hB hobserved_lower hcommon_tendsto hupper

/-- The preceding generic assembly with its L-043 premise discharged by the
exported fixed-common-refinement projection theorem.  The proof shifts only
the *nested auxiliary sequence* past the source full-rank threshold; it makes
no nesting or rate assertion about observed regional partitions. -/
theorem exists_commonRefinement_information_limit_and_tendsto_observed_of_source_comparison
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∃ (start : ℕ) (B : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ),
      B.PosSemidef ∧
        (∀ n, start ≤ n →
          (commonRefinementCoefficientCovarianceSequence E n - B).PosSemidef) ∧
        Tendsto (commonRefinementCoefficientCovarianceSequence E) atTop (nhds B) ∧
        (∀ n, start ≤ n →
          (observedTrueGLSCoefficientCovariance E n - B).PosSemidef) ∧
        Tendsto (observedTrueGLSCoefficientCovariance E) atTop (nhds B) := by
  rcases exists_commonRefinement_information_limit E covariance with
    ⟨commonStart, B, hB, hcommon_lower, hcommon_tendsto,
      hobserved_lower, hobserved_psd⟩
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  let start := max commonStart rankStart
  have hcommon_lower_start : ∀ n, start ≤ n →
      (commonRefinementCoefficientCovarianceSequence E n - B).PosSemidef := by
    intro n hn
    exact hcommon_lower n (le_trans (le_max_left _ _) hn)
  have hobserved_lower_start : ∀ n, start ≤ n →
      (observedTrueGLSCoefficientCovariance E n - B).PosSemidef := by
    intro n hn
    exact hobserved_lower n (le_trans (le_max_left _ _) hn)
  have hobserved_psd_start : ∀ n, start ≤ n →
      (observedTrueGLSCoefficientCovariance E n).PosSemidef := by
    intro n hn
    exact hobserved_psd n (le_trans (le_max_left _ _) hn)
  have hshifted_common_tendsto :
      Tendsto (fun k => commonRefinementCoefficientCovarianceSequence E (k + start))
        atTop (nhds B) :=
    (tendsto_add_atTop_iff_nat start).mpr hcommon_tendsto
  refine ⟨start, B, hB, hcommon_lower_start, hcommon_tendsto,
    hobserved_lower_start, ?_⟩
  apply tendsto_observed_of_eventual_fixed_refinement_comparisons
    (observedTrueGLSCoefficientCovariance E)
    (fun k => commonRefinementCoefficientCovarianceSequence E (k + start)) B start
    hobserved_psd_start hB hobserved_lower_start hshifted_common_tendsto
  intro k x ε hε
  let W : FirstCommonRefinement E.maps (k + start) :=
    firstCommonRefinement E.maps (k + start)
  have hrank :
      (regionalDesign μ E.maps E.treatment E.controls (Fin.last (k + start)).1).rank =
        E.q + 1 := by
    simpa using hfull (k + start)
      (le_trans (le_max_right commonStart rankStart) (Nat.le_add_left start k))
  have hcomparison :=
    InfillGLSLean.ManuscriptSpecification.L043.FirstCommonRefinement.eventually_quadraticForm_trueGLS_le_fixed_add_of_observed_rank_eq
      E covariance W (Fin.last (k + start)) hrank x ε hε
  simpa [quadraticForm_eq_dotProduct_mulVec, W,
    observedTrueGLSCoefficientCovariance,
    commonRefinementCoefficientCovarianceSequence,
    commonRefinementTrueGLSCoefficientCovariance] using hcomparison

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Once the already-derived treatment variance `v_n` tends to zero, the first
row and column of the global information-limit matrix vanish. This is the
last sentence of the common-refinement paragraph in Appendix `lem:mean`; its
proof uses only the established PSD lower order and does not require a rate. -/
theorem treatment_row_and_column_vanish_of_information_limit
    (E : FixedConditionalExperiment μ P) (B : Matrix (Fin (E.q + 1))
      (Fin (E.q + 1)) ℝ) (start : ℕ)
    (hB : B.PosSemidef)
    (hlower : ∀ n, start ≤ n →
      (observedTrueGLSCoefficientCovariance E n - B).PosSemidef)
    (hvariance : Tendsto (observedTrueGLSTreatmentVariance E) atTop (nhds 0)) :
    (∀ j, B 0 j = 0) ∧ (∀ j, B j 0 = 0) := by
  apply row_and_column_eq_zero_of_eventual_lower_order_and_tendsto_diagonal_zero
    B (observedTrueGLSCoefficientCovariance E) start hB hlower 0
  change Tendsto (fun n => observedTrueGLSCoefficientCovariance E n 0 0)
    atTop (nhds 0) at hvariance
  exact hvariance

/-- Full source-level endpoint for the global common-refinement paragraph of
Appendix `lem:mean`.  The fixed-refinement comparison is the exported L-043
theorem, and the zero treatment row/column follows from the source-derived
`v_n → 0` bridge above.  Thus the statement adds no external convergence,
nesting, rank, or covariance premise. -/
theorem exists_commonRefinement_information_limit_tendsto_observed_and_treatment_row_column_zero
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∃ (start : ℕ) (B : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ),
      B.PosSemidef ∧
        (∀ n, start ≤ n →
          (commonRefinementCoefficientCovarianceSequence E n - B).PosSemidef) ∧
        Tendsto (commonRefinementCoefficientCovarianceSequence E) atTop (nhds B) ∧
        (∀ n, start ≤ n →
          (observedTrueGLSCoefficientCovariance E n - B).PosSemidef) ∧
        Tendsto (observedTrueGLSCoefficientCovariance E) atTop (nhds B) ∧
        (∀ j, B 0 j = 0) ∧ (∀ j, B j 0 = 0) := by
  rcases exists_commonRefinement_information_limit_and_tendsto_observed_of_source_comparison
      E covariance with
    ⟨start, B, hB, hcommon_lower, hcommon_tendsto, hobserved_lower,
      hobserved_tendsto⟩
  refine ⟨start, B, hB, hcommon_lower, hcommon_tendsto, hobserved_lower,
    hobserved_tendsto, ?_⟩
  exact treatment_row_and_column_vanish_of_information_limit E B start hB
    hobserved_lower (observedTrueGLSTreatmentVariance_tendsto_zero E covariance)

end InfillGLSLean.ManuscriptSpecification.L047

end
