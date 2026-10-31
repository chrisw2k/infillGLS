module

public import InfillGLSLean.MultiControlGLS
public import InfillGLSLean.FiniteRandomScore
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.AEDisjoint
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Distributions.Gaussian.Real

/- The source specification is intentionally a separate module, but its
definitions are public so source-grounded proof modules can state lemmas over
the exact transcription rather than local mirrors. This changes no
assumption, definition body, or proposition statement. -/
public section

/-!
# Source-faithful transcription of the manuscript statements

This specification file contains the exact source-facing definitions and
proposition-shaped `Prop`s, plus public `rfl` API expansions for
`regionalMeanCompatibility`; the finite GLS/FWL support interfaces
(`regionalControls`, `regionalDesign`, `glsObjective`, `IsGLSMinimizer`,
`IsTreatmentInformation`, `fwlSlope`, and `estimatorHasFWLForm`); the
centered-integral interfaces; the true regional covariance interface; and the
consistency-expression interfaces needed by the existing completed L-029
proof.  It contains no substantive manuscript proof,
no unproved declarations, and no placeholders.  Its purpose is to make the manuscript's
exact hypotheses and conclusions reviewable and usable by proof modules
without local mirrors. It also records the ordinary convention that
a selected estimator is measurable, as documented by L-031; this is needed
to express the paper's distributional conclusions in Mathlib and does not
change a displayed paper assumption or conclusion.

The conditioning on complete `X, W` in the paper is represented by fixing a
probability measure `P` for the outcome experiment.  This file does not claim
to construct a regular conditional distribution.

Source: `the source manuscript`, especially `reg:maps`, `reg:information`,
`ass:upper`, `ass:weak-mean`, `ass:covariance`, `ass:mean`, and
`prop:consistency`--`prop:variance`.
-/

namespace InfillGLSLean.ManuscriptSpecification

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

universe u v

variable {α : Type u} [MeasurableSpace α]

/-! ## Spatial domain, partitions, and regional averages -/

/-- The paper's compact set `T ⊂ ℝ^d`.  The spatial type below is its subtype,
so its metric and Borel structure are the relative Euclidean ones. -/
structure CompactEuclideanDomain where
  dimension : ℕ
  carrier : Set (EuclideanSpace ℝ (Fin dimension))
  compact_carrier : IsCompact carrier

/-- Points of the compact spatial domain. -/
abbrev Point (D : CompactEuclideanDomain) : Type := D.carrier

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ℕ}

/-- A direct atomless splitting formulation of the manuscript's
"nonatomic Borel probability measure" condition.  This deliberately does
not substitute Mathlib's weaker null-singleton class. -/
def IsNonatomic (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet s → 0 < μ s →
    ∃ u : Set α, u ⊆ s ∧ MeasurableSet u ∧ 0 < μ u ∧ μ u < μ s

/-- One labeled finite Borel partition, allowing overlaps and uncovered
points only on `μ`-null sets, exactly as in the manuscript. -/
structure AERegionalPartition {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (N : ℕ) where
  cell : Fin N → Set (Point D)
  measurable_cell : ∀ i, MeasurableSet (cell i)
  aedisjoint_cell : ∀ ⦃i j⦄, i ≠ j → AEDisjoint μ (cell i) (cell j)
  union_measure_one : μ (⋃ i, cell i) = 1
  positive_measure : ∀ i, 0 < μ (cell i)

/-- The deterministic sequence of partitions in `reg:maps`.  In particular,
there is intentionally no nesting or mesh-size field. -/
structure RegionalMaps {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) where
  N : ℕ → ℕ
  partition : (n : ℕ) → AERegionalPartition μ (N n)
  cell_count_tendsto : Tendsto N atTop atTop
  large_cell_mass_tendsto : ∀ h : ℝ, 0 < h →
    Tendsto
      (fun n => ∑ i : Fin (N n),
        if h < Metric.diam ((partition n).cell i)
        then μ.real ((partition n).cell i) else 0)
      atTop (nhds 0)

/-- The literal regional average from equation `eq:averages`.  Positivity of
partition cells makes this the paper's `1 / μ(R)` expression. -/
@[expose]
noncomputable def cellMean {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (R : Set (Point D)) (f : Point D → ℝ) : ℝ :=
  ⨍ s in R, f s ∂μ

/-- Stack the regional means of a deterministic spatial function. -/
@[expose]
noncomputable def regionalValues {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (maps : RegionalMaps μ) (f : Point D → ℝ) (n : ℕ) :
    Fin (maps.N n) → ℝ :=
  fun i => cellMean μ ((maps.partition n).cell i) f

/-- Stack the regional means of an outcome-indexed spatial random function. -/
@[expose]
noncomputable def regionalRandomValues {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (maps : RegionalMaps μ)
    (field : Ω → Point D → ℝ) (n : ℕ) :
    Fin (maps.N n) → Ω → ℝ :=
  fun i ω => cellMean μ ((maps.partition n).cell i) (field ω)

/-- The regional control matrix formed from one fixed family of spatial
control functions. -/
@[expose]
noncomputable def regionalControls {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (maps : RegionalMaps μ)
    (controls : Fin q → Point D → ℝ) (n : ℕ) :
    Matrix (Fin (maps.N n)) (Fin q) ℝ :=
  fun i j => regionalValues μ maps (controls j) n i

omit [IsProbabilityMeasure μ] in
/-- Public definitional expansion of one existing regional-control entry.  It
is an API-only `rfl` bridge for finite GLS translations. -/
@[simp]
theorem regionalControls_apply {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (maps : RegionalMaps μ)
    (controls : Fin q → Point D → ℝ) (n : ℕ)
    (i : Fin (maps.N n)) (j : Fin q) :
    regionalControls μ maps controls n i j = regionalValues μ maps (controls j) n i :=
  rfl

/-- The exact `[X_n W_n]` matrix from `reg:maps`; the first column is the
treatment and the remaining fixed columns are controls. -/
@[expose]
noncomputable def regionalDesign {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (maps : RegionalMaps μ) (treatment : Point D → ℝ)
    (controls : Fin q → Point D → ℝ) (n : ℕ) :
    Matrix (Fin (maps.N n)) (Fin (q + 1)) ℝ :=
  fun i j =>
    Fin.cases (regionalValues μ maps treatment n i)
      (fun k => regionalControls μ maps controls n i k) j

omit [IsProbabilityMeasure μ] in
/-- Public definitional expansion of one entry of the existing regional design.
This API-only `rfl` bridge supports the finite FWL translation and changes no
design formula or manuscript statement. -/
@[simp]
theorem regionalDesign_apply {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (maps : RegionalMaps μ) (treatment : Point D → ℝ)
    (controls : Fin q → Point D → ℝ) (n : ℕ)
    (i : Fin (maps.N n)) (j : Fin (q + 1)) :
    regionalDesign μ maps treatment controls n i j =
      Fin.cases (regionalValues μ maps treatment n i)
        (fun k => regionalControls μ maps controls n i k) j :=
  rfl

/-! ## The fixed conditional outcome experiment -/

/-- The fixed-law reading of the manuscript's conditional mean.
`P` is the conditional outcome law after `X, W` have been fixed. -/
@[expose]
noncomputable def conditionalErrorMean (P : Measure Ω)
    (error : Ω → Point D → ℝ) : Point D → ℝ :=
  fun s => ∫ ω, error ω s ∂P

/-- The regional averages of the fixed-law conditional mean function. -/
@[expose]
noncomputable def regionalMeanFromSpatialConditionalMean (maps : RegionalMaps μ)
    (P : Measure Ω) (error : Ω → Point D → ℝ) (n : ℕ) :
    Fin (maps.N n) → ℝ :=
  regionalValues μ maps (conditionalErrorMean P error) n

/-- The regional conditional-error mean in equation `eq:conditional-mean`:
the fixed-law expectation of each regional error. -/
@[expose]
noncomputable def regionalConditionalMean (maps : RegionalMaps μ)
    (P : Measure Ω) (error : Ω → Point D → ℝ) (n : ℕ) :
    Fin (maps.N n) → ℝ :=
  fun i => ∫ ω, regionalRandomValues μ maps error n i ω ∂P

/-- A test function in `L²(T, μ)` for the manuscript's Gaussian-field clause. -/
abbrev L2TestFunction (μ : Measure (Point D)) :=
  {h : Point D → ℝ // MemLp h 2 μ}

/-- The centered spatial integral against one `L²` test function. -/
@[expose]
noncomputable def centeredTestIntegral (μ : Measure (Point D)) (P : Measure Ω)
    (error : Ω → Point D → ℝ) (h : L2TestFunction μ) : Ω → ℝ :=
  fun ω => ∫ s, h.1 s * (error ω s - conditionalErrorMean P error s) ∂μ

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of one centered `L²` test integral.  This
is an API-only `rfl` bridge for source-aligned proofs; it changes neither the
Gaussian-field assumption nor the displayed integral formula. -/
@[simp]
theorem centeredTestIntegral_apply (μ : Measure (Point D)) (P : Measure Ω)
    (error : Ω → Point D → ℝ) (h : L2TestFunction μ) (ω : Ω) :
    centeredTestIntegral μ P error h ω =
      ∫ s, h.1 s * (error ω s - conditionalErrorMean P error s) ∂μ :=
  rfl

/-- The process indexed by all `L²` test functions.  `IsGaussianProcess` for
this process is the source's clause that every finite family of such integrals
is jointly Gaussian. -/
@[expose]
noncomputable def centeredIntegralProcess (μ : Measure (Point D))
    (P : Measure Ω) (error : Ω → Point D → ℝ) :
    L2TestFunction μ → Ω → ℝ :=
  fun h => centeredTestIntegral μ P error h

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the centered process at one test
function.  This merely exposes the existing `rfl` relation for external
proofs; no statistical statement is added. -/
@[simp]
theorem centeredIntegralProcess_apply (μ : Measure (Point D))
    (P : Measure Ω) (error : Ω → Point D → ℝ) (h : L2TestFunction μ) (ω : Ω) :
    centeredIntegralProcess μ P error h ω = centeredTestIntegral μ P error h ω :=
  rfl

/-- Conditional variance under the fixed outcome law `P`. -/
@[expose]
noncomputable def varianceUnder (P : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, (f ω - ∫ z, f z ∂P) ^ 2 ∂P

/-- Public definitional expansion of the conditional variance used in the
strict-variance clause.  This API-only bridge exposes the existing formula
without changing any covariance assumption or manuscript conclusion. -/
theorem varianceUnder_eq (P : Measure Ω) (f : Ω → ℝ) :
    varianceUnder P f = ∫ ω, (f ω - ∫ z, f z ∂P) ^ 2 ∂P :=
  rfl

/-- Nonzero in `L²(T, μ)`, expressed as failure to be zero almost everywhere. -/
def NonzeroInL2 (μ : Measure (Point D)) (h : L2TestFunction μ) : Prop :=
  ¬ (h.1 =ᵐ[μ] fun _ => 0)

/-- Public definitional expansion of nonzero spatial `L²` test status.
This is an API-only `Iff.rfl` bridge for the strict-variance clause; it
changes neither a covariance assumption nor a manuscript statement. -/
theorem nonzeroInL2_iff (μ : Measure (Point D)) (h : L2TestFunction μ) :
    NonzeroInL2 μ h ↔ ¬ (h.1 =ᵐ[μ] fun _ => 0) :=
  Iff.rfl

/-- The finite GLS objective in equation `eq:estimator`. -/
@[expose]
noncomputable def glsObjective {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (x : ι → ℝ) (W : Matrix ι κ ℝ)
    (y : ι → ℝ) (b : ℝ) (g : κ → ℝ) : ℝ :=
  quadraticForm K⁻¹ (y - b • x - W *ᵥ g)

/-- Public definitional expansion of the existing finite GLS objective.  This
is an API-only `rfl` bridge for the exact minimizer translation. -/
@[simp]
theorem glsObjective_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (x : ι → ℝ) (W : Matrix ι κ ℝ)
    (y : ι → ℝ) (b : ℝ) (g : κ → ℝ) :
    glsObjective K x W y b g = quadraticForm K⁻¹ (y - b • x - W *ᵥ g) :=
  rfl

/-- A selected minimizer of the exact GLS objective.  This is a predicate,
not an existence assertion or a replacement estimator. -/
@[expose]
def IsGLSMinimizer {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (x : ι → ℝ) (W : Matrix ι κ ℝ)
    (y : ι → ℝ) (b : ℝ) (g : κ → ℝ) : Prop :=
  ∀ b' : ℝ, ∀ g' : κ → ℝ,
    glsObjective K x W y b g ≤ glsObjective K x W y b' g'

/-- Public definitional expansion of the selected-minimizer predicate.  It
only exposes the existing `eq:estimator` formula for external exact proofs. -/
theorem isGLSMinimizer_iff {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (x : ι → ℝ) (W : Matrix ι κ ℝ)
    (y : ι → ℝ) (b : ℝ) (g : κ → ℝ) :
    IsGLSMinimizer K x W y b g ↔
      ∀ b' : ℝ, ∀ g' : κ → ℝ,
        glsObjective K x W y b g ≤ glsObjective K x W y b' g' :=
  Iff.rfl

/-- The literal "minimum over ℓ" definition of `Q_n`, represented by a
value together with attainment and the lower-bound property. -/
@[expose]
def IsTreatmentInformation {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (x : ι → ℝ) (W : Matrix ι κ ℝ) (Q : ℝ) : Prop :=
  (∃ ℓ : κ → ℝ, Q = quadraticForm K⁻¹ (x - W *ᵥ ℓ)) ∧
    ∀ ℓ : κ → ℝ, Q ≤ quadraticForm K⁻¹ (x - W *ᵥ ℓ)

/-- Public definitional expansion of the attained information minimum.  This
is an API-only `rfl` interface for the existing `eq:information` formula. -/
theorem isTreatmentInformation_iff {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (K : Matrix ι ι ℝ) (x : ι → ℝ) (W : Matrix ι κ ℝ) (Q : ℝ) :
    IsTreatmentInformation K x W Q ↔
      (∃ ℓ : κ → ℝ, Q = quadraticForm K⁻¹ (x - W *ᵥ ℓ)) ∧
        ∀ ℓ : κ → ℝ, Q ≤ quadraticForm K⁻¹ (x - W *ᵥ ℓ) :=
  Iff.rfl

/-- Everything fixed after conditioning on `X, W` that is required by
`reg:maps`, `reg:information`, and the estimator definitions.  The fields
are intentionally source-facing; no finite-dimensional equivalences are
inserted as assumptions. -/
structure FixedConditionalExperiment {D : CompactEuclideanDomain}
    (μ : Measure (Point D)) (P : Measure Ω) where
  maps : RegionalMaps μ
  nonatomic_spatial_measure : IsNonatomic μ
  q : ℕ
  treatment : Point D → ℝ
  controls : Fin q → Point D → ℝ
  outcome : Ω → Point D → ℝ
  error : Ω → Point D → ℝ
  beta : ℝ
  gamma : Fin q → ℝ
  treatment_measurable : Measurable treatment
  controls_measurable : ∀ j, Measurable (controls j)
  outcome_jointly_measurable : Measurable (fun z : Ω × Point D => outcome z.1 z.2)
  error_jointly_measurable : Measurable (fun z : Ω × Point D => error z.1 z.2)
  regressor_second_moment :
    (∫⁻ s, ENNReal.ofReal
      (treatment s ^ 2 + ∑ j : Fin q, controls j s ^ 2) ∂μ) < ∞
  conditional_error_second_moment :
    (∫⁻ ω, ∫⁻ s, ENNReal.ofReal (error ω s ^ 2) ∂μ ∂P) < ∞
  structural_model : ∀ᵐ ω ∂P, ∀ᵐ s ∂μ,
    outcome ω s = beta * treatment s +
      dotProduct (fun j => controls j s) gamma + error ω s
  eventual_full_rank : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (regionalDesign μ maps treatment controls n).rank = q + 1
  kernel : (n : ℕ) → Matrix (Fin (maps.N n)) (Fin (maps.N n)) ℝ
  kernel_posDef : ∀ n, (kernel n).PosDef
  information : ℕ → ℝ
  information_is_minimum : ∀ n,
    IsTreatmentInformation (kernel n) (regionalValues μ maps treatment n)
      (regionalControls μ maps controls n) (information n)
  information_tendsto : Tendsto information atTop atTop
  betaHat : (n : ℕ) → Ω → ℝ
  gammaHat : (n : ℕ) → Ω → Fin q → ℝ
  /-- The selected slope estimator is an a.e.-measurable statistic at every
  resolution.  This formalizes the ordinary meaning of “estimator”, including
  any finite prefix before eventual full rank; it introduces no covariance,
  Gaussianity, or asymptotic restriction. -/
  betaHat_aemeasurable : ∀ n, AEMeasurable (betaHat n) P
  /-- The selected control estimator is likewise a.e.-measurable at every
  resolution.  This supports measurability of fitted residuals and reported
  variance without changing any manuscript formula. -/
  gammaHat_aemeasurable : ∀ n, AEMeasurable (gammaHat n) P
  estimator_minimizes : ∀ n ω,
    IsGLSMinimizer (kernel n) (regionalValues μ maps treatment n)
      (regionalControls μ maps controls n)
      (fun i => regionalRandomValues μ maps outcome n i ω)
      (betaHat n ω) (gammaHat n ω)
  early_scale_fallback : ℝ
  early_scale_fallback_pos : 0 < early_scale_fallback

/-! ## Derived quantities named in the paper -/

/-- The true conditional covariance `Σ_n` from `eq:true-covariance`. -/
@[expose]
noncomputable def trueCovariance
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    Matrix (Fin (E.maps.N n)) (Fin (E.maps.N n)) ℝ :=
  finiteErrorCovariance (regionalRandomValues μ E.maps E.error n) P

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the manuscript's true regional covariance
matrix.  This is an API-only `rfl` bridge for covariance comparisons; it
leaves `Σ_n`, its formula, and every manuscript statement unchanged. -/
@[simp]
theorem trueCovariance_eq (E : FixedConditionalExperiment μ P) (n : ℕ) :
    trueCovariance E n =
      finiteErrorCovariance (regionalRandomValues μ E.maps E.error n) P :=
  rfl

/-- The Fubini/conditional-mean compatibility stated in prose below
`eq:conditional-mean`: each component of `m_n` is the regional average of
`m(s)`.  It is a named translation obligation, not an extra assumption inside
any manuscript proposition. -/
@[expose]
def regionalMeanCompatibility (E : FixedConditionalExperiment μ P) : Prop :=
  ∀ n i,
    regionalMeanFromSpatialConditionalMean E.maps P E.error n i =
      regionalConditionalMean E.maps P E.error n i

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional interface for the exact prose assertion below
`eq:conditional-mean`.  This is an `rfl` expansion, not an added hypothesis
or a mathematical strengthening. -/
@[simp]
theorem regionalMeanCompatibility_iff (E : FixedConditionalExperiment μ P) :
    regionalMeanCompatibility E ↔
      ∀ n i,
        regionalMeanFromSpatialConditionalMean E.maps P E.error n i =
          regionalConditionalMean E.maps P E.error n i :=
  Iff.rfl

/-- The `m_n - W_n c` vector in the two mean restrictions. -/
@[expose]
noncomputable def meanOffset
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) (n : ℕ) :
    Fin (E.maps.N n) → ℝ :=
  regionalConditionalMean E.maps P E.error n -
    regionalControls μ E.maps E.controls n *ᵥ c

/-- The inverse-working-covariance energy appearing in `eq:relative-mean`
and `eq:mean-energy`. -/
@[expose]
noncomputable def meanEnergy
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) (n : ℕ) : ℝ :=
  quadraticForm (E.kernel n)⁻¹ (meanOffset E c n)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the inverse-working-covariance mean
energy.  It exposes the existing formula for exact finite bounds only. -/
@[simp]
theorem meanEnergy_eq (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ)
    (n : ℕ) :
    meanEnergy E c n = quadraticForm (E.kernel n)⁻¹ (meanOffset E c n) :=
  rfl

/-- The residual-scale numerator's full GLS residual, from `eq:residuals`. -/
@[expose]
noncomputable def fittedResidual
    (E : FixedConditionalExperiment μ P) (n : ℕ) (ω : Ω) :
    Fin (E.maps.N n) → ℝ :=
  (fun i => regionalRandomValues μ E.maps E.outcome n i ω) -
    (E.betaHat n ω) • regionalValues μ E.maps E.treatment n -
    regionalControls μ E.maps E.controls n *ᵥ E.gammaHat n ω

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the literal residual in `eq:residuals`.
This is an API-only `rfl` bridge: it leaves the residual formula, all source
assumptions, and every manuscript proposition unchanged. -/
@[simp]
theorem fittedResidual_eq (E : FixedConditionalExperiment μ P) (n : ℕ) (ω : Ω) :
    fittedResidual E n ω =
      (fun i => regionalRandomValues μ E.maps E.outcome n i ω) -
        (E.betaHat n ω) • regionalValues μ E.maps E.treatment n -
        regionalControls μ E.maps E.controls n *ᵥ E.gammaHat n ω :=
  rfl

/-- The residual scale in `eq:scale`, including exactly the manuscript's
fixed positive fallback when its displayed divisor is not yet positive. -/
@[expose]
noncomputable def residualScale
    (E : FixedConditionalExperiment μ P) (n : ℕ) (ω : Ω) : ℝ :=
  if E.q + 1 < E.maps.N n then
    quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) /
      ((E.maps.N n - E.q - 1 : ℕ) : ℝ)
  else E.early_scale_fallback

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public exact expansion of the displayed branch of `eq:scale`.  This is an
API-only visibility bridge: it leaves the fallback, divisor, formula, and all
manuscript statements unchanged. -/
@[simp]
theorem residualScale_eq_quotient_of_divisor
    (E : FixedConditionalExperiment μ P) (n : ℕ) (ω : Ω)
    (hdivisor : E.q + 1 < E.maps.N n) :
    residualScale E n ω =
      quadraticForm (E.kernel n)⁻¹ (fittedResidual E n ω) /
        ((E.maps.N n - E.q - 1 : ℕ) : ℝ) := by
  rw [residualScale, if_pos hdivisor]

/-- The reported variance in `eq:variance`. -/
@[expose]
noncomputable def reportedVariance
    (E : FixedConditionalExperiment μ P) (n : ℕ) (ω : Ω) : ℝ :=
  residualScale E n ω / E.information n

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the existing reported variance.  This is
an API-only `rfl` bridge: it exposes neither a new variance comparison nor an
additional inference claim. -/
@[simp]
theorem reportedVariance_eq
    (E : FixedConditionalExperiment μ P) (n : ℕ) (ω : Ω) :
    reportedVariance E n ω = residualScale E n ω / E.information n :=
  rfl

/-- The FWL expression in `eq:FWL`.  Its equality to the selected minimizer
is deliberately recorded below as a proof obligation rather than assumed in
the manuscript proposition definitions. -/
@[expose]
noncomputable def fwlSlope
    (E : FixedConditionalExperiment μ P) (n : ℕ) (ω : Ω) : ℝ :=
  fwlEstimateControls (E.kernel n)⁻¹ (regionalControls μ E.maps E.controls n)
    (regionalValues μ E.maps E.treatment n)
    (fun i => regionalRandomValues μ E.maps E.outcome n i ω)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the existing FWL expression.  It exposes
no new estimator identity or manuscript assumption. -/
@[simp]
theorem fwlSlope_eq (E : FixedConditionalExperiment μ P) (n : ℕ) (ω : Ω) :
    fwlSlope E n ω =
      fwlEstimateControls (E.kernel n)⁻¹ (regionalControls μ E.maps E.controls n)
        (regionalValues μ E.maps E.treatment n)
        (fun i => regionalRandomValues μ E.maps E.outcome n i ω) :=
  rfl

/-- A named translation obligation connecting `eq:estimator` and `eq:FWL`.
It is not included as a source assumption and has no proof in this file. -/
@[expose]
def estimatorHasFWLForm (E : FixedConditionalExperiment μ P) : Prop :=
  ∀ᶠ n in atTop, ∀ ω, E.betaHat n ω = fwlSlope E n ω

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the named estimator/FWL translation
obligation.  This is an API-only `rfl` interface, not an added hypothesis. -/
theorem estimatorHasFWLForm_iff (E : FixedConditionalExperiment μ P) :
    estimatorHasFWLForm E ↔ ∀ᶠ n in atTop, ∀ ω, E.betaHat n ω = fwlSlope E n ω :=
  Iff.rfl

/-- The conditional MSE in `eq:mse-bound`, evaluated under the fixed law `P`. -/
@[expose]
noncomputable def conditionalSlopeMSE
    (E : FixedConditionalExperiment μ P) (n : ℕ) : ℝ :=
  ∫ ω, (E.betaHat n ω - E.beta) ^ 2 ∂P

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the existing conditional slope MSE.  It
is an API-only `rfl` bridge for the literal consistency conclusion. -/
@[simp]
theorem conditionalSlopeMSE_eq (E : FixedConditionalExperiment μ P) (n : ℕ) :
    conditionalSlopeMSE E n = ∫ ω, (E.betaHat n ω - E.beta) ^ 2 ∂P :=
  rfl

/-! ## Exact source assumptions after conditioning -/

/-- `ass:upper`, including both `0 ⪯ Σ_n` and `Σ_n ⪯ C K_n` after one
common starting index. -/
structure UpperCovarianceAssumption (E : FixedConditionalExperiment μ P) where
  C : ℝ
  C_pos : 0 < C
  start : ℕ
  bound : ∀ n ≥ start,
    (trueCovariance E n).PosSemidef ∧
      (C • E.kernel n - trueCovariance E n).PosSemidef

/-- `ass:weak-mean`: one fixed control coefficient vector, not one vector per
resolution. -/
structure WeakMeanAssumption (E : FixedConditionalExperiment μ P) where
  c : Fin E.q → ℝ
  relative_energy_tendsto :
    Tendsto (fun n => meanEnergy E c n / E.information n) atTop (nhds 0)

/-- `ass:covariance` after fixing the conditional law. -/
structure CovarianceAssumption (E : FixedConditionalExperiment μ P) where
  centered_field_gaussian :
    IsGaussianProcess (centeredIntegralProcess μ P E.error) P
  positive_test_variance : ∀ h : L2TestFunction μ, NonzeroInL2 μ h →
    0 < varianceUnder P (centeredTestIntegral μ P E.error h)
  sigmaSquared : ℝ
  sigmaSquared_pos : 0 < sigmaSquared
  delta : ℕ → ℝ
  delta_tendsto_zero : Tendsto delta atTop (nhds 0)
  start : ℕ
  sandwich : ∀ n ≥ start,
    0 ≤ delta n ∧ delta n < 1 ∧
      (trueCovariance E n -
        (sigmaSquared / (1 + delta n)) • E.kernel n).PosSemidef ∧
      ((sigmaSquared / (1 - delta n)) • E.kernel n -
        trueCovariance E n).PosSemidef

/-- `ass:mean`: one fixed control coefficient vector whose inverse-working
covariance energy is bounded uniformly over all resolutions.  `BddAbove` is
the real-valued rendering of the manuscript's finite supremum. -/
structure FixedMeanAssumption (E : FixedConditionalExperiment μ P) where
  c : Fin E.q → ℝ
  bounded_energy : BddAbove (Set.range (fun n => meanEnergy E c n))

/-! ## Exact proposition conclusions (definitions only; not proved here) -/

/-- The conclusion and displayed MSE bound of `prop:consistency`. -/
@[expose]
def consistencyConclusion (E : FixedConditionalExperiment μ P)
    (upper : UpperCovarianceAssumption E) (weakMean : WeakMeanAssumption E) : Prop :=
  TendstoInMeasure P E.betaHat atTop (fun _ => E.beta) ∧
    (∀ᶠ n in atTop,
      conditionalSlopeMSE E n ≤
        (upper.C + meanEnergy E weakMean.c n) / E.information n) ∧
    Tendsto
      (fun n => (upper.C + meanEnergy E weakMean.c n) / E.information n)
      atTop (nhds 0)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the exact consistency conclusion.  This
is an API-only `rfl` interface, not a new asymptotic theorem. -/
theorem consistencyConclusion_iff (E : FixedConditionalExperiment μ P)
    (upper : UpperCovarianceAssumption E) (weakMean : WeakMeanAssumption E) :
    consistencyConclusion E upper weakMean ↔
      TendstoInMeasure P E.betaHat atTop (fun _ => E.beta) ∧
        (∀ᶠ n in atTop,
          conditionalSlopeMSE E n ≤
            (upper.C + meanEnergy E weakMean.c n) / E.information n) ∧
        Tendsto
          (fun n => (upper.C + meanEnergy E weakMean.c n) / E.information n)
          atTop (nhds 0) :=
  Iff.rfl

/-- The full proposition-shaped statement of `prop:consistency` after the
fixed conditional experiment has supplied `reg:maps` and `reg:information`. -/
@[expose]
def manuscriptConsistency (E : FixedConditionalExperiment μ P) : Prop :=
  ∀ upper : UpperCovarianceAssumption E, ∀ weakMean : WeakMeanAssumption E,
    consistencyConclusion E upper weakMean

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the source-facing consistency
proposition.  It only exposes the existing universal quantification. -/
theorem manuscriptConsistency_iff (E : FixedConditionalExperiment μ P) :
    manuscriptConsistency E ↔ ∀ upper : UpperCovarianceAssumption E,
      ∀ weakMean : WeakMeanAssumption E, consistencyConclusion E upper weakMean :=
  Iff.rfl

/-- The conclusion of `prop:normality`, with `σ = sqrt(σ²)`. -/
@[expose]
def normalityConclusion (E : FixedConditionalExperiment μ P)
    (covariance : CovarianceAssumption E) (_mean : FixedMeanAssumption E) : Prop :=
  TendstoInDistribution
    (fun n ω =>
      (Real.sqrt (E.information n) / Real.sqrt covariance.sigmaSquared) *
        (E.betaHat n ω - E.beta))
    atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1)

omit [IsProbabilityMeasure μ] in
/-- Public definitional expansion of the exact source-facing normality
conclusion.  This is an API-only `rfl` interface; it leaves the displayed
normalization, law, and every manuscript assumption unchanged. -/
theorem normalityConclusion_iff (E : FixedConditionalExperiment μ P)
    (covariance : CovarianceAssumption E) (mean : FixedMeanAssumption E) :
    normalityConclusion E covariance mean ↔
      TendstoInDistribution
        (fun n ω =>
          (Real.sqrt (E.information n) / Real.sqrt covariance.sigmaSquared) *
            (E.betaHat n ω - E.beta))
        atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1) :=
  Iff.rfl

/-- The full proposition-shaped statement of `prop:normality`. -/
@[expose]
def manuscriptNormality (E : FixedConditionalExperiment μ P) : Prop :=
  ∀ covariance : CovarianceAssumption E, ∀ mean : FixedMeanAssumption E,
    normalityConclusion E covariance mean

omit [IsProbabilityMeasure μ] in
/-- Public definitional expansion of the unchanged proposition-shaped
normality target.  It exposes only the existing universal quantification. -/
theorem manuscriptNormality_iff (E : FixedConditionalExperiment μ P) :
    manuscriptNormality E ↔ ∀ covariance : CovarianceAssumption E,
      ∀ mean : FixedMeanAssumption E, normalityConclusion E covariance mean :=
  Iff.rfl

/-- A standard-normal critical value, written so that the source's notation
`z_{1-α/2}` has an explicit mathematical calibration. -/
structure StandardNormalQuantile (α : ℝ) where
  alpha_pos : 0 < α
  alpha_lt_one : α < 1
  value : ℝ
  cdf_value : gaussianReal 0 1 (Set.Iic value) = ENNReal.ofReal (1 - α / 2)

/-- The confidence-interval coverage statement in `prop:variance`, evaluated
 under the fixed conditional law. -/
@[expose]
def confidenceCoverage (E : FixedConditionalExperiment μ P) (α : ℝ)
    (z : StandardNormalQuantile α) : Prop :=
  Tendsto
    (fun n => P {ω |
      E.beta ∈ Set.Icc
        (E.betaHat n ω - z.value * Real.sqrt (reportedVariance E n ω))
        (E.betaHat n ω + z.value * Real.sqrt (reportedVariance E n ω))})
    atTop (nhds (ENNReal.ofReal (1 - α)))

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Public definitional expansion of the unchanged literal coverage target.
This API-only interface exposes neither a new calibration condition nor a
different interval. -/
theorem confidenceCoverage_iff (E : FixedConditionalExperiment μ P) (α : ℝ)
    (z : StandardNormalQuantile α) :
    confidenceCoverage E α z ↔
      Tendsto
        (fun n => P {ω |
          E.beta ∈ Set.Icc
            (E.betaHat n ω - z.value * Real.sqrt (reportedVariance E n ω))
            (E.betaHat n ω + z.value * Real.sqrt (reportedVariance E n ω))})
        atTop (nhds (ENNReal.ofReal (1 - α))) :=
  Iff.rfl

/-- All conclusions asserted by `prop:variance`. -/
@[expose]
def varianceConclusion (E : FixedConditionalExperiment μ P)
    (covariance : CovarianceAssumption E) (_mean : FixedMeanAssumption E) : Prop :=
  TendstoInMeasure P (residualScale E) atTop
      (fun _ => covariance.sigmaSquared) ∧
    TendstoInMeasure P
      (fun n ω => reportedVariance E n ω / varianceUnder P (E.betaHat n))
      atTop (fun _ => (1 : ℝ)) ∧
    TendstoInMeasure P
      (fun n ω =>
        reportedVariance E n ω /
          (covariance.sigmaSquared / E.information n))
      atTop (fun _ => (1 : ℝ)) ∧
    TendstoInDistribution
      (fun n ω =>
        (E.betaHat n ω - E.beta) / Real.sqrt (reportedVariance E n ω))
      atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1) ∧
    ∀ α : ℝ, ∀ z : StandardNormalQuantile α, confidenceCoverage E α z

omit [IsProbabilityMeasure μ] in
/-- Public definitional expansion of the exact five-conjunct variance
conclusion.  This is deliberately an `rfl` interface: its statistic,
denominators, law, and coverage codomain are unchanged. -/
theorem varianceConclusion_iff (E : FixedConditionalExperiment μ P)
    (covariance : CovarianceAssumption E) (mean : FixedMeanAssumption E) :
    varianceConclusion E covariance mean ↔
      TendstoInMeasure P (residualScale E) atTop
          (fun _ => covariance.sigmaSquared) ∧
        TendstoInMeasure P
          (fun n ω => reportedVariance E n ω / varianceUnder P (E.betaHat n))
          atTop (fun _ => (1 : ℝ)) ∧
        TendstoInMeasure P
          (fun n ω =>
            reportedVariance E n ω /
              (covariance.sigmaSquared / E.information n))
          atTop (fun _ => (1 : ℝ)) ∧
        TendstoInDistribution
          (fun n ω =>
            (E.betaHat n ω - E.beta) / Real.sqrt (reportedVariance E n ω))
          atTop (fun z : ℝ => z) (fun _ => P) (gaussianReal 0 1) ∧
        ∀ α : ℝ, ∀ z : StandardNormalQuantile α, confidenceCoverage E α z :=
  Iff.rfl

/-- The full proposition-shaped statement of `prop:variance`. -/
@[expose]
def manuscriptVariance (E : FixedConditionalExperiment μ P) : Prop :=
  ∀ covariance : CovarianceAssumption E, ∀ mean : FixedMeanAssumption E,
    varianceConclusion E covariance mean

omit [IsProbabilityMeasure μ] in
/-- Public definitional expansion of the unchanged proposition-shaped
variance target.  It exposes only its existing universal quantification. -/
theorem manuscriptVariance_iff (E : FixedConditionalExperiment μ P) :
    manuscriptVariance E ↔ ∀ covariance : CovarianceAssumption E,
      ∀ mean : FixedMeanAssumption E, varianceConclusion E covariance mean :=
  Iff.rfl

end InfillGLSLean.ManuscriptSpecification
