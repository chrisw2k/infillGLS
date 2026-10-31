module

public import ManuscriptSpecification
public import «L-025-api-fubini-integration».RegionalMeanCompatibility
public import «L-026-nonnested-regional-averaging».NonnestedRegionalAveraging
public import InfillGLSLean.GLSBiasBound
public import InfillGLSLean.FiniteConditionalError
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
public import Mathlib.Tactic

/-!
# Covariance-Hilbert/Riesz support for Appendix `lem:mean`

This module formalizes source-faithful Hilbert-space ingredients for the
Riesz-representer portion of the Appendix mean lemma. Its results are used by
the common-refinement and working-weight integrations; it does not
alter any source-facing proposition.
-/

public section

namespace InfillGLSLean.MeanHilbertRiesz

open Filter Topology
open scoped RealInnerProductSpace

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The Frechet--Riesz representative of a bounded real linear functional.
This is the exact generic construction used in the paper's covariance-space
paragraph: the functional itself, not an additional covariance assumption,
determines the representing element. -/
noncomputable def rieszRepresenter (L : StrongDual ℝ H) : H :=
  (InnerProductSpace.toDual ℝ H).symm L

/-- Frechet--Riesz in the orientation used by the paper: every bounded
functional is inner product against its fixed representative. -/
theorem inner_rieszRepresenter (L : StrongDual ℝ H) (h : H) :
    inner ℝ (rieszRepresenter (H := H) L) h = L h := by
  simp [rieszRepresenter]

/-- The representative is unique. This is the exact uniqueness used when a
fixed covariance functional identifies one fixed `V` in the paper's Hilbert
space, rather than a resolution-dependent choice. -/
theorem rieszRepresenter_unique (L : StrongDual ℝ H) (V : H)
    (hV : ∀ h : H, inner ℝ V h = L h) : V = rieszRepresenter (H := H) L := by
  apply ext_inner_right ℝ
  intro h
  rw [hV h, inner_rieszRepresenter]

/-- The bound obtained from the paper's inverse-covariance energy turns an
algebraic linear functional into a bounded functional. Fréchet--Riesz then
provides a fixed representer without postulating one. -/
theorem exists_rieszRepresenter_of_linear_bound
    (L : H →ₗ[ℝ] ℝ) (C : ℝ)
    (hL : ∀ h : H, ‖L h‖ ≤ C * ‖h‖) :
    ∃ V : H, ∀ h : H, L h = inner ℝ V h := by
  let Lc : StrongDual ℝ H := LinearMap.mkContinuous L C hL
  refine ⟨rieszRepresenter (H := H) Lc, ?_⟩
  intro h
  simpa [Lc] using (inner_rieszRepresenter (H := H) Lc h).symm

/-- The paper's dense-range Riesz step, packaged using Mathlib's completion
extension: a functional on spatial tests that is bounded by the norm of its
centered-average image has one fixed representer in the closure of those
averages.  This is a generic Hilbert-space consequence, not an added
covariance assumption. -/
theorem exists_rieszRepresenter_of_linear_bound_along_dense
    {X : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X →ₗ[ℝ] H) (f : X →ₗ[ℝ] ℝ) (hdense : DenseRange A)
    (hbound : ∃ C : ℝ, ∀ x : X, ‖f x‖ ≤ C * ‖A x‖) :
    ∃ V : H, ∀ x : X, f x = inner ℝ V (A x) := by
  let L : H →L[ℝ] ℝ := f.extendOfNorm A
  refine ⟨rieszRepresenter (H := H) L, ?_⟩
  intro x
  rw [← LinearMap.extendOfNorm_eq hdense hbound x]
  exact (inner_rieszRepresenter (H := H) L (A x)).symm

/-! ### The fixed spatial mean residual

The paper applies its covariance-space argument to the literal fixed spatial
function `f = m - W c`.  The source specification records its regional
version as `meanOffset`.  The following exact bridge derives, rather than
assumes, the correspondence between those two presentations.  It is kept
here because it is the input required by the Riesz construction; it changes
neither `meanOffset` nor the manuscript assumptions. -/

section SourceMeanOffset

open InfillGLSLean.ManuscriptSpecification
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

variable {α ι : Type*} [MeasurableSpace α] {μ₀ : Measure α} {R : Set α}
  [Fintype ι]

/-- Linearity of a regional mean for the finite control combination in the
paper's fixed function `m - Wc`. -/
theorem setAverage_sub_dotProduct
    (m : α → ℝ) (w : ι → α → ℝ) (c : ι → ℝ)
    (hm : IntegrableOn m R μ₀)
    (hw : ∀ j, IntegrableOn (w j) R μ₀) :
    (⨍ s in R, (m s - dotProduct (fun j => w j s) c) ∂μ₀) =
      (⨍ s in R, m s ∂μ₀) - ∑ j, (⨍ s in R, w j s ∂μ₀) * c j := by
  let g : α → ℝ := fun s => ∑ j, w j s * c j
  have hg : IntegrableOn g R μ₀ := by
    change Integrable (fun s => ∑ j, w j s * c j) (μ₀.restrict R)
    exact integrable_finsetSum Finset.univ fun j _ => (hw j).mul_const (c j)
  change (⨍ s in R, (m - g) s ∂μ₀) =
    (⨍ s in R, m s ∂μ₀) - ∑ j, (⨍ s in R, w j s ∂μ₀) * c j
  rw [setAverage_sub hm hg]
  have hsum : (⨍ s in R, g s ∂μ₀) =
      ∑ j, (⨍ s in R, w j s * c j ∂μ₀) := by
    simp only [g]
    simpa only [Finset.sum_apply] using
      (setAverage_finsetSum (s := R) (μ := μ₀) (t := Finset.univ)
        (f := fun j => fun s => w j s * c j)
        (fun j _ => (hw j).mul_const (c j)))
  rw [hsum]
  simp only [average_mul_const]

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
private theorem control_memLp_two
    (E : FixedConditionalExperiment μ P) (j : Fin E.q) : MemLp (E.controls j) 2 μ := by
  have hsq_measurable : Measurable (fun s => E.controls j s ^ 2) :=
    (E.controls_measurable j).pow measurable_const
  have hpoint : ∀ s : Point D,
      ENNReal.ofReal (E.controls j s ^ 2) ≤
        ENNReal.ofReal (E.treatment s ^ 2 + ∑ k : Fin E.q, E.controls k s ^ 2) := by
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
private theorem error_square_product_integrable
    (E : FixedConditionalExperiment μ P) :
    Integrable (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) (P.prod μ) := by
  have hsq_measurable : Measurable
      (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) :=
    E.error_jointly_measurable.pow measurable_const
  have hsq_ennreal_measurable : Measurable
      (fun z : Ω × Point D => ENNReal.ofReal (E.error z.1 z.2 ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp hsq_measurable
  have hsq_lintegral :
      (∫⁻ z : Ω × Point D, ENNReal.ofReal (E.error z.1 z.2 ^ 2) ∂(P.prod μ)) < ∞ := by
    rw [lintegral_prod _ hsq_ennreal_measurable.aemeasurable]
    exact E.conditional_error_second_moment
  exact
    (lintegral_ofReal_ne_top_iff_integrable hsq_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => sq_nonneg (E.error z.1 z.2))).mp
      hsq_lintegral.ne

private theorem error_product_integrable
    (E : FixedConditionalExperiment μ P) :
    Integrable (fun z : Ω × Point D => E.error z.1 z.2) (P.prod μ) := by
  have hmemLp : MemLp (fun z : Ω × Point D => E.error z.1 z.2) 2 (P.prod μ) :=
    (memLp_two_iff_integrable_sq E.error_jointly_measurable.aestronglyMeasurable).mpr
      (error_square_product_integrable E)
  exact hmemLp.integrable (by norm_num)

private theorem conditional_error_mean_integrable
    (E : FixedConditionalExperiment μ P) :
    Integrable (conditionalErrorMean P E.error) μ := by
  change Integrable (fun s => ∫ w, E.error w s ∂P) μ
  simpa using (error_product_integrable E).integral_prod_right

/-- The conditional error mean is square-integrable under precisely the
source's joint second-moment condition.  This establishes the L2 premise for
the paper's fixed spatial mean residual rather than assuming it separately. -/
private theorem conditional_error_mean_memLp_two
    (E : FixedConditionalExperiment μ P) :
    MemLp (conditionalErrorMean P E.error) 2 μ := by
  have hsq_measurable : Measurable
      (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) :=
    E.error_jointly_measurable.pow measurable_const
  have hvertical_error : ∀ᵐ s ∂μ, Integrable (fun ω => E.error ω s) P :=
    (integrable_prod_iff' E.error_jointly_measurable.aestronglyMeasurable).mp
      (error_product_integrable E) |>.1
  have hvertical_square : ∀ᵐ s ∂μ, Integrable (fun ω => E.error ω s ^ 2) P :=
    (integrable_prod_iff' hsq_measurable.aestronglyMeasurable).mp
      (error_square_product_integrable E) |>.1
  have haverage_square : Integrable
      (fun s => ∫ ω, E.error ω s ^ 2 ∂P) μ :=
    (error_square_product_integrable E).integral_prod_right
  have hm_aestronglyMeasurable : AEStronglyMeasurable
      (conditionalErrorMean P E.error) μ := by
    change AEStronglyMeasurable (fun s => ∫ ω, E.error ω s ∂P) μ
    simpa using (error_product_integrable E).integral_prod_right.1
  apply (memLp_two_iff_integrable_sq hm_aestronglyMeasurable).mpr
  apply Integrable.mono' haverage_square
  · exact hm_aestronglyMeasurable.pow 2
  filter_upwards [hvertical_error, hvertical_square] with s herror hsquare
  have hjensen := (Even.convexOn_pow (𝕜 := ℝ) (by norm_num : Even 2)).map_integral_le
    (continuous_pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) herror hsquare
  change ‖(∫ ω, E.error ω s ∂P) ^ 2‖ ≤ ∫ ω, E.error ω s ^ 2 ∂P
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa [Function.comp_def] using hjensen

/-- The centered error field `u = ε - m` used in the covariance-space
paragraph of Appendix `lem:mean`.  This merely gives a local name to the
paper's displayed expression. -/
noncomputable def centeredError
    (E : FixedConditionalExperiment μ P) : Ω → Point D → ℝ :=
  fun ω s => E.error ω s - conditionalErrorMean P E.error s

omit [IsProbabilityMeasure P] in
private theorem error_memLp_two_product
    (E : FixedConditionalExperiment μ P) :
    MemLp (fun z : Ω × Point D => E.error z.1 z.2) 2 (P.prod μ) := by
  exact (memLp_two_iff_integrable_sq E.error_jointly_measurable.aestronglyMeasurable).mpr
    (error_square_product_integrable E)

private theorem conditional_error_mean_comp_snd_memLp_two
    (E : FixedConditionalExperiment μ P) :
    MemLp (fun z : Ω × Point D => conditionalErrorMean P E.error z.2) 2 (P.prod μ) := by
  exact (conditional_error_mean_memLp_two E).comp_snd P

/-- The existing conditional second-moment field implies that the paper's
centered field belongs to L2 on the outcome-by-space product measure. -/
theorem centeredError_memLp_two_product
    (E : FixedConditionalExperiment μ P) :
    MemLp (fun z : Ω × Point D => centeredError E z.1 z.2) 2 (P.prod μ) := by
  change MemLp
    ((fun z : Ω × Point D => E.error z.1 z.2) -
      fun z : Ω × Point D => conditionalErrorMean P E.error z.2) 2 (P.prod μ)
  exact (error_memLp_two_product E).sub (conditional_error_mean_comp_snd_memLp_two E)

/-- The product in the paper's covariance pairing is integrable for every
outcome-L2 representative.  This is the Fubini prerequisite for the map
`V ↦ E[u(·) V]`; it follows from the source's product-L2 field and does not
assert the later spatial-L2 bound. -/
theorem centeredError_mul_outcomeL2_integrable
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    Integrable
      (fun z : Ω × Point D => centeredError E z.1 z.2 * V z.1) (P.prod μ) := by
  have hV : MemLp (fun z : Ω × Point D => V z.1) 2 (P.prod μ) :=
    Lp.memLp V |>.comp_fst μ
  change Integrable
    ((fun z : Ω × Point D => centeredError E z.1 z.2) * fun z => V z.1)
    (P.prod μ)
  exact (centeredError_memLp_two_product E).integrable_mul hV

/-- The raw source-specific covariance pairing from an outcome-L2 random
variable to a spatial L1 function.  The paper next proves this function is in
spatial L2 by a product-space Cauchy--Schwarz bound; that stronger conclusion
is intentionally not built into this definition. -/
noncomputable def centeredErrorPairing
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) : Point D → ℝ :=
  fun s => ∫ ω, centeredError E ω s * V ω ∂P

/-- The covariance pairing is spatially integrable by Fubini.  This is a
literal consequence of the joint second moment and the outcome-L2 condition
on `V`. -/
theorem centeredErrorPairing_integrable
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    Integrable (centeredErrorPairing E V) μ := by
  change Integrable (fun s => ∫ ω, centeredError E ω s * V ω ∂P) μ
  exact (centeredError_mul_outcomeL2_integrable E V).integral_prod_right

private theorem centeredErrorPairing_abs_bound
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    ∀ᵐ s ∂μ,
      |centeredErrorPairing E V s| ≤
        (∫ ω, ‖centeredError E ω s‖ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
          (∫ ω, ‖V ω‖ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
  have hU := centeredError_memLp_two_product E
  have hV : MemLp (fun ω => V ω) 2 P := Lp.memLp V
  have hU_sq :
      Integrable (fun z : Ω × Point D => centeredError E z.1 z.2 ^ 2) (P.prod μ) :=
    (memLp_two_iff_integrable_sq hU.aestronglyMeasurable).mp hU
  have hmeas : ∀ᵐ s ∂μ, AEStronglyMeasurable (fun ω => centeredError E ω s) P :=
    hU.aestronglyMeasurable.prodMk_right
  have hsq : ∀ᵐ s ∂μ, Integrable (fun ω => centeredError E ω s ^ 2) P :=
    hU_sq.prod_left_ae
  filter_upwards [hmeas, hsq] with s hs_meas hs_sq
  have hUs : MemLp (fun ω => centeredError E ω s) 2 P :=
    (memLp_two_iff_integrable_sq hs_meas).mpr hs_sq
  have hUs' : MemLp (fun ω => centeredError E ω s) (ENNReal.ofReal (2 : ℝ)) P := by
    norm_num
    exact hUs
  have hV' : MemLp (fun ω => V ω) (ENNReal.ofReal (2 : ℝ)) P := by
    norm_num
    exact hV
  have hCS := integral_mul_norm_le_Lp_mul_Lq
    (μ := P) (f := fun ω => centeredError E ω s) (g := fun ω => V ω)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2) hUs' hV'
  change |∫ ω, centeredError E ω s * V ω ∂P| ≤ _
  calc
    |∫ ω, centeredError E ω s * V ω ∂P| ≤
        ∫ ω, |centeredError E ω s * V ω| ∂P := abs_integral_le_integral_abs
    _ = ∫ ω, ‖centeredError E ω s‖ * ‖V ω‖ ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      simp [abs_mul, Real.norm_eq_abs]
    _ ≤ _ := hCS

private theorem centeredErrorPairing_sq_bound
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    ∀ᵐ s ∂μ,
      (centeredErrorPairing E V s) ^ 2 ≤
        (∫ ω, centeredError E ω s ^ 2 ∂P) * (∫ ω, V ω ^ 2 ∂P) := by
  filter_upwards [centeredErrorPairing_abs_bound E V] with s hs
  have ha : 0 ≤ ∫ ω, ‖centeredError E ω s‖ ^ (2 : ℝ) ∂P :=
    integral_nonneg fun ω => by positivity
  have hb : 0 ≤ ∫ ω, ‖V ω‖ ^ (2 : ℝ) ∂P :=
    integral_nonneg fun ω => by positivity
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hs
  have hright : 0 ≤
      Real.sqrt (∫ ω, ‖centeredError E ω s‖ ^ (2 : ℝ) ∂P) *
        Real.sqrt (∫ ω, ‖V ω‖ ^ (2 : ℝ) ∂P) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : |centeredErrorPairing E V s| ^ 2 ≤
      (Real.sqrt (∫ ω, ‖centeredError E ω s‖ ^ (2 : ℝ) ∂P) *
        Real.sqrt (∫ ω, ‖V ω‖ ^ (2 : ℝ) ∂P)) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hright).mpr hs
  have hbound : (centeredErrorPairing E V s) ^ 2 ≤
      (∫ ω, ‖centeredError E ω s‖ ^ (2 : ℝ) ∂P) *
        (∫ ω, ‖V ω‖ ^ (2 : ℝ) ∂P) := by
    calc
      (centeredErrorPairing E V s) ^ 2 = |centeredErrorPairing E V s| ^ 2 := by
        rw [sq_abs]
      _ ≤ _ := hsq
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hbound

/-- Product-space Cauchy--Schwarz upgrades the raw Fubini pairing to the
spatial L2 map asserted in the covariance-function-space paragraph of
Appendix `lem:mean`.  It uses only the source's joint second moment and an
outcome-L2 representative; no covariance regularity is added. -/
theorem centeredErrorPairing_memLp_two
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    MemLp (centeredErrorPairing E V) 2 μ := by
  have hpair : Integrable (centeredErrorPairing E V) μ :=
    centeredErrorPairing_integrable E V
  have hU := centeredError_memLp_two_product E
  have hU_sq :
      Integrable (fun z : Ω × Point D => centeredError E z.1 z.2 ^ 2) (P.prod μ) :=
    (memLp_two_iff_integrable_sq hU.aestronglyMeasurable).mp hU
  have hA : Integrable (fun s => ∫ ω, centeredError E ω s ^ 2 ∂P) μ :=
    hU_sq.integral_prod_right
  let b : ℝ := ∫ ω, V ω ^ 2 ∂P
  have hb : 0 ≤ b := by
    dsimp [b]
    exact integral_nonneg fun ω => sq_nonneg (V ω)
  apply (memLp_two_iff_integrable_sq hpair.aestronglyMeasurable).mpr
  refine Integrable.mono (hA.const_mul b) (hpair.aestronglyMeasurable.pow 2) ?_
  filter_upwards [centeredErrorPairing_sq_bound E V] with s hs
  have ha : 0 ≤ ∫ ω, centeredError E ω s ^ 2 ∂P :=
    integral_nonneg fun ω => sq_nonneg (centeredError E ω s)
  have hba : 0 ≤ b * (∫ ω, centeredError E ω s ^ 2 ∂P) := mul_nonneg hb ha
  change |(centeredErrorPairing E V s) ^ 2| ≤
    |b * (∫ ω, centeredError E ω s ^ 2 ∂P)|
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hba]
  simpa [b, mul_comm] using hs

/-- The checked product-space energy bound behind the covariance pairing.
This is the source-faithful Cauchy--Schwarz estimate from the paper's claim
that `V ↦ E[u(·)V]` maps outcome L2 into spatial L2. -/
theorem centeredErrorPairing_integral_sq_le
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    (∫ s, (centeredErrorPairing E V s) ^ 2 ∂μ) ≤
      (∫ z : Ω × Point D, centeredError E z.1 z.2 ^ 2 ∂(P.prod μ)) *
        (∫ ω, V ω ^ 2 ∂P) := by
  have hpair := centeredErrorPairing_memLp_two E V
  have hpair_sq : Integrable (fun s => centeredErrorPairing E V s ^ 2) μ :=
    (memLp_two_iff_integrable_sq hpair.aestronglyMeasurable).mp hpair
  have hU := centeredError_memLp_two_product E
  have hU_sq :
      Integrable (fun z : Ω × Point D => centeredError E z.1 z.2 ^ 2) (P.prod μ) :=
    (memLp_two_iff_integrable_sq hU.aestronglyMeasurable).mp hU
  have hA : Integrable (fun s => ∫ ω, centeredError E ω s ^ 2 ∂P) μ :=
    hU_sq.integral_prod_right
  let b : ℝ := ∫ ω, V ω ^ 2 ∂P
  have hdom :
      (∫ s, (centeredErrorPairing E V s) ^ 2 ∂μ) ≤
        ∫ s, b * (∫ ω, centeredError E ω s ^ 2 ∂P) ∂μ := by
    apply integral_mono_ae hpair_sq (hA.const_mul b)
    filter_upwards [centeredErrorPairing_sq_bound E V] with s hs
    simpa [b, mul_comm] using hs
  have hFubini :
      (∫ s, ∫ ω, centeredError E ω s ^ 2 ∂P ∂μ) =
        ∫ z : Ω × Point D, centeredError E z.1 z.2 ^ 2 ∂(P.prod μ) := by
    calc
      (∫ s, ∫ ω, centeredError E ω s ^ 2 ∂P ∂μ) =
          ∫ ω, ∫ s, centeredError E ω s ^ 2 ∂μ ∂P :=
        (integral_integral_swap hU_sq).symm
      _ = ∫ z : Ω × Point D, centeredError E z.1 z.2 ^ 2 ∂(P.prod μ) :=
        integral_integral hU_sq
  calc
    (∫ s, (centeredErrorPairing E V s) ^ 2 ∂μ) ≤
        ∫ s, b * (∫ ω, centeredError E ω s ^ 2 ∂P) ∂μ := hdom
    _ = b * (∫ s, ∫ ω, centeredError E ω s ^ 2 ∂P ∂μ) := by
      rw [integral_const_mul]
    _ = b * (∫ z : Ω × Point D, centeredError E z.1 z.2 ^ 2 ∂(P.prod μ)) := by
      rw [hFubini]
    _ = _ := by
      dsimp [b]
      rw [mul_comm]

/-- The spatial-L2 packaging of the paper's map
`V ↦ E[u(·) V]`.  The pointwise formula remains available through
`centeredErrorPairing`. -/
noncomputable def centeredErrorPairingL2
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) : Lp ℝ 2 μ :=
  (centeredErrorPairing_memLp_two E V).toLp (centeredErrorPairing E V)

/-- The L2 representative agrees almost everywhere with the displayed
source-level covariance pairing. -/
theorem centeredErrorPairingL2_coeFn_ae
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    (centeredErrorPairingL2 E V : Point D → ℝ) =ᵐ[μ] centeredErrorPairing E V := by
  exact MemLp.coeFn_toLp (centeredErrorPairing_memLp_two E V)

/-- The raw covariance pairing is additive in outcome-L2 representatives,
with equality understood spatially almost everywhere. -/
theorem centeredErrorPairing_add_ae
    (E : FixedConditionalExperiment μ P) (V W : Lp ℝ 2 P) :
    centeredErrorPairing E (V + W) =ᵐ[μ]
      centeredErrorPairing E V + centeredErrorPairing E W := by
  have hsum :
      (fun z : Ω × Point D => centeredError E z.1 z.2 * (V + W) z.1) =ᵐ[P.prod μ]
        (fun z => centeredError E z.1 z.2 * V z.1 + centeredError E z.1 z.2 * W z.1) := by
    have hsum_pre : (fun z : Ω × Point D => (V + W) z.1) =ᵐ[P.prod μ]
        (fun z => V z.1 + W z.1) :=
      Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_add V W)
    filter_upwards [hsum_pre] with z hz
    rw [hz]
    ring
  have hsum_swap :
      (fun z : Point D × Ω => centeredError E z.2 z.1 * (V + W) z.2) =ᵐ[μ.prod P]
        (fun z => centeredError E z.2 z.1 * V z.2 + centeredError E z.2 z.1 * W z.2) := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_swap (μ := μ) (ν := P)).quasiMeasurePreserving.ae_eq_comp hsum
  have hfiber := Measure.ae_ae_of_ae_prod hsum_swap
  have hVfiber := (centeredError_mul_outcomeL2_integrable E V).prod_left_ae
  have hWfiber := (centeredError_mul_outcomeL2_integrable E W).prod_left_ae
  filter_upwards [hfiber, hVfiber, hWfiber] with s hs hV hW
  change (∫ ω, centeredError E ω s * (V + W) ω ∂P) =
    (∫ ω, centeredError E ω s * V ω ∂P) +
      ∫ ω, centeredError E ω s * W ω ∂P
  rw [integral_congr_ae hs]
  exact integral_add hV hW

/-- The raw covariance pairing is homogeneous in outcome-L2 representatives,
again as a spatial almost-everywhere identity. -/
theorem centeredErrorPairing_smul_ae
    (E : FixedConditionalExperiment μ P) (a : ℝ) (V : Lp ℝ 2 P) :
    centeredErrorPairing E (a • V) =ᵐ[μ]
      a • centeredErrorPairing E V := by
  have hsmul :
      (fun z : Ω × Point D => centeredError E z.1 z.2 * (a • V) z.1) =ᵐ[P.prod μ]
        (fun z => a * (centeredError E z.1 z.2 * V z.1)) := by
    have hsmul_pre : (fun z : Ω × Point D => (a • V) z.1) =ᵐ[P.prod μ]
        (fun z => a • V z.1) :=
      Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_smul a V)
    filter_upwards [hsmul_pre] with z hz
    rw [hz]
    change centeredError E z.1 z.2 * (a * V z.1) = a * (centeredError E z.1 z.2 * V z.1)
    ring
  have hsmul_swap :
      (fun z : Point D × Ω => centeredError E z.2 z.1 * (a • V) z.2) =ᵐ[μ.prod P]
        (fun z => a * (centeredError E z.2 z.1 * V z.2)) := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_swap (μ := μ) (ν := P)).quasiMeasurePreserving.ae_eq_comp hsmul
  have hfiber := Measure.ae_ae_of_ae_prod hsmul_swap
  filter_upwards [hfiber] with s hs
  change (∫ ω, centeredError E ω s * (a • V) ω ∂P) =
    a * ∫ ω, centeredError E ω s * V ω ∂P
  rw [integral_congr_ae hs]
  rw [integral_const_mul]

/-- Additivity of the spatial-L2 covariance pairing. -/
theorem centeredErrorPairingL2_add
    (E : FixedConditionalExperiment μ P) (V W : Lp ℝ 2 P) :
    centeredErrorPairingL2 E (V + W) =
      centeredErrorPairingL2 E V + centeredErrorPairingL2 E W := by
  apply Lp.ext
  exact (centeredErrorPairingL2_coeFn_ae E (V + W)).trans
    ((centeredErrorPairing_add_ae E V W).trans
      (((centeredErrorPairingL2_coeFn_ae E V).add
        (centeredErrorPairingL2_coeFn_ae E W)).symm.trans
          (Lp.coeFn_add (centeredErrorPairingL2 E V) (centeredErrorPairingL2 E W)).symm))

/-- Homogeneity of the spatial-L2 covariance pairing. -/
theorem centeredErrorPairingL2_smul
    (E : FixedConditionalExperiment μ P) (a : ℝ) (V : Lp ℝ 2 P) :
    centeredErrorPairingL2 E (a • V) = a • centeredErrorPairingL2 E V := by
  apply Lp.ext
  have hVsmul : (fun s => a • (centeredErrorPairingL2 E V : Point D → ℝ) s) =ᵐ[μ]
      (fun s => a • centeredErrorPairing E V s) := by
    simpa [Function.comp_def] using
      (centeredErrorPairingL2_coeFn_ae E V).fun_comp (fun x : ℝ => a • x)
  exact (centeredErrorPairingL2_coeFn_ae E (a • V)).trans <|
    (centeredErrorPairing_smul_ae E a V).trans <|
      hVsmul.symm.trans (Lp.coeFn_smul a (centeredErrorPairingL2 E V)).symm

/-- The paper's map `V ↦ E[u(·)V]` as a genuine linear map from outcome L2
to spatial L2.  Its construction uses the source's fixed field and joint
second moment only; a norm-bound/continuity refinement is separate. -/
noncomputable def centeredErrorPairingLinearMap
    (E : FixedConditionalExperiment μ P) :
    Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := centeredErrorPairingL2 E
  map_add' := centeredErrorPairingL2_add E
  map_smul' := centeredErrorPairingL2_smul E

/-- The L2 norm squared of the spatial covariance pairing is its displayed
spatial square integral. -/
theorem centeredErrorPairingL2_norm_sq_eq_integral
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    ‖centeredErrorPairingL2 E V‖ ^ 2 =
      ∫ s, (centeredErrorPairing E V s) ^ 2 ∂μ := by
  calc
    ‖centeredErrorPairingL2 E V‖ ^ 2 =
        inner ℝ (centeredErrorPairingL2 E V) (centeredErrorPairingL2 E V) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ s, inner ℝ (centeredErrorPairingL2 E V s)
        (centeredErrorPairingL2 E V s) ∂μ :=
      L2.inner_def _ _
    _ = ∫ s, (centeredErrorPairing E V s) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [centeredErrorPairingL2_coeFn_ae E V] with s hs
      rw [hs]
      rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The product-L2 energy controls the squared norm of the source covariance
pairing operator. -/
theorem centeredErrorPairingL2_norm_sq_le
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    ‖centeredErrorPairingL2 E V‖ ^ 2 ≤
      (∫ z : Ω × Point D, centeredError E z.1 z.2 ^ 2 ∂(P.prod μ)) * ‖V‖ ^ 2 := by
  have hVnorm : ‖V‖ ^ 2 = ∫ ω, V ω ^ 2 ∂P := by
    calc
      ‖V‖ ^ 2 = inner ℝ V V := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ ω, inner ℝ (V ω) (V ω) ∂P := L2.inner_def _ _
      _ = ∫ ω, V ω ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [centeredErrorPairingL2_norm_sq_eq_integral, hVnorm]
  exact centeredErrorPairing_integral_sq_le E V

/-- The explicit boundedness estimate for the paper's covariance pairing
operator.  It is derived from the joint second moment alone. -/
theorem centeredErrorPairingL2_norm_bound
    (E : FixedConditionalExperiment μ P) (V : Lp ℝ 2 P) :
    ‖centeredErrorPairingL2 E V‖ ≤
      Real.sqrt (∫ z : Ω × Point D, centeredError E z.1 z.2 ^ 2 ∂(P.prod μ)) * ‖V‖ := by
  let energy : ℝ := ∫ z : Ω × Point D, centeredError E z.1 z.2 ^ 2 ∂(P.prod μ)
  have henergy : 0 ≤ energy := by
    dsimp [energy]
    exact integral_nonneg fun z => sq_nonneg (centeredError E z.1 z.2)
  have hright : 0 ≤ Real.sqrt energy * ‖V‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  calc
    ‖centeredErrorPairingL2 E V‖ ^ 2 ≤ energy * ‖V‖ ^ 2 := by
      simpa [energy] using centeredErrorPairingL2_norm_sq_le E V
    _ = (Real.sqrt energy * ‖V‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt henergy]

/-- The bounded continuous-linear version of the paper's map
`V ↦ E[u(·)V]`, constructed from the exact product-L2 energy bound. -/
noncomputable def centeredErrorPairingContinuousLinearMap
    (E : FixedConditionalExperiment μ P) :
    Lp ℝ 2 P →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous (centeredErrorPairingLinearMap E)
    (Real.sqrt (∫ z : Ω × Point D, centeredError E z.1 z.2 ^ 2 ∂(P.prod μ)))
    (centeredErrorPairingL2_norm_bound E)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
private theorem spatial_outcome_product_memLp_two
    (h : L2TestFunction μ) (V : Lp ℝ 2 P) :
    MemLp (fun z : Ω × Point D => h.1 z.2 * V z.1) 2 (P.prod μ) := by
  have hhsq : Integrable (fun s => h.1 s ^ 2) μ := h.2.integrable_sq
  have hVsq : Integrable (fun ω => V ω ^ 2) P := (Lp.memLp V).integrable_sq
  have hprodSq :
      Integrable (fun z : Ω × Point D => V z.1 ^ 2 * h.1 z.2 ^ 2) (P.prod μ) :=
    hVsq.mul_prod hhsq
  have hmeas :
      AEStronglyMeasurable (fun z : Ω × Point D => h.1 z.2 * V z.1) (P.prod μ) :=
    h.2.aestronglyMeasurable.comp_snd |>.mul
      ((Lp.memLp V).aestronglyMeasurable.comp_fst)
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  convert hprodSq using 1
  ext z
  ring

private theorem centeredErrorPairing_triple_integrable
    (E : FixedConditionalExperiment μ P) (h : L2TestFunction μ) (V : Lp ℝ 2 P) :
    Integrable (fun z : Ω × Point D =>
      h.1 z.2 * (centeredError E z.1 z.2 * V z.1)) (P.prod μ) := by
  have htestV := spatial_outcome_product_memLp_two (P := P) h V
  have hU := centeredError_memLp_two_product E
  have hmul := htestV.integrable_mul hU
  change Integrable
    ((fun z : Ω × Point D => h.1 z.2 * V z.1) *
      fun z => centeredError E z.1 z.2) (P.prod μ) at hmul
  convert hmul using 1
  ext z
  change h.1 z.2 * (centeredError E z.1 z.2 * V z.1) =
    (h.1 z.2 * V z.1) * centeredError E z.1 z.2
  ring

/-- The source-level Fubini identity relating the covariance pairing to a
centered spatial test integral.  This is the exact product-space calculation
underlying the covariance-Hilbert construction in Appendix `lem:mean`. -/
theorem centeredErrorPairing_fubini
    (E : FixedConditionalExperiment μ P) (h : L2TestFunction μ) (V : Lp ℝ 2 P) :
    (∫ s, h.1 s * centeredErrorPairing E V s ∂μ) =
      ∫ ω, V ω * centeredTestIntegral μ P E.error h ω ∂P := by
  have htriple := centeredErrorPairing_triple_integrable E h V
  calc
    (∫ s, h.1 s * centeredErrorPairing E V s ∂μ) =
        ∫ s, ∫ ω, h.1 s * (centeredError E ω s * V ω) ∂P ∂μ := by
      apply integral_congr_ae
      filter_upwards with s
      change h.1 s * (∫ ω, centeredError E ω s * V ω ∂P) = _
      rw [← integral_const_mul]
    _ = ∫ ω, ∫ s, h.1 s * (centeredError E ω s * V ω) ∂μ ∂P :=
      (integral_integral_swap htriple).symm
    _ = ∫ ω, V ω * (∫ s, h.1 s * centeredError E ω s ∂μ) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      calc
        (∫ s, h.1 s * (centeredError E ω s * V ω) ∂μ) =
            ∫ s, V ω * (h.1 s * centeredError E ω s) ∂μ := by
          apply integral_congr_ae
          filter_upwards with s
          ring
        _ = V ω * (∫ s, h.1 s * centeredError E ω s ∂μ) :=
          integral_const_mul _ _
    _ = ∫ ω, V ω * centeredTestIntegral μ P E.error h ω ∂P := by
      rfl

private theorem centered_test_integrand_integrable
    (E : FixedConditionalExperiment μ P) (h : L2TestFunction μ) :
    Integrable (fun z : Ω × Point D => h.1 z.2 * centeredError E z.1 z.2) (P.prod μ) := by
  have htest : MemLp (fun z : Ω × Point D => h.1 z.2) 2 (P.prod μ) :=
    h.2.comp_snd P
  exact (htest.mul (centeredError_memLp_two_product E) (r := 1)).integrable (by norm_num)

/-- Each centered test integral is integrable directly from the product-L2
bound, independently of the Gaussian shortcut used to package it in outcome
L2. -/
theorem centeredTestIntegral_integrable
    (E : FixedConditionalExperiment μ P) (h : L2TestFunction μ) :
    Integrable (centeredTestIntegral μ P E.error h) P := by
  change Integrable (fun ω =>
    ∫ s, h.1 s * centeredError E ω s ∂μ) P
  simpa using (centered_test_integrand_integrable E h).integral_prod_left

/-- Linearity in a pair of literal spatial L2 representatives.  This is an
almost-everywhere statement because the outcome L2 space identifies random
variables modulo the fixed outcome law. -/
theorem centeredTestIntegral_add_ae
    (E : FixedConditionalExperiment μ P) (h g : L2TestFunction μ) :
    centeredTestIntegral μ P E.error ⟨h.1 + g.1, h.2.add g.2⟩ =ᵐ[P]
      centeredTestIntegral μ P E.error h + centeredTestIntegral μ P E.error g := by
  have hfiber_h : ∀ᵐ ω ∂P,
      Integrable (fun s => h.1 s * centeredError E ω s) μ :=
    (centered_test_integrand_integrable E h).prod_right_ae
  have hfiber_g : ∀ᵐ ω ∂P,
      Integrable (fun s => g.1 s * centeredError E ω s) μ :=
    (centered_test_integrand_integrable E g).prod_right_ae
  filter_upwards [hfiber_h, hfiber_g] with ω hh hg
  change (∫ s, (h.1 s + g.1 s) * centeredError E ω s ∂μ) =
    (∫ s, h.1 s * centeredError E ω s ∂μ) +
      ∫ s, g.1 s * centeredError E ω s ∂μ
  rw [show (fun s => (h.1 s + g.1 s) * centeredError E ω s) =
      (fun s => h.1 s * centeredError E ω s + g.1 s * centeredError E ω s) by
        funext s
        ring]
  exact integral_add hh hg

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Scalar linearity for literal spatial L2 representatives. -/
theorem centeredTestIntegral_smul_ae
    (E : FixedConditionalExperiment μ P) (a : ℝ) (h : L2TestFunction μ) :
    centeredTestIntegral μ P E.error ⟨a • h.1, h.2.const_smul a⟩ =ᵐ[P]
      a • centeredTestIntegral μ P E.error h := by
  filter_upwards with ω
  change (∫ s, (a * h.1 s) * centeredError E ω s ∂μ) =
    a * ∫ s, h.1 s * centeredError E ω s ∂μ
  rw [show (fun s => (a * h.1 s) * centeredError E ω s) =
      fun s => a * (h.1 s * centeredError E ω s) by
        funext s
        ring]
  rw [integral_const_mul]

/-- The fixed spatial function to which the paper applies `lem:mean`: its
conditional error mean minus one fixed control combination. -/
noncomputable def spatialMeanOffset
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) : Point D → ℝ :=
  fun s => conditionalErrorMean P E.error s - dotProduct (fun j => E.controls j s) c

omit [IsProbabilityMeasure P] in
private theorem controls_dot_integrable
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) :
    Integrable (fun s => dotProduct (fun j => E.controls j s) c) μ := by
  classical
  have hsum : Integrable (fun s => ∑ j, E.controls j s * c j) μ := by
    exact integrable_finsetSum Finset.univ fun j _ =>
      (control_memLp_two E j).integrable (by norm_num) |>.mul_const (c j)
  simpa [dotProduct] using hsum

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
private theorem controls_dot_memLp_two
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) :
    MemLp (fun s => dotProduct (fun j => E.controls j s) c) 2 μ := by
  classical
  have hsum : MemLp (fun s => ∑ j, E.controls j s * c j) 2 μ := by
    exact memLp_finsetSum Finset.univ fun j _ =>
      (control_memLp_two E j).mul_const (c j)
  simpa [dotProduct] using hsum

/-- The fixed spatial residual `m - Wc` is in spatial L2 under the exact
existing source moment conditions.  This is the `f ∈ L²(T, μ)` premise in
Appendix `lem:mean`, derived here rather than appended as an assumption. -/
theorem spatialMeanOffset_memLp_two
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) :
    MemLp (spatialMeanOffset E c) 2 μ := by
  change MemLp
    (conditionalErrorMean P E.error - fun s => dotProduct (fun j => E.controls j s) c) 2 μ
  exact (conditional_error_mean_memLp_two E).sub (controls_dot_memLp_two E c)

/-- The source fixed residual `m - Wc`, packaged as its spatial L2 class. -/
noncomputable def spatialMeanOffsetL2
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) : Lp ℝ 2 μ :=
  (spatialMeanOffset_memLp_two E c).toLp (spatialMeanOffset E c)

/-- The packaged fixed residual agrees almost everywhere with its displayed
spatial formula. -/
theorem spatialMeanOffsetL2_coeFn_ae
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) :
    (spatialMeanOffsetL2 E c : Point D → ℝ) =ᵐ[μ] spatialMeanOffset E c := by
  unfold spatialMeanOffsetL2
  exact MemLp.coeFn_toLp (spatialMeanOffset_memLp_two E c)

/-- The linear functional `h ↦ ∫ (m-Wc)h dμ` used in the paper's
covariance-Hilbert argument.  It is constructed from the already derived
spatial-L2 residual, rather than introduced as an assumption. -/
@[expose] noncomputable def spatialMeanOffsetFunctional
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) :
    Lp ℝ 2 μ →ₗ[ℝ] ℝ :=
  (innerSL ℝ (spatialMeanOffsetL2 E c)).toLinearMap

/-- Public Hilbert-space form of the fixed spatial mean functional.  This is
the existing `innerSL` definition written at one argument, not a new
covariance-space assumption. -/
theorem spatialMeanOffsetFunctional_eq_inner
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) (h : Lp ℝ 2 μ) :
    spatialMeanOffsetFunctional E c h = inner ℝ (spatialMeanOffsetL2 E c) h :=
  rfl

/-- Pointwise integral form of the paper's fixed spatial functional. -/
theorem spatialMeanOffsetFunctional_apply
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) (h : Lp ℝ 2 μ) :
    spatialMeanOffsetFunctional E c h =
      ∫ s, spatialMeanOffset E c s * h s ∂μ := by
  change inner ℝ (spatialMeanOffsetL2 E c) h = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spatialMeanOffsetL2_coeFn_ae E c] with s hs
  rw [hs]
  simp
  ring

/-- The source's finite-second-moment and regressor-second-moment fields
already imply that the paper's fixed spatial mean residual belongs to L1.
No regularity assumption is added here. -/
theorem spatialMeanOffset_integrable
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) :
    Integrable (spatialMeanOffset E c) μ := by
  exact (conditional_error_mean_integrable E).sub (controls_dot_integrable E c)

/-- The exact connection between the source's vector `meanOffset` and the
regional means of the paper's one fixed spatial function `m - Wc`.  The only
Fubini step is imported from the already completed L-025 bridge. -/
theorem meanOffset_apply_eq_regionalValues_spatialMeanOffset
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) (n : ℕ)
    (i : Fin (E.maps.N n)) :
    meanOffset E c n i = regionalValues μ E.maps (spatialMeanOffset E c) n i := by
  classical
  rw [meanOffset, Pi.sub_apply]
  rw [← regionalMeanCompatibility_of_fixedLawHypotheses E n i]
  change cellMean μ ((E.maps.partition n).cell i) (conditionalErrorMean P E.error) -
      ∑ j, cellMean μ ((E.maps.partition n).cell i) (E.controls j) * c j =
    cellMean μ ((E.maps.partition n).cell i)
      (fun s => conditionalErrorMean P E.error s - dotProduct (fun j => E.controls j s) c)
  symm
  apply setAverage_sub_dotProduct
  · exact (conditional_error_mean_integrable E).restrict
  · intro j
    exact ((control_memLp_two E j).integrable (by norm_num)).restrict

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The finite matrix Cauchy--Schwarz line in the Appendix mean argument.
For an arbitrary vector of regional test weights, the score against the
fixed regional mean residual is controlled by its inverse-working-covariance
energy and the working covariance quadratic form.  This is a direct reuse of
the existing positive-definite matrix identity, with `meanEnergy` expanded
only definitionally. -/
theorem meanOffset_score_sq_le_meanEnergy_mul_workingQuadratic
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) (n : ℕ)
    (weight : Fin (E.maps.N n) → ℝ) :
    (meanOffset E c n ⬝ᵥ weight) ^ 2 ≤
      meanEnergy E c n * quadraticForm (E.kernel n) weight := by
  let K := E.kernel n
  let f := meanOffset E c n
  have hprecision : K⁻¹.PosDef := (E.kernel_posDef n).inv
  have hcs := InfillGLSLean.precision_score_sq_le_quadraticForms
    hprecision (K *ᵥ weight) f
  change (f ⬝ᵥ weight) ^ 2 ≤
    quadraticForm K⁻¹ f * quadraticForm K weight
  rw [InfillGLSLean.quadraticForm_inverse_working_mulVec_eq
      (E.kernel_posDef n) weight,
    InfillGLSLean.workingCovariance_dual_score_eq
      (E.kernel_posDef n) weight f] at hcs
  simpa [K, f, meanEnergy, dotProduct_comm, mul_comm] using hcs

/-- The lower half of the paper's covariance sandwich transfers a true
regional covariance quadratic form back to the working covariance quadratic
form.  Its only scalar hypotheses are exactly the positivity already present
in `CovarianceAssumption`: `sigmaSquared > 0` and `delta ≥ 0`. -/
theorem workingQuadratic_le_trueQuadratic_of_lowerSandwich
    {I : Type*} [Fintype I]
    (truth working : Matrix I I ℝ) (sigmaSquared delta : ℝ)
    (hsigma : 0 < sigmaSquared) (hdelta : 0 ≤ delta)
    (hlower : (truth - (sigmaSquared / (1 + delta)) • working).PosSemidef)
    (weight : I → ℝ) :
    quadraticForm working weight ≤
      ((1 + delta) / sigmaSquared) * quadraticForm truth weight := by
  have hdenom : 0 < 1 + delta := by linarith
  have hscale : 0 < sigmaSquared / (1 + delta) := div_pos hsigma hdenom
  have hmono : (sigmaSquared / (1 + delta)) * quadraticForm working weight ≤
      quadraticForm truth weight := by
    calc
      (sigmaSquared / (1 + delta)) * quadraticForm working weight =
          quadraticForm ((sigmaSquared / (1 + delta)) • working) weight :=
        (InfillGLSLean.quadraticForm_smul _ _ _).symm
      _ ≤ quadraticForm truth weight :=
        InfillGLSLean.quadraticForm_mono_of_posSemidef_sub hlower weight
  calc
    quadraticForm working weight ≤
        quadraticForm truth weight / (sigmaSquared / (1 + delta)) :=
      (le_div_iff₀ hscale).mpr (by simpa [mul_comm] using hmono)
    _ = ((1 + delta) / sigmaSquared) * quadraticForm truth weight := by
      field_simp [hsigma.ne', hdenom.ne']

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The manuscript's finite supremum of inverse-working-covariance mean
energies has a nonnegative real upper bound.  Nonnegativity is derived from
the positive definiteness of each specified working kernel; it is not an
extra boundedness condition. -/
theorem exists_nonnegative_meanEnergy_upper_bound
    (E : FixedConditionalExperiment μ P) (mean : FixedMeanAssumption E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, meanEnergy E mean.c n ≤ M := by
  rcases mean.bounded_energy with ⟨M, hM⟩
  refine ⟨M, ?_, ?_⟩
  · have henergy : 0 ≤ meanEnergy E mean.c 0 := by
      change 0 ≤ quadraticForm (E.kernel 0)⁻¹ (meanOffset E mean.c 0)
      exact InfillGLSLean.quadraticForm_nonneg
        ((E.kernel_posDef 0).inv.posSemidef) _
    exact henergy.trans (hM (Set.mem_range_self 0))
  · intro n
    exact hM (Set.mem_range_self n)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The finite regional score bound after the lower covariance sandwich.
This is the precise combination of finite matrix Cauchy--Schwarz and the
lower sandwich used in the mean proof; it has not yet identified a regional
weight with an arbitrary spatial test or taken the L2 approximation limit. -/
theorem meanOffset_score_sq_le_energy_trueQuadratic_of_lowerSandwich
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) (n : ℕ)
    (sigmaSquared delta : ℝ)
    (hdelta : 0 ≤ delta) (hsigma : 0 < sigmaSquared)
    (hlower : (trueCovariance E n -
      (sigmaSquared / (1 + delta)) • E.kernel n).PosSemidef)
    (weight : Fin (E.maps.N n) → ℝ) :
    (meanOffset E c n ⬝ᵥ weight) ^ 2 ≤
      meanEnergy E c n * ((1 + delta) / sigmaSquared) *
        quadraticForm (trueCovariance E n) weight := by
  have henergy_nonneg : 0 ≤ meanEnergy E c n := by
    change 0 ≤ quadraticForm (E.kernel n)⁻¹ (meanOffset E c n)
    exact InfillGLSLean.quadraticForm_nonneg
      ((E.kernel_posDef n).inv.posSemidef) _
  have hworking := meanOffset_score_sq_le_meanEnergy_mul_workingQuadratic
    E c n weight
  have htransfer := workingQuadratic_le_trueQuadratic_of_lowerSandwich
    (trueCovariance E n) (E.kernel n) sigmaSquared delta hsigma hdelta hlower weight
  calc
    (meanOffset E c n ⬝ᵥ weight) ^ 2 ≤
        meanEnergy E c n * quadraticForm (E.kernel n) weight := hworking
    _ ≤ meanEnergy E c n *
        (((1 + delta) / sigmaSquared) * quadraticForm (trueCovariance E n) weight) :=
      mul_le_mul_of_nonneg_left htransfer henergy_nonneg
    _ = meanEnergy E c n * ((1 + delta) / sigmaSquared) *
        quadraticForm (trueCovariance E n) weight := by ring

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The centered test integral in the manuscript's covariance assumption is
an actual outcome-side L2 random variable for every spatial L2 test.  This is
not an added moment hypothesis: it follows directly from the existing
Gaussian-process field in `CovarianceAssumption`. -/
theorem centeredTestIntegral_memLp_two
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : L2TestFunction μ) :
    MemLp (centeredTestIntegral μ P E.error h) 2 P := by
  exact (cov.centered_field_gaussian.hasGaussianLaw_eval h).memLp_two

/-- The source covariance process, viewed in the outcome L2 space at one
spatial test.  This is deliberately a map on the source's `L2TestFunction`
representatives; proving descent to the spatial L2 quotient is a later,
separate obligation. -/
noncomputable def centeredTestIntegralL2
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : L2TestFunction μ) : Lp ℝ 2 P :=
  (centeredTestIntegral_memLp_two E cov h).toLp (centeredTestIntegral μ P E.error h)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The L2 representative above has exactly the centered-test-integral
version of the source process almost surely. -/
theorem centeredTestIntegralL2_coeFn_ae
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : L2TestFunction μ) :
    centeredTestIntegralL2 E cov h =ᵐ[P] centeredTestIntegral μ P E.error h := by
  exact MemLp.coeFn_toLp (centeredTestIntegral_memLp_two E cov h)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Centered spatial test integrals respect equality of spatial tests in
 L2.  This is the quotient-compatibility part of the covariance construction;
 it uses the source formula directly and does not invoke an RKHS or pointwise
 evaluation convention. -/
theorem centeredTestIntegral_ae_congr
    (E : FixedConditionalExperiment μ P) (h g : L2TestFunction μ)
    (hfg : h.1 =ᵐ[μ] g.1) :
    centeredTestIntegral μ P E.error h =ᵐ[P] centeredTestIntegral μ P E.error g := by
  filter_upwards with ω
  apply integral_congr_ae
  filter_upwards [hfg] with s hs
  simp only [hs]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The outcome-L2 representatives respect spatial L2 equality. -/
theorem centeredTestIntegralL2_congr
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h g : L2TestFunction μ) (hfg : h.1 =ᵐ[μ] g.1) :
    centeredTestIntegralL2 E cov h = centeredTestIntegralL2 E cov g := by
  apply MemLp.toLp_congr
  exact centeredTestIntegral_ae_congr E h g hfg

/-- Addition for the outcome-L2 representatives of two literal spatial L2
 tests. -/
theorem centeredTestIntegralL2_add
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h g : L2TestFunction μ) :
    centeredTestIntegralL2 E cov ⟨h.1 + g.1, h.2.add g.2⟩ =
      centeredTestIntegralL2 E cov h + centeredTestIntegralL2 E cov g := by
  apply Lp.ext
  filter_upwards [
    centeredTestIntegralL2_coeFn_ae E cov ⟨h.1 + g.1, h.2.add g.2⟩,
    centeredTestIntegralL2_coeFn_ae E cov h,
    centeredTestIntegralL2_coeFn_ae E cov g,
    Lp.coeFn_add (centeredTestIntegralL2 E cov h) (centeredTestIntegralL2 E cov g),
    centeredTestIntegral_add_ae E h g]
    with ω hadd hh hg hsum hlin
  rw [hadd, hsum]
  simpa only [Pi.add_apply, hh, hg] using hlin

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Scalar multiplication for outcome-L2 representatives of literal spatial
 L2 tests. -/
theorem centeredTestIntegralL2_smul
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (a : ℝ) (h : L2TestFunction μ) :
    centeredTestIntegralL2 E cov ⟨a • h.1, h.2.const_smul a⟩ =
      a • centeredTestIntegralL2 E cov h := by
  apply Lp.ext
  filter_upwards [
    centeredTestIntegralL2_coeFn_ae E cov ⟨a • h.1, h.2.const_smul a⟩,
    centeredTestIntegralL2_coeFn_ae E cov h,
    Lp.coeFn_smul a (centeredTestIntegralL2 E cov h),
    centeredTestIntegral_smul_ae E a h] with ω ha hh hsmul hlin
  rw [ha, hsmul]
  simpa only [Pi.smul_apply, smul_eq_mul, hh] using hlin

/-- The canonical test-function representative carried by a spatial L2
equivalence class. -/
noncomputable def l2TestOfLp (h : Lp ℝ 2 μ) : L2TestFunction μ :=
  ⟨(h : Point D → ℝ), Lp.memLp h⟩

/-- The source centered Gaussian process as a function from the spatial L2
space into the outcome L2 space.  The definition uses Mathlib's canonical
function representative of an `Lp` class.  Linearity and boundedness remain
separate proof obligations; neither is built into this definition. -/
@[expose] noncomputable def centeredTestIntegralLp
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E) :
    Lp ℝ 2 μ → Lp ℝ 2 P :=
  fun h => centeredTestIntegralL2 E cov (l2TestOfLp h)

/-- Passing an existing literal `L²` test through its quotient class leaves
the centered test integral unchanged.  This is the exact a.e.-congruence
bridge used for finite common-refinement covariance entries. -/
theorem centeredTestIntegralLp_toLp
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : L2TestFunction μ) :
    centeredTestIntegralLp E cov (h.2.toLp h.1) = centeredTestIntegralL2 E cov h := by
  unfold centeredTestIntegralLp
  apply centeredTestIntegralL2_congr
  simpa [l2TestOfLp] using MemLp.coeFn_toLp h.2

/-- The quotient-level form of `centeredErrorPairing_fubini`: the bounded
map `V ↦ E[u(·) V]` is paired with the manuscript's centered spatial-average
map by the exact real-L2 inner-product identity.  The statement uses no
regularity beyond the fixed joint second moment and the source's existing
outcome-L2 packaging of centered tests. -/
theorem inner_centeredErrorPairingL2_eq_inner_centeredTestIntegralLp
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : Lp ℝ 2 μ) (V : Lp ℝ 2 P) :
    inner ℝ (centeredErrorPairingL2 E V) h =
      inner ℝ V (centeredTestIntegralLp E cov h) := by
  have hfubini := centeredErrorPairing_fubini E (l2TestOfLp h) V
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ s, inner ℝ (centeredErrorPairingL2 E V s) (h s) ∂μ) =
        ∫ s, (l2TestOfLp h).1 s * centeredErrorPairing E V s ∂μ := by
      apply integral_congr_ae
      filter_upwards [centeredErrorPairingL2_coeFn_ae E V] with s hs
      rw [hs]
      simp [l2TestOfLp]
    _ = ∫ ω, V ω * centeredTestIntegral μ P E.error (l2TestOfLp h) ω ∂P :=
      hfubini
    _ = ∫ ω, inner ℝ (V ω) (centeredTestIntegralLp E cov h ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [centeredTestIntegralL2_coeFn_ae E cov (l2TestOfLp h)] with ω hω
      change V ω * centeredTestIntegral μ P E.error (l2TestOfLp h) ω =
        inner ℝ (V ω) (centeredTestIntegralL2 E cov (l2TestOfLp h) ω)
      rw [hω]
      simp
      ring

/-- The centered spatial-integration map is the Hilbert adjoint of the
already bounded covariance-pairing map.  This uses no new covariance
assumption: the following equality proves that this adjoint is exactly the
source `centeredTestIntegralLp` map supplied by the existing field clause. -/
noncomputable def centeredTestIntegralContinuousLinearMap
    (E : FixedConditionalExperiment μ P) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P :=
  ContinuousLinearMap.adjoint (centeredErrorPairingContinuousLinearMap E)

/-- Exact adjoint identification for the source spatial-test map.  In
particular it supplies the continuity needed to pass L-026 regional L2
approximations through centered spatial integration. -/
theorem centeredTestIntegralContinuousLinearMap_apply
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : Lp ℝ 2 μ) :
    centeredTestIntegralContinuousLinearMap E h = centeredTestIntegralLp E cov h := by
  apply ext_inner_right ℝ
  intro V
  calc
    inner ℝ (centeredTestIntegralContinuousLinearMap E h) V =
        inner ℝ h (centeredErrorPairingContinuousLinearMap E V) :=
      ContinuousLinearMap.adjoint_inner_left
        (centeredErrorPairingContinuousLinearMap E) V h
    _ = inner ℝ (centeredErrorPairingL2 E V) h := by
      change inner ℝ h (centeredErrorPairingL2 E V) =
        inner ℝ (centeredErrorPairingL2 E V) h
      rw [real_inner_comm]
    _ = inner ℝ V (centeredTestIntegralLp E cov h) :=
      inner_centeredErrorPairingL2_eq_inner_centeredTestIntegralLp E cov h V
    _ = inner ℝ (centeredTestIntegralLp E cov h) V := by
      rw [real_inner_comm]

/-! ### Exact finite regional-test bridge

The next definitions and lemmas make the finite vectors in the source
covariance sandwich literal spatial L2 tests.  They are only the normalized
indicators of the already observed regions and their finite linear
combinations.  This is the finite part of the Appendix `lem:mean` argument;
the separate L-026 limit is used only after these exact identities. -/

private theorem regional_error_integrableOn_ae
    (E : FixedConditionalExperiment μ P) (n : ℕ) (i : Fin (E.maps.N n)) :
    ∀ᵐ ω ∂P, IntegrableOn (E.error ω) ((E.maps.partition n).cell i) μ := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  have hmeasure : P.prod (μ.restrict R) =
      (P.prod μ).restrict (Set.univ ×ˢ R) := by
    calc
      P.prod (μ.restrict R) = (P.restrict Set.univ).prod (μ.restrict R) := by
        rw [Measure.restrict_univ]
      _ = (P.prod μ).restrict (Set.univ ×ˢ R) := by
        rw [Measure.prod_restrict]
  have hrestrict : Integrable
      (fun z : Ω × Point D => E.error z.1 z.2) (P.prod (μ.restrict R)) := by
    rw [hmeasure]
    exact (error_product_integrable E).restrict
  simpa only [IntegrableOn, R] using
    (integrable_prod_iff E.error_jointly_measurable.aestronglyMeasurable).mp
      hrestrict |>.1

private theorem regional_error_integrable
    (E : FixedConditionalExperiment μ P) (n : ℕ) (i : Fin (E.maps.N n)) :
    Integrable (regionalRandomValues μ E.maps E.error n i) P := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  have hmeasure : P.prod (μ.restrict R) =
      (P.prod μ).restrict (Set.univ ×ˢ R) := by
    calc
      P.prod (μ.restrict R) = (P.restrict Set.univ).prod (μ.restrict R) := by
        rw [Measure.restrict_univ]
      _ = (P.prod μ).restrict (Set.univ ×ˢ R) := by
        rw [Measure.prod_restrict]
  have hrestrict : Integrable
      (fun z : Ω × Point D => E.error z.1 z.2) (P.prod (μ.restrict R)) := by
    rw [hmeasure]
    exact (error_product_integrable E).restrict
  have hinterior : Integrable (fun ω => ∫ s, E.error ω s ∂(μ.restrict R)) P :=
    hrestrict.integral_prod_left
  change Integrable (fun ω => ⨍ s in R, E.error ω s ∂μ) P
  rw [show (fun ω => ⨍ s in R, E.error ω s ∂μ) =
      fun ω => (μ.real R)⁻¹ • ∫ s, E.error ω s ∂(μ.restrict R) by
        funext ω
        rw [setAverage_eq]]
  exact hinterior.const_mul _

/-- The normalized indicator of one source region, viewed as the literal
L2 test whose centered spatial integral is that region's centered error
average. -/
noncomputable def regionalCellAverageTest
    (E : FixedConditionalExperiment μ P) (n : ℕ) (i : Fin (E.maps.N n)) :
    L2TestFunction μ :=
  ⟨(E.maps.partition n).cell i |>.indicator
      (fun _ => (μ.real ((E.maps.partition n).cell i))⁻¹), by
    apply memLp_indicator_const 2
      ((E.maps.partition n).measurable_cell i).nullMeasurableSet
    right
    exact measure_ne_top μ ((E.maps.partition n).cell i)⟩

/-- A finite regional vector, rendered as its exact spatial test function:
the weighted sum of normalized cell indicators. -/
@[expose] noncomputable def weightedRegionalCellTest
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (weight : Fin (E.maps.N n) → ℝ) : L2TestFunction μ :=
  ⟨fun s => ∑ i, weight i * (regionalCellAverageTest E n i).1 s, by
    exact memLp_finsetSum Finset.univ fun i _ =>
      (regionalCellAverageTest E n i).2.const_mul (weight i)⟩

/-- The finite weight vector which turns the normalized regional-cell tests
into the literal regional projection of a spatial function. -/
@[expose]
noncomputable def regionalProjectionWeights
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ) (n : ℕ) :
    Fin (E.maps.N n) → ℝ :=
  fun i => μ.real ((E.maps.partition n).cell i) * regionalValues μ E.maps f n i

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Entrywise form of `regionalProjectionWeights`; this is the literal
cell-mass-times-cell-average coefficient used by the regional projection. -/
theorem regionalProjectionWeights_apply
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ) (n : ℕ)
    (i : Fin (E.maps.N n)) :
    regionalProjectionWeights E f n i =
      μ.real ((E.maps.partition n).cell i) * regionalValues μ E.maps f n i := rfl

omit [IsProbabilityMeasure P] in
/-- Exact pointwise identification of the L-026 regional projection with a
weighted sum of the normalized regional-cell tests.  Positivity of each
source cell is enough to cancel its normalizing factor; no nesting or
additional regularity of the regions is used. -/
theorem weightedRegionalCellTest_eq_regionalProjection
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ) (n : ℕ) :
    (weightedRegionalCellTest E n (regionalProjectionWeights E f n)).1 =
      InfillGLSLean.ManuscriptSpecification.L026.regionalProjection
        (E.maps.partition n) f := by
  funext s
  simp only [weightedRegionalCellTest, regionalProjectionWeights,
    regionalCellAverageTest,
    InfillGLSLean.ManuscriptSpecification.L026.regionalProjection_apply,
    regionalValues]
  apply Finset.sum_congr rfl
  intro i hi
  let R : Set (Point D) := (E.maps.partition n).cell i
  have hRpos : 0 < μ.real R := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((E.maps.partition n).positive_measure i).ne'
      (measure_ne_top μ R)
  change (μ.real R * cellMean μ R f) *
      R.indicator (fun _ => (μ.real R)⁻¹) s =
    R.indicator (fun _ => cellMean μ R f) s
  by_cases hs : s ∈ R
  · simp only [Set.indicator_of_mem hs]
    calc
      μ.real R * cellMean μ R f * (μ.real R)⁻¹ =
          (μ.real R * (μ.real R)⁻¹) * cellMean μ R f := by ring
      _ = cellMean μ R f := by rw [mul_inv_cancel₀ hRpos.ne', one_mul]
  · simp [hs]

/-- The Lp class of the literal L-026 regional projection. -/
noncomputable def regionalProjectionLp
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ)
    (hf : MemLp f 2 μ) (n : ℕ) : Lp ℝ 2 μ :=
  (InfillGLSLean.ManuscriptSpecification.L026.memLp_regionalProjection
    (E.maps.partition n) hf).toLp _

private theorem indicator_const_mul_eq_indicator
    (R : Set (Point D)) (a : ℝ) (g : Point D → ℝ) :
    (fun s => R.indicator (fun _ => a) s * g s) =
      R.indicator (fun s => a * g s) := by
  funext s
  by_cases hs : s ∈ R <;> simp [hs]

/-- One centered regional error average is, almost everywhere under the
fixed outcome law, exactly the centered spatial test integral for its
normalized cell indicator. -/
private theorem centeredTestIntegral_cell_ae_eq
    (E : FixedConditionalExperiment μ P) (n : ℕ) (i : Fin (E.maps.N n)) :
    centeredIntegralProcess μ P E.error (regionalCellAverageTest E n i) =ᵐ[P]
      centeredFiniteError
        (regionalRandomValues μ E.maps E.error n)
        (regionalConditionalMean E.maps P E.error n) i := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  let a : ℝ := (μ.real R)⁻¹
  have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
  have hm : Integrable (conditionalErrorMean P E.error) (μ.restrict R) :=
    (conditional_error_mean_integrable E).restrict
  have hcompat := regionalMeanCompatibility_of_fixedLawHypotheses E n i
  filter_upwards [regional_error_integrableOn_ae E n i] with ω hω
  have hsub : Integrable (fun s => E.error ω s - conditionalErrorMean P E.error s)
      (μ.restrict R) := hω.sub hm
  rw [centeredIntegralProcess_apply, centeredTestIntegral_apply, centeredFiniteError_apply]
  change (∫ s, (regionalCellAverageTest E n i).1 s *
      (E.error ω s - conditionalErrorMean P E.error s) ∂μ) =
        regionalRandomValues μ E.maps E.error n i ω -
          regionalConditionalMean E.maps P E.error n i
  change (∫ s, R.indicator (fun _ => a) s *
      (E.error ω s - conditionalErrorMean P E.error s) ∂μ) = _
  rw [indicator_const_mul_eq_indicator, integral_indicator hR]
  rw [integral_const_mul, integral_sub hω hm]
  rw [mul_sub]
  have hregional : regionalRandomValues μ E.maps E.error n i ω =
      a * (∫ s in R, E.error ω s ∂μ) := by
    simp [regionalRandomValues, cellMean, setAverage_eq, R, a, smul_eq_mul]
  rw [hregional]
  congr 1
  rw [← hcompat]
  simp [regionalMeanFromSpatialConditionalMean, regionalValues, cellMean,
    setAverage_eq, R, a, smul_eq_mul]

private theorem cell_centered_integrand_integrable_ae
    (E : FixedConditionalExperiment μ P) (n : ℕ) (i : Fin (E.maps.N n)) :
    ∀ᵐ ω ∂P, Integrable (fun s => (regionalCellAverageTest E n i).1 s *
      (E.error ω s - conditionalErrorMean P E.error s)) μ := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  let a : ℝ := (μ.real R)⁻¹
  have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
  have hm : Integrable (conditionalErrorMean P E.error) (μ.restrict R) :=
    (conditional_error_mean_integrable E).restrict
  filter_upwards [regional_error_integrableOn_ae E n i] with ω hω
  have hsub : Integrable (fun s => E.error ω s - conditionalErrorMean P E.error s)
      (μ.restrict R) := hω.sub hm
  change Integrable (fun s => R.indicator (fun _ => a) s *
    (E.error ω s - conditionalErrorMean P E.error s)) μ
  rw [indicator_const_mul_eq_indicator, integrable_indicator_iff hR]
  exact hsub.const_mul _

/-- The centered integral of a finite weighted regional-cell test is a.e.
the corresponding finite weighted centered regional error score. -/
private theorem centeredTestIntegral_weighted_ae_eq_score
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (weight : Fin (E.maps.N n) → ℝ) :
    centeredIntegralProcess μ P E.error (weightedRegionalCellTest E n weight) =ᵐ[P]
      finiteWeightedScore weight
        (centeredFiniteError
          (regionalRandomValues μ E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n)) := by
  have hintegrable : ∀ᵐ ω ∂P, ∀ i,
      Integrable (fun s => (regionalCellAverageTest E n i).1 s *
        (E.error ω s - conditionalErrorMean P E.error s)) μ :=
    ae_all_iff.2 fun i => cell_centered_integrand_integrable_ae E n i
  have hcell : ∀ᵐ ω ∂P, ∀ i,
      centeredIntegralProcess μ P E.error (regionalCellAverageTest E n i) ω =
        centeredFiniteError
          (regionalRandomValues μ E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n) i ω :=
    ae_all_iff.2 fun i => centeredTestIntegral_cell_ae_eq E n i
  filter_upwards [hintegrable, hcell] with ω hInt hCell
  rw [centeredIntegralProcess_apply, centeredTestIntegral_apply]
  change (∫ s, (∑ i, weight i * (regionalCellAverageTest E n i).1 s) *
      (E.error ω s - conditionalErrorMean P E.error s) ∂μ) =
        finiteWeightedScore weight
          (centeredFiniteError
            (regionalRandomValues μ E.maps E.error n)
            (regionalConditionalMean E.maps P E.error n)) ω
  have hsum : (fun s => (∑ i, weight i * (regionalCellAverageTest E n i).1 s) *
      (E.error ω s - conditionalErrorMean P E.error s)) =
      fun s => ∑ i, weight i * ((regionalCellAverageTest E n i).1 s *
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

private theorem centered_regional_error_integral_eq_zero
    (E : FixedConditionalExperiment μ P) (n : ℕ) (i : Fin (E.maps.N n)) :
    P[centeredFiniteError
      (regionalRandomValues μ E.maps E.error n)
      (regionalConditionalMean E.maps P E.error n) i] = 0 := by
  have hraw : Integrable (regionalRandomValues μ E.maps E.error n i) P :=
    regional_error_integrable E n i
  simp_rw [centeredFiniteError_apply]
  rw [integral_sub hraw (integrable_const _), integral_const]
  simp [regionalConditionalMean]

private theorem centered_regional_error_memLp_two
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (i : Fin (E.maps.N n)) :
    MemLp (centeredFiniteError
      (regionalRandomValues μ E.maps E.error n)
      (regionalConditionalMean E.maps P E.error n) i) 2 P := by
  have htest : MemLp
      (centeredIntegralProcess μ P E.error (regionalCellAverageTest E n i)) 2 P :=
    (cov.centered_field_gaussian.hasGaussianLaw_eval (regionalCellAverageTest E n i)).memLp_two
  exact htest.ae_eq (centeredTestIntegral_cell_ae_eq E n i)

private theorem centered_regional_error_covariance_eq_true
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    finiteErrorCovariance
      (centeredFiniteError (regionalRandomValues μ E.maps E.error n)
        (regionalConditionalMean E.maps P E.error n)) P = trueCovariance E n := by
  ext i j
  simp only [finiteErrorCovariance_apply, trueCovariance]
  change cov[(fun ω => regionalRandomValues μ E.maps E.error n i ω -
      regionalConditionalMean E.maps P E.error n i),
    (fun ω => regionalRandomValues μ E.maps E.error n j ω -
      regionalConditionalMean E.maps P E.error n j); P] =
    cov[regionalRandomValues μ E.maps E.error n i,
      regionalRandomValues μ E.maps E.error n j; P]
  rw [covariance_sub_const_left (regional_error_integrable E n i),
    covariance_sub_const_right (regional_error_integrable E n j)]

private theorem weighted_centered_regional_score_sq_integral_eq_trueQuadratic
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (weight : Fin (E.maps.N n) → ℝ) :
    (∫ ω, (finiteWeightedScore weight
      (centeredFiniteError
        (regionalRandomValues μ E.maps E.error n)
        (regionalConditionalMean E.maps P E.error n)) ω) ^ 2 ∂P) =
      quadraticForm (trueCovariance E n) weight := by
  let centered := centeredFiniteError
    (regionalRandomValues μ E.maps E.error n)
    (regionalConditionalMean E.maps P E.error n)
  have hmem : ∀ i, MemLp (centered i) 2 P := by
    intro i
    exact centered_regional_error_memLp_two E cov n i
  have hzero : ∀ i, P[centered i] = 0 := by
    intro i
    exact centered_regional_error_integral_eq_zero E n i
  have hzero_again : ∀ i, P[centeredFiniteError centered (0 : Fin (E.maps.N n) → ℝ) i] = 0 := by
    intro i
    simpa [centeredFiniteError] using hzero i
  have hscore := finiteWeightedError_sq_integral_eq_bias_sq_add_quadraticForm
    (μ := P) weight centered (0 : Fin (E.maps.N n) → ℝ) hmem hzero_again
  have hcentered_again :
      centeredFiniteError centered (0 : Fin (E.maps.N n) → ℝ) = centered := by
    funext i ω
    simp [centeredFiniteError]
  change (∫ ω, (finiteWeightedScore weight centered ω) ^ 2 ∂P) = _
  calc
    (∫ ω, (finiteWeightedScore weight centered ω) ^ 2 ∂P) =
        (weight ⬝ᵥ (0 : Fin (E.maps.N n) → ℝ)) ^ 2 +
          quadraticForm
            (finiteErrorCovariance
              (centeredFiniteError centered (0 : Fin (E.maps.N n) → ℝ)) P) weight := hscore
    _ = quadraticForm (finiteErrorCovariance centered P) weight := by
      rw [hcentered_again]
      simp
    _ = quadraticForm (trueCovariance E n) weight := by
      rw [centered_regional_error_covariance_eq_true E n]

/-- Exact outcome-L2 energy of a weighted regional-cell test.  This is the
source bridge from the spatial centered-test map to the true finite
covariance quadratic form in the lower sandwich. -/
theorem weightedRegionalCellTest_centeredIntegral_norm_sq_eq_trueQuadratic
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (weight : Fin (E.maps.N n) → ℝ) :
    ‖centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight)‖ ^ 2 =
      quadraticForm (trueCovariance E n) weight := by
  calc
    ‖centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight)‖ ^ 2 =
        inner ℝ (centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight))
          (centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight)) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ ω, inner ℝ
        (centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight) ω)
        (centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight) ω) ∂P :=
      L2.inner_def _ _
    _ = ∫ ω, (finiteWeightedScore weight
        (centeredFiniteError
          (regionalRandomValues μ E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n)) ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [
        centeredTestIntegralL2_coeFn_ae E cov (weightedRegionalCellTest E n weight),
        centeredTestIntegral_weighted_ae_eq_score E n weight] with ω hL2 hscore
      rw [hL2]
      change inner ℝ
        (centeredIntegralProcess μ P E.error (weightedRegionalCellTest E n weight) ω)
        (centeredIntegralProcess μ P E.error (weightedRegionalCellTest E n weight) ω) = _
      rw [hscore]
      rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = quadraticForm (trueCovariance E n) weight :=
      weighted_centered_regional_score_sq_integral_eq_trueQuadratic E cov n weight

/-- The L2 quotient class of the exact weighted regional-cell test. -/
@[expose] noncomputable def weightedRegionalCellTestLp
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (weight : Fin (E.maps.N n) → ℝ) : Lp ℝ 2 μ :=
  (weightedRegionalCellTest E n weight).2.toLp (weightedRegionalCellTest E n weight).1

omit [IsProbabilityMeasure P] in
private theorem weightedRegionalCellTestLp_coeFn_ae
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (weight : Fin (E.maps.N n) → ℝ) :
    (weightedRegionalCellTestLp E n weight : Point D → ℝ) =ᵐ[μ]
      (weightedRegionalCellTest E n weight).1 := by
  exact MemLp.coeFn_toLp (weightedRegionalCellTest E n weight).2

omit [IsProbabilityMeasure P] in
/-- The finite regional test used in the covariance bound is precisely the
Lp class of the L-026 regional projection. -/
theorem weightedRegionalCellTestLp_eq_regionalProjectionLp
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ)
    (hf : MemLp f 2 μ) (n : ℕ) :
    weightedRegionalCellTestLp E n (regionalProjectionWeights E f n) =
      regionalProjectionLp E f hf n := by
  apply Lp.ext
  refine (weightedRegionalCellTestLp_coeFn_ae E n
    (regionalProjectionWeights E f n)).trans ?_
  have hpoint : (weightedRegionalCellTest E n
      (regionalProjectionWeights E f n)).1 =ᵐ[μ]
      InfillGLSLean.ManuscriptSpecification.L026.regionalProjection
        (E.maps.partition n) f :=
    Filter.Eventually.of_forall fun s => congrFun
      (weightedRegionalCellTest_eq_regionalProjection E f n) s
  exact hpoint.trans (by
    simpa [regionalProjectionLp] using
      (MemLp.coeFn_toLp
        (InfillGLSLean.ManuscriptSpecification.L026.memLp_regionalProjection
          (E.maps.partition n) hf)).symm)

/-- L-026's regional-averaging result expressed directly in the spatial
`Lp` quotient. -/
theorem regionalProjectionLp_sub_tendsto_zero
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ)
    (hf : MemLp f 2 μ) :
    Tendsto (fun n => regionalProjectionLp E f hf n - hf.toLp f)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hL026 :=
    InfillGLSLean.ManuscriptSpecification.L026.regionalAveraging_tendsto_L2
      E f hf
  convert hL026 using 1
  funext n
  let hprojection : MemLp
      (InfillGLSLean.ManuscriptSpecification.L026.regionalProjection
        (E.maps.partition n) f) 2 μ :=
    InfillGLSLean.ManuscriptSpecification.L026.memLp_regionalProjection
      (E.maps.partition n) hf
  change ‖hprojection.toLp _ - hf.toLp f‖ = _
  rw [← hprojection.toLp_sub hf]
  exact Lp.norm_toLp _ _

omit [IsProbabilityMeasure P] in
/-- The Lp version of the weighted regional test has the same centered
outcome integral as its literal test-function representative. -/
theorem centeredTestIntegralLp_weightedRegionalCellTestLp
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (weight : Fin (E.maps.N n) → ℝ) :
    centeredTestIntegralLp E cov (weightedRegionalCellTestLp E n weight) =
      centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight) := by
  unfold centeredTestIntegralLp
  apply centeredTestIntegralL2_congr
  simpa [l2TestOfLp] using weightedRegionalCellTestLp_coeFn_ae E n weight

/-- The exact regional tests used in the finite covariance bound converge to
any fixed spatial L2 test, using L-026 with their source-faithful weights. -/
theorem weightedRegionalCellTestLp_sub_tendsto_zero
    (E : FixedConditionalExperiment μ P) (f : Point D → ℝ)
    (hf : MemLp f 2 μ) :
    Tendsto (fun n =>
      weightedRegionalCellTestLp E n (regionalProjectionWeights E f n) - hf.toLp f)
      atTop (nhds 0) := by
  convert regionalProjectionLp_sub_tendsto_zero E f hf using 1
  funext n
  rw [weightedRegionalCellTestLp_eq_regionalProjectionLp E f hf n]

private theorem integral_spatialMeanOffset_mul_regionalCellAverageTest
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ)
    (n : ℕ) (i : Fin (E.maps.N n)) :
    (∫ s, spatialMeanOffset E c s * (regionalCellAverageTest E n i).1 s ∂μ) =
      regionalValues μ E.maps (spatialMeanOffset E c) n i := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  let a : ℝ := (μ.real R)⁻¹
  have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
  have hf : Integrable (spatialMeanOffset E c) (μ.restrict R) :=
    (spatialMeanOffset_integrable E c).restrict
  change (∫ s, spatialMeanOffset E c s * R.indicator (fun _ => a) s ∂μ) =
    cellMean μ R (spatialMeanOffset E c)
  have hmul : (fun s => spatialMeanOffset E c s * R.indicator (fun _ => a) s) =
      R.indicator (fun s => spatialMeanOffset E c s * a) := by
    funext s
    by_cases hs : s ∈ R <;> simp [hs]
  rw [hmul, integral_indicator hR, integral_mul_const]
  simp [cellMean, setAverage_eq, R, a, smul_eq_mul, mul_comm]

/-- Pairing the fixed spatial mean residual with a weighted regional-cell
test is exactly the finite score of its source `meanOffset` vector. -/
theorem spatialMeanOffsetFunctional_weightedRegionalCellTest
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ)
    (n : ℕ) (weight : Fin (E.maps.N n) → ℝ) :
    spatialMeanOffsetFunctional E c (weightedRegionalCellTestLp E n weight) =
      meanOffset E c n ⬝ᵥ weight := by
  rw [spatialMeanOffsetFunctional_apply]
  have hcoe := weightedRegionalCellTestLp_coeFn_ae E n weight
  calc
    (∫ s, spatialMeanOffset E c s * weightedRegionalCellTestLp E n weight s ∂μ) =
        ∫ s, spatialMeanOffset E c s * (weightedRegionalCellTest E n weight).1 s ∂μ := by
      apply integral_congr_ae
      filter_upwards [hcoe] with s hs
      rw [hs]
    _ = ∑ i, weight i *
        (∫ s, spatialMeanOffset E c s * (regionalCellAverageTest E n i).1 s ∂μ) := by
      rw [weightedRegionalCellTest]
      have hsum : (fun s => spatialMeanOffset E c s *
          (∑ i, weight i * (regionalCellAverageTest E n i).1 s)) =
          fun s => ∑ i, weight i *
            (spatialMeanOffset E c s * (regionalCellAverageTest E n i).1 s) := by
        funext s
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum, integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_const_mul]
      · intro i hi
        exact ((spatialMeanOffset_memLp_two E c).integrable_mul
          (regionalCellAverageTest E n i).2).const_mul (weight i)
    _ = ∑ i, weight i * regionalValues μ E.maps (spatialMeanOffset E c) n i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_spatialMeanOffset_mul_regionalCellAverageTest E c n i]
    _ = meanOffset E c n ⬝ᵥ weight := by
      simp only [dotProduct]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← meanOffset_apply_eq_regionalValues_spatialMeanOffset E c n i]
      ring

/-- The paper's bounded inverse-working-covariance mean energy and lower
covariance sandwich give one eventual, uniform squared bound on every exact
weighted regional-cell test.  This is still a finite-resolution statement;
the L-026 regional-averaging limit is applied separately below. -/
theorem exists_eventually_weightedRegionalCellTest_sq_bound
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∀ weight : Fin (E.maps.N n) → ℝ,
      (spatialMeanOffsetFunctional E mean.c (weightedRegionalCellTestLp E n weight)) ^ 2 ≤
        (2 * M / cov.sigmaSquared) *
          ‖centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight)‖ ^ 2 := by
  obtain ⟨M, hM_nonneg, hM⟩ := exists_nonnegative_meanEnergy_upper_bound E mean
  refine ⟨M, hM_nonneg, ?_⟩
  filter_upwards [eventually_ge_atTop cov.start] with n hn
  intro weight
  obtain ⟨hdelta_nonneg, hdelta_lt_one, hlower, _hupper⟩ := cov.sandwich n hn
  have henergy_nonneg : 0 ≤ meanEnergy E mean.c n := by
    change 0 ≤ quadraticForm (E.kernel n)⁻¹ (meanOffset E mean.c n)
    exact InfillGLSLean.quadraticForm_nonneg
      ((E.kernel_posDef n).inv.posSemidef) _
  have hfinite := meanOffset_score_sq_le_energy_trueQuadratic_of_lowerSandwich
    E mean.c n cov.sigmaSquared (cov.delta n) hdelta_nonneg cov.sigmaSquared_pos
    hlower weight
  have hnorm := weightedRegionalCellTest_centeredIntegral_norm_sq_eq_trueQuadratic
    E cov n weight
  have htrue_nonneg : 0 ≤ quadraticForm (trueCovariance E n) weight := by
    rw [← hnorm]
    positivity
  have hcoeff_nonneg : 0 ≤ (1 + cov.delta n) / cov.sigmaSquared :=
    div_nonneg (by linarith) cov.sigmaSquared_pos.le
  have hcoeff_le : (1 + cov.delta n) / cov.sigmaSquared ≤ 2 / cov.sigmaSquared := by
    have hinv_nonneg : 0 ≤ cov.sigmaSquared⁻¹ :=
      inv_nonneg.mpr cov.sigmaSquared_pos.le
    calc
      (1 + cov.delta n) / cov.sigmaSquared =
          (1 + cov.delta n) * cov.sigmaSquared⁻¹ := by ring
      _ ≤ 2 * cov.sigmaSquared⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hinv_nonneg
      _ = 2 / cov.sigmaSquared := by ring
  have hscalar : meanEnergy E mean.c n * ((1 + cov.delta n) / cov.sigmaSquared) ≤
      M * (2 / cov.sigmaSquared) := by
    calc
      meanEnergy E mean.c n * ((1 + cov.delta n) / cov.sigmaSquared) ≤
          M * ((1 + cov.delta n) / cov.sigmaSquared) :=
        mul_le_mul_of_nonneg_right (hM n) hcoeff_nonneg
      _ ≤ M * (2 / cov.sigmaSquared) :=
        mul_le_mul_of_nonneg_left hcoeff_le hM_nonneg
  rw [spatialMeanOffsetFunctional_weightedRegionalCellTest]
  calc
    (meanOffset E mean.c n ⬝ᵥ weight) ^ 2 ≤
        meanEnergy E mean.c n * ((1 + cov.delta n) / cov.sigmaSquared) *
          quadraticForm (trueCovariance E n) weight := hfinite
    _ ≤ (M * (2 / cov.sigmaSquared)) * quadraticForm (trueCovariance E n) weight :=
      mul_le_mul_of_nonneg_right hscalar htrue_nonneg
    _ = (2 * M / cov.sigmaSquared) *
          ‖centeredTestIntegralL2 E cov (weightedRegionalCellTest E n weight)‖ ^ 2 := by
      rw [hnorm]
      ring

/-- The finite-energy covariance bound written for the literal L-026
regional projections.  This is only a change of representation: the weights
are exactly the regional cell masses times their cell averages. -/
theorem exists_eventually_regionalProjectionLp_sq_bound
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) (f : Point D → ℝ) (hf : MemLp f 2 μ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop,
      (spatialMeanOffsetFunctional E mean.c (regionalProjectionLp E f hf n)) ^ 2 ≤
        (2 * M / cov.sigmaSquared) *
          ‖centeredTestIntegralLp E cov (regionalProjectionLp E f hf n)‖ ^ 2 := by
  obtain ⟨M, hM_nonneg, hfinite⟩ :=
    exists_eventually_weightedRegionalCellTest_sq_bound E cov mean
  refine ⟨M, hM_nonneg, ?_⟩
  filter_upwards [hfinite] with n hn
  have htest := weightedRegionalCellTestLp_eq_regionalProjectionLp E f hf n
  calc
    (spatialMeanOffsetFunctional E mean.c (regionalProjectionLp E f hf n)) ^ 2 =
        (spatialMeanOffsetFunctional E mean.c
          (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n))) ^ 2 := by
      rw [htest]
    _ ≤ (2 * M / cov.sigmaSquared) *
          ‖centeredTestIntegralL2 E cov
            (weightedRegionalCellTest E n (regionalProjectionWeights E f n))‖ ^ 2 :=
      hn (regionalProjectionWeights E f n)
    _ = (2 * M / cov.sigmaSquared) *
          ‖centeredTestIntegralLp E cov
            (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n))‖ ^ 2 := by
      rw [centeredTestIntegralLp_weightedRegionalCellTestLp]
    _ = (2 * M / cov.sigmaSquared) *
          ‖centeredTestIntegralLp E cov (regionalProjectionLp E f hf n)‖ ^ 2 := by
      rw [htest]

/-- The spatial mean-residual pairing as its canonical continuous linear
functional on spatial L2. -/
noncomputable def spatialMeanOffsetContinuousLinearMap
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) :
    Lp ℝ 2 μ →L[ℝ] ℝ :=
  innerSL ℝ (spatialMeanOffsetL2 E c)

/- This continuous functional is definitionally the source's spatial
mean-offset functional.  It is private because it unfolds local packaging
definitions; the public convergence theorem below is the usable interface. -/
private theorem spatialMeanOffsetContinuousLinearMap_apply
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ) (h : Lp ℝ 2 μ) :
    spatialMeanOffsetContinuousLinearMap E c h = spatialMeanOffsetFunctional E c h := rfl

/-- The exact regional L2 tests remain convergent after centered spatial
integration into outcome L2. -/
theorem centeredTestIntegralLp_weightedRegionalCellTestLp_sub_tendsto_zero
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (f : Point D → ℝ) (hf : MemLp f 2 μ) :
    Tendsto (fun n =>
      centeredTestIntegralLp E cov
        (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n)) -
      centeredTestIntegralLp E cov (hf.toLp f)) atTop (nhds 0) := by
  have htests := weightedRegionalCellTestLp_sub_tendsto_zero E f hf
  have hmap : Tendsto (fun n => centeredTestIntegralContinuousLinearMap E
      (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n) - hf.toLp f))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, ContinuousLinearMap.map_zero] using
      ((centeredTestIntegralContinuousLinearMap E).continuous.tendsto 0).comp htests
  apply hmap.congr'
  filter_upwards [] with n
  rw [ContinuousLinearMap.map_sub]
  rw [centeredTestIntegralContinuousLinearMap_apply,
    centeredTestIntegralContinuousLinearMap_apply]

/-- The source spatial mean functional is continuous along the exact regional
L2 tests. -/
theorem spatialMeanOffsetFunctional_weightedRegionalCellTestLp_sub_tendsto_zero
    (E : FixedConditionalExperiment μ P) (c : Fin E.q → ℝ)
    (f : Point D → ℝ) (hf : MemLp f 2 μ) :
    Tendsto (fun n =>
      spatialMeanOffsetFunctional E c
        (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n)) -
      spatialMeanOffsetFunctional E c (hf.toLp f)) atTop (nhds 0) := by
  have htests := weightedRegionalCellTestLp_sub_tendsto_zero E f hf
  have hmap : Tendsto (fun n => spatialMeanOffsetContinuousLinearMap E c
      (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n) - hf.toLp f))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, ContinuousLinearMap.map_zero] using
      ((spatialMeanOffsetContinuousLinearMap E c).continuous.tendsto 0).comp htests
  apply hmap.congr'
  filter_upwards [] with n
  rw [ContinuousLinearMap.map_sub]
  rw [spatialMeanOffsetContinuousLinearMap_apply,
    spatialMeanOffsetContinuousLinearMap_apply]

/-- The source's bounded inverse-covariance mean energy, covariance sandwich,
and L-026 regional approximation jointly give one uniform squared bound for
the spatial mean functional on every spatial L2 test.  The constant is fixed
before the test is chosen. -/
theorem exists_uniform_spatialMeanOffsetFunctional_sq_bound
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : Lp ℝ 2 μ,
      (spatialMeanOffsetFunctional E mean.c h) ^ 2 ≤
        (2 * M / cov.sigmaSquared) * ‖centeredTestIntegralLp E cov h‖ ^ 2 := by
  obtain ⟨M, hM_nonneg, hfinite_weights⟩ :=
    exists_eventually_weightedRegionalCellTest_sq_bound E cov mean
  refine ⟨M, hM_nonneg, ?_⟩
  intro h
  let f : Point D → ℝ := fun s => h s
  have hf : MemLp f 2 μ := by
    simpa [f] using Lp.memLp h
  have htoLp : hf.toLp f = h := by
    simp [f]
  have hfinite : ∀ᶠ n in atTop,
      (spatialMeanOffsetFunctional E mean.c
        (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n))) ^ 2 ≤
        (2 * M / cov.sigmaSquared) *
          ‖centeredTestIntegralLp E cov
            (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n))‖ ^ 2 := by
    filter_upwards [hfinite_weights] with n hn
    calc
      (spatialMeanOffsetFunctional E mean.c
          (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n))) ^ 2 ≤
          (2 * M / cov.sigmaSquared) *
            ‖centeredTestIntegralL2 E cov
              (weightedRegionalCellTest E n (regionalProjectionWeights E f n))‖ ^ 2 :=
        hn (regionalProjectionWeights E f n)
      _ = (2 * M / cov.sigmaSquared) *
            ‖centeredTestIntegralLp E cov
              (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n))‖ ^ 2 := by
        rw [centeredTestIntegralLp_weightedRegionalCellTestLp]
  have hFdiff :=
    spatialMeanOffsetFunctional_weightedRegionalCellTestLp_sub_tendsto_zero
      E mean.c f hf
  have hF : Tendsto (fun n => spatialMeanOffsetFunctional E mean.c
      (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n)))
      atTop (nhds (spatialMeanOffsetFunctional E mean.c h)) := by
    rw [tendsto_sub_nhds_zero_iff] at hFdiff
    rw [htoLp] at hFdiff
    exact hFdiff
  have hAdiff :=
    centeredTestIntegralLp_weightedRegionalCellTestLp_sub_tendsto_zero E cov f hf
  have hA : Tendsto (fun n => centeredTestIntegralLp E cov
      (weightedRegionalCellTestLp E n (regionalProjectionWeights E f n)))
      atTop (nhds (centeredTestIntegralLp E cov h)) := by
    rw [tendsto_sub_nhds_zero_iff] at hAdiff
    rw [htoLp] at hAdiff
    exact hAdiff
  exact le_of_tendsto_of_tendsto (hF.pow 2)
    ((hA.norm.pow 2).const_mul (2 * M / cov.sigmaSquared)) hfinite

/-- Square-root form of the uniform spatial-functional bound, before the
centered integral is corestricted to its closed covariance Hilbert space. -/
theorem exists_uniform_spatialMeanOffsetFunctional_bound_lp
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ C : ℝ, ∀ h : Lp ℝ 2 μ,
      ‖spatialMeanOffsetFunctional E mean.c h‖ ≤
        C * ‖centeredTestIntegralLp E cov h‖ := by
  obtain ⟨M, hM_nonneg, hsq⟩ :=
    exists_uniform_spatialMeanOffsetFunctional_sq_bound E cov mean
  let K : ℝ := 2 * M / cov.sigmaSquared
  have hK_nonneg : 0 ≤ K := by
    exact div_nonneg (mul_nonneg (by norm_num) hM_nonneg) cov.sigmaSquared_pos.le
  refine ⟨Real.sqrt K, ?_⟩
  intro h
  have hright_nonneg : 0 ≤ Real.sqrt K * ‖centeredTestIntegralLp E cov h‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp
  calc
    ‖spatialMeanOffsetFunctional E mean.c h‖ ^ 2 =
        (spatialMeanOffsetFunctional E mean.c h) ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    _ ≤ K * ‖centeredTestIntegralLp E cov h‖ ^ 2 := by
      simpa [K] using hsq h
    _ = (Real.sqrt K * ‖centeredTestIntegralLp E cov h‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK_nonneg]

/-- Addition for the source map from spatial L2 classes to outcome L2
classes. -/
theorem centeredTestIntegralLp_add
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h g : Lp ℝ 2 μ) :
    centeredTestIntegralLp E cov (h + g) =
      centeredTestIntegralLp E cov h + centeredTestIntegralLp E cov g := by
  let hsum : L2TestFunction μ :=
    ⟨(h : Point D → ℝ) + (g : Point D → ℝ), (Lp.memLp h).add (Lp.memLp g)⟩
  change centeredTestIntegralL2 E cov (l2TestOfLp (h + g)) =
    centeredTestIntegralL2 E cov (l2TestOfLp h) +
      centeredTestIntegralL2 E cov (l2TestOfLp g)
  calc
    centeredTestIntegralL2 E cov (l2TestOfLp (h + g)) =
        centeredTestIntegralL2 E cov hsum := by
      apply centeredTestIntegralL2_congr
      simpa [l2TestOfLp, hsum] using (Lp.coeFn_add h g)
    _ = centeredTestIntegralL2 E cov (l2TestOfLp h) +
        centeredTestIntegralL2 E cov (l2TestOfLp g) :=
      centeredTestIntegralL2_add E cov (l2TestOfLp h) (l2TestOfLp g)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Scalar multiplication for the source map from spatial L2 classes to
 outcome L2 classes. -/
theorem centeredTestIntegralLp_smul
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (a : ℝ) (h : Lp ℝ 2 μ) :
    centeredTestIntegralLp E cov (a • h) = a • centeredTestIntegralLp E cov h := by
  let ha : L2TestFunction μ :=
    ⟨a • (h : Point D → ℝ), (Lp.memLp h).const_smul a⟩
  change centeredTestIntegralL2 E cov (l2TestOfLp (a • h)) =
    a • centeredTestIntegralL2 E cov (l2TestOfLp h)
  calc
    centeredTestIntegralL2 E cov (l2TestOfLp (a • h)) =
        centeredTestIntegralL2 E cov ha := by
      apply centeredTestIntegralL2_congr
      simpa [l2TestOfLp, ha] using (Lp.coeFn_smul a h)
    _ = a • centeredTestIntegralL2 E cov (l2TestOfLp h) :=
      centeredTestIntegralL2_smul E cov a (l2TestOfLp h)

/-- The paper's centered spatial-integration map, now packaged as a genuine
linear map between the two L2 spaces.  Its continuity bound is a later
consequence of the product-L2 estimate, not an added hypothesis. -/
@[expose] noncomputable def centeredTestIntegralLinearMap
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 P where
  toFun := centeredTestIntegralLp E cov
  map_add' := centeredTestIntegralLp_add E cov
  map_smul' := centeredTestIntegralLp_smul E cov

/-- The paper's covariance Hilbert space: the closed linear span, in the
outcome L2 space, of all centered spatial L2 averages of the one fixed error
field.  This is a direct source-faithful definition, not a new assumption. -/
noncomputable def covarianceHilbertSpace
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E) :
    Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (Set.range (centeredTestIntegralLp E cov))).topologicalClosure

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Every centered spatial L2 average belongs to the covariance Hilbert
space by construction. -/
theorem centeredTestIntegralLp_mem_covarianceHilbertSpace
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : Lp ℝ 2 μ) :
    centeredTestIntegralLp E cov h ∈ covarianceHilbertSpace E cov := by
  exact (Submodule.le_topologicalClosure _)
    (Submodule.subset_span ⟨h, rfl⟩)

/-- The centered spatial-average map, corestricted to exactly the closed
covariance Hilbert space used in the paper. -/
@[expose] noncomputable def centeredTestIntegralToCovarianceHilbertSpace
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E) :
    Lp ℝ 2 μ →ₗ[ℝ] covarianceHilbertSpace E cov :=
  (centeredTestIntegralLinearMap E cov).codRestrict
    (covarianceHilbertSpace E cov)
    (centeredTestIntegralLp_mem_covarianceHilbertSpace E cov)

/-- The corestriction has the literal centered spatial average as its ambient
value.  This public bridge exposes no new analytic content; it makes the
source-level definition available to downstream covariance-Hilbert arguments
without unfolding an opaque imported definition. -/
theorem centeredTestIntegralToCovarianceHilbertSpace_apply_coe
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : Lp ℝ 2 μ) :
    ((centeredTestIntegralToCovarianceHilbertSpace E cov h :
      covarianceHilbertSpace E cov) : Lp ℝ 2 P) =
      centeredTestIntegralLp E cov h := rfl

private theorem centeredTestIntegralLinearMap_range_eq_span
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E) :
    LinearMap.range (centeredTestIntegralLinearMap E cov) =
      Submodule.span ℝ (Set.range (centeredTestIntegralLp E cov)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact Submodule.subset_span ⟨x, rfl⟩
  · apply Submodule.span_le.2
    rintro y ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- The corestricted centered-average map has dense range in the covariance
Hilbert space by the paper's literal closed-span definition. -/
theorem denseRange_centeredTestIntegralToCovarianceHilbertSpace
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E) :
    DenseRange (centeredTestIntegralToCovarianceHilbertSpace E cov) := by
  rw [DenseRange, Subtype.dense_iff]
  intro y hy
  change y ∈ closure ((↑) '' Set.range (centeredTestIntegralToCovarianceHilbertSpace E cov))
  have himage : ((↑) '' Set.range (centeredTestIntegralToCovarianceHilbertSpace E cov)) =
      (LinearMap.range (centeredTestIntegralLinearMap E cov) : Set (Lp ℝ 2 P)) := by
    ext z
    constructor
    · rintro ⟨w, ⟨x, hx⟩, rfl⟩
      exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨centeredTestIntegralToCovarianceHilbertSpace E cov x, ⟨x, rfl⟩, rfl⟩
  rw [himage, centeredTestIntegralLinearMap_range_eq_span E cov]
  simpa [covarianceHilbertSpace] using hy

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The covariance Hilbert space is complete because it is the closed
submodule generated by the source's centered spatial averages. -/
theorem covarianceHilbertSpace_complete
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E) :
    CompleteSpace (covarianceHilbertSpace E cov) := by
  change CompleteSpace
    ((Submodule.span ℝ (Set.range (centeredTestIntegralLp E cov))).topologicalClosure)
  infer_instance

/-- The uniform source bound in the exact corestricted covariance-Hilbert
norm needed by the Riesz step.  It is derived from, rather than added to,
the fixed-mean and covariance assumptions. -/
theorem exists_uniform_spatialMeanOffsetFunctional_bound
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ C : ℝ, ∀ h : Lp ℝ 2 μ,
      ‖spatialMeanOffsetFunctional E mean.c h‖ ≤
        C * ‖centeredTestIntegralToCovarianceHilbertSpace E cov h‖ := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_spatialMeanOffsetFunctional_bound_lp E cov mean
  refine ⟨C, ?_⟩
  intro h
  change ‖spatialMeanOffsetFunctional E mean.c h‖ ≤
    C * ‖centeredTestIntegralLp E cov h‖
  exact hC h

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Source-specialized Fréchet--Riesz step: once the paper's finite-energy
argument has supplied a bounded functional on the covariance Hilbert space,
one fixed representer follows with no supplementary covariance assumption. -/
theorem exists_covarianceHilbertSpace_rieszRepresenter_of_linear_bound
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (L : covarianceHilbertSpace E cov →ₗ[ℝ] ℝ) (C : ℝ)
    (hL : ∀ h : covarianceHilbertSpace E cov, ‖L h‖ ≤ C * ‖h‖) :
    ∃ V : covarianceHilbertSpace E cov,
      ∀ h : covarianceHilbertSpace E cov, L h = inner ℝ V h := by
  let _ : CompleteSpace (covarianceHilbertSpace E cov) :=
    covarianceHilbertSpace_complete E cov
  exact exists_rieszRepresenter_of_linear_bound L C hL

/-- Source-specialized endpoint of the paper's covariance-Hilbert/Riesz
argument.  Once the finite regional-energy calculation has supplied the
displayed spatial-test bound, the existing assumptions force one fixed
covariance-Hilbert element whose covariance pairing is exactly the fixed
spatial residual in L2.  The premise is stated explicitly so this theorem
does not silently strengthen `FixedMeanAssumption`. -/
theorem exists_covarianceHilbert_spatial_representer_of_spatial_bound
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (c : Fin E.q → ℝ)
    (hbound : ∃ C : ℝ, ∀ h : Lp ℝ 2 μ,
      ‖spatialMeanOffsetFunctional E c h‖ ≤
        C * ‖centeredTestIntegralToCovarianceHilbertSpace E cov h‖) :
    ∃ V : covarianceHilbertSpace E cov,
      centeredErrorPairingL2 E (V : Lp ℝ 2 P) = spatialMeanOffsetL2 E c := by
  let _ : CompleteSpace (covarianceHilbertSpace E cov) :=
    covarianceHilbertSpace_complete E cov
  obtain ⟨V, hV⟩ := exists_rieszRepresenter_of_linear_bound_along_dense
    (X := Lp ℝ 2 μ) (H := covarianceHilbertSpace E cov)
    (centeredTestIntegralToCovarianceHilbertSpace E cov)
    (spatialMeanOffsetFunctional E c)
    (denseRange_centeredTestIntegralToCovarianceHilbertSpace E cov) hbound
  refine ⟨V, ?_⟩
  apply ext_inner_right ℝ
  intro h
  calc
    inner ℝ (centeredErrorPairingL2 E (V : Lp ℝ 2 P)) h =
        inner ℝ (V : Lp ℝ 2 P) (centeredTestIntegralLp E cov h) :=
      inner_centeredErrorPairingL2_eq_inner_centeredTestIntegralLp E cov h (V : Lp ℝ 2 P)
    _ = inner ℝ V (centeredTestIntegralToCovarianceHilbertSpace E cov h) := by
      rfl
    _ = spatialMeanOffsetFunctional E c h := (hV h).symm
    _ = inner ℝ (spatialMeanOffsetL2 E c) h := by
      rfl

/-- The fixed covariance-Hilbert representer for the paper's fixed mean
residual.  This is the existing Riesz endpoint instantiated with the uniform
bound proved above from the stated source assumptions. -/
theorem exists_covarianceHilbert_spatial_representer_of_fixedMeanAssumption
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ V : covarianceHilbertSpace E cov,
      centeredErrorPairingL2 E (V : Lp ℝ 2 P) = spatialMeanOffsetL2 E mean.c := by
  exact exists_covarianceHilbert_spatial_representer_of_spatial_bound E cov mean.c
    (exists_uniform_spatialMeanOffsetFunctional_bound E cov mean)

end SourceMeanOffset

section DenseWeakTest

variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- A uniformly bounded sequence of Hilbert-space elements converges weakly to
zero once its inner products converge to zero on a dense submodule. This is
the exact density extension used in the paper after regional spatial averages
have been shown dense in the covariance Hilbert space; it introduces neither
nested partitions nor a rate condition. -/
theorem inner_tendsto_zero_of_dense_submodule
    (z : ℕ → G) (M : Submodule ℝ G) (hM : Dense (M : Set G))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖z n‖ ≤ C)
    (htest : ∀ w : M,
      Tendsto (fun n => inner ℝ (z n) (w : G)) atTop (nhds 0))
    (v : G) :
    Tendsto (fun n => inner ℝ (z n) v) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdenom_pos : 0 < 2 * (C + 1) := by linarith
  have hdelta_pos : 0 < ε / (2 * (C + 1)) := div_pos hε hdenom_pos
  obtain ⟨w, hwM, hwclose⟩ := hM.exists_dist_lt v hdelta_pos
  let wM : M := ⟨w, hwM⟩
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp (htest wM)) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have htest_n : ‖inner ℝ (z n) w‖ < ε / 2 := by
    simpa [wM, dist_eq_norm] using hN n hn
  have hw_norm : ‖v - w‖ < ε / (2 * (C + 1)) := by
    simpa [dist_eq_norm] using hwclose
  have hfirst : ‖inner ℝ (z n) (v - w)‖ < ε / 2 := by
    by_cases hC_zero : C = 0
    · rw [hC_zero] at hbound
      have hz_zero : z n = 0 :=
        norm_eq_zero.mp (le_antisymm (hbound n) (norm_nonneg _))
      simp [hz_zero, hε]
    · have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC_zero)
      have hscale : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
        calc
          C * (ε / (2 * (C + 1))) ≤
              (C + 1) * (ε / (2 * (C + 1))) := by
            exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdelta_pos)
          _ = ε / 2 := by field_simp
      calc
        ‖inner ℝ (z n) (v - w)‖ ≤ ‖z n‖ * ‖v - w‖ := norm_inner_le_norm _ _
        _ ≤ C * ‖v - w‖ :=
          mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
        _ < C * (ε / (2 * (C + 1))) :=
          mul_lt_mul_of_pos_left hw_norm hC_pos
        _ ≤ ε / 2 := hscale
  have hinner : ‖inner ℝ (z n) v‖ < ε := by
    calc
      ‖inner ℝ (z n) v‖ =
          ‖inner ℝ (z n) (v - w) + inner ℝ (z n) w‖ := by
        rw [inner_sub_right]
        ring_nf
      _ ≤ ‖inner ℝ (z n) (v - w)‖ + ‖inner ℝ (z n) w‖ := norm_add_le _ _
      _ < ε := by linarith
  simpa [dist_eq_norm] using hinner

/-- Set-indexed form of `inner_tendsto_zero_of_dense_submodule`. The paper's
regional averages first give convergence on a family of test averages; this
lemma performs the finite-linear-combination step before density is used. -/
theorem inner_tendsto_zero_of_dense_span
    (z : ℕ → G) (S : Set G) (hS : Dense (Submodule.span ℝ S : Set G))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖z n‖ ≤ C)
    (htest : ∀ w ∈ S,
      Tendsto (fun n => inner ℝ (z n) w) atTop (nhds 0))
    (v : G) :
    Tendsto (fun n => inner ℝ (z n) v) atTop (nhds 0) := by
  apply inner_tendsto_zero_of_dense_submodule z (Submodule.span ℝ S) hS C hC hbound
  intro w
  have hspan : ∀ x : G, x ∈ Submodule.span ℝ S →
      Tendsto (fun n => inner ℝ (z n) x) atTop (nhds 0) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => simpa using htest x hx
    | zero => simp
    | add x y hx hy htx hty =>
        simpa [inner_add_right] using htx.add hty
    | smul a x hx htx =>
        simpa [inner_smul_right] using htx.const_mul a
  exact hspan w w.property

end DenseWeakTest

end InfillGLSLean.MeanHilbertRiesz

end
