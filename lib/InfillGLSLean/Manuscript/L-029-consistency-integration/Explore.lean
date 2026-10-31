module

public import ManuscriptSpecification
public import InfillGLSLean
public import «L-027-api-fwl-integration».FWLIntegration
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Convex.Integral

/-!
Direct integration proof for the literal source-facing consistency proposition.
The module packaging/public-import boundary is visibility-only: existing
theorem statements and proof bodies are unchanged, and it permits L-034 to
consume the two already-proved exact translation APIs.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L029

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

universe v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

private theorem regional_error_memLp_two
    (E : FixedConditionalExperiment μ P) (n : ℕ) (i : Fin (E.maps.N n)) :
    MemLp (regionalRandomValues μ E.maps E.error n i) 2 P := by
  let R : Set (Point D) := (E.maps.partition n).cell i
  have hsq_measurable : Measurable
      (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) :=
    E.error_jointly_measurable.pow measurable_const
  have hsq_lintegral :
      (∫⁻ z : Ω × Point D, ENNReal.ofReal (E.error z.1 z.2 ^ 2) ∂(P.prod μ)) < ∞ := by
    have hsq_ennreal_measurable : Measurable
        (fun z : Ω × Point D => ENNReal.ofReal (E.error z.1 z.2 ^ 2)) :=
      ENNReal.continuous_ofReal.measurable.comp hsq_measurable
    rw [lintegral_prod _ hsq_ennreal_measurable.aemeasurable]
    exact E.conditional_error_second_moment
  have hsq_integrable : Integrable
      (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) (P.prod μ) :=
    (lintegral_ofReal_ne_top_iff_integrable hsq_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => sq_nonneg (E.error z.1 z.2))).mp
      hsq_lintegral.ne
  have herror_product : Integrable
      (fun z : Ω × Point D => E.error z.1 z.2) (P.prod μ) := by
    have hmemLp : MemLp (fun z : Ω × Point D => E.error z.1 z.2) 2 (P.prod μ) :=
      (memLp_two_iff_integrable_sq E.error_jointly_measurable.aestronglyMeasurable).mpr
        hsq_integrable
    exact hmemLp.integrable (by norm_num)
  have hmeasure : P.prod (μ.restrict R) =
      (P.prod μ).restrict (Set.univ ×ˢ R) := by
    calc
      P.prod (μ.restrict R) = (P.restrict Set.univ).prod (μ.restrict R) := by
        rw [Measure.restrict_univ]
      _ = (P.prod μ).restrict (Set.univ ×ˢ R) := by
        rw [Measure.prod_restrict]
  have hsq_restrict : Integrable
      (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) (P.prod (μ.restrict R)) := by
    rw [hmeasure]
    exact hsq_integrable.restrict
  have herror_restrict : Integrable
      (fun z : Ω × Point D => E.error z.1 z.2) (P.prod (μ.restrict R)) := by
    rw [hmeasure]
    exact herror_product.restrict
  have hvertical_error : ∀ᵐ ω ∂P,
      Integrable (fun s => E.error ω s) (μ.restrict R) :=
    (integrable_prod_iff E.error_jointly_measurable.aestronglyMeasurable).mp
      herror_restrict |>.1
  have hvertical_square : ∀ᵐ ω ∂P,
      Integrable (fun s => E.error ω s ^ 2) (μ.restrict R) :=
    (integrable_prod_iff hsq_measurable.aestronglyMeasurable).mp
      hsq_restrict |>.1
  have haverage_square : Integrable
      (fun ω => ⨍ s in R, E.error ω s ^ 2 ∂μ) P := by
    rw [show (fun ω => ⨍ s in R, E.error ω s ^ 2 ∂μ) =
        fun ω => (μ.real R)⁻¹ • ∫ s, E.error ω s ^ 2 ∂(μ.restrict R) by
          funext ω
          rw [setAverage_eq]]
    exact hsq_restrict.integral_prod_left.const_mul _
  have hregional_ae : AEStronglyMeasurable
      (regionalRandomValues μ E.maps E.error n i) P := by
    change AEStronglyMeasurable (fun ω => ⨍ s in R, E.error ω s ∂μ) P
    rw [show (fun ω => ⨍ s in R, E.error ω s ∂μ) =
        fun ω => (μ.real R)⁻¹ • ∫ s, E.error ω s ∂(μ.restrict R) by
          funext ω
          rw [setAverage_eq]]
    have hinner : AEStronglyMeasurable
        (fun ω : Ω => ∫ s, E.error ω s ∂(μ.restrict R)) P :=
      E.error_jointly_measurable.aestronglyMeasurable.integral_prod_right'
    exact hinner.const_smul ((μ.real R)⁻¹)
  apply (memLp_two_iff_integrable_sq hregional_ae).mpr
  apply Integrable.mono' haverage_square
  · exact hregional_ae.pow 2
  filter_upwards [hvertical_error, hvertical_square] with ω herror hsquare
  have hjensen := (Even.convexOn_pow (by norm_num : Even 2)).map_set_average_le
    (continuous_pow 2).continuousOn isClosed_univ
    (ne_of_gt ((E.maps.partition n).positive_measure i))
    (measure_ne_top μ R) (Filter.Eventually.of_forall fun _ => Set.mem_univ _) herror hsquare
  change ‖(⨍ s in R, E.error ω s ∂μ) ^ 2‖ ≤
    ⨍ s in R, E.error ω s ^ 2 ∂μ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa [Function.comp_def] using hjensen

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
private theorem treatment_memLp_two
    (E : FixedConditionalExperiment μ P) : MemLp E.treatment 2 μ := by
  have hsq_measurable : Measurable (fun s => E.treatment s ^ 2) :=
    E.treatment_measurable.pow measurable_const
  have hpoint : ∀ s : Point D,
      ENNReal.ofReal (E.treatment s ^ 2) ≤
        ENNReal.ofReal (E.treatment s ^ 2 + ∑ j : Fin E.q, E.controls j s ^ 2) := by
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

/-- Centering a finite regional error vector by its coordinatewise mean does
not change its covariance matrix.  This is only a private translation lemma
for the literal `trueCovariance` definition. -/
private theorem centered_regional_error_covariance_eq_true
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    finiteErrorCovariance
      (centeredFiniteError (regionalRandomValues μ E.maps E.error n)
        (regionalConditionalMean E.maps P E.error n)) P =
      trueCovariance E n := by
  ext i j
  simp only [finiteErrorCovariance_apply, trueCovariance]
  change cov[(fun w => regionalRandomValues μ E.maps E.error n i w -
      regionalConditionalMean E.maps P E.error n i),
    (fun w => regionalRandomValues μ E.maps E.error n j w -
      regionalConditionalMean E.maps P E.error n j); P] =
    cov[regionalRandomValues μ E.maps E.error n i,
      regionalRandomValues μ E.maps E.error n j; P]
  rw [covariance_sub_const_left
      ((regional_error_memLp_two E n i).integrable (by norm_num)),
    covariance_sub_const_right
      ((regional_error_memLp_two E n j).integrable (by norm_num))]

/-- Public source-to-finite translation API: the literal source structural
model passes to every regional average.  The integrability facts are derived
from the existing second-moment clauses, not added as hypotheses.  This
visibility change leaves the statement and proof body unchanged. -/
theorem regional_structural_model
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    ∀ᵐ w ∂P, ∀ i,
      regionalRandomValues μ E.maps E.outcome n i w =
        E.beta * regionalValues μ E.maps E.treatment n i +
          dotProduct (fun j => regionalValues μ E.maps (E.controls j) n i) E.gamma +
            regionalRandomValues μ E.maps E.error n i w := by
  have htreatment : Integrable E.treatment μ :=
    (treatment_memLp_two E).integrable (by norm_num)
  have hcontrols : ∀ j, Integrable (E.controls j) μ := by
    intro j
    exact (control_memLp_two E j).integrable (by norm_num)
  have herrors : ∀ᵐ w ∂P, ∀ i,
      IntegrableOn (E.error w) ((E.maps.partition n).cell i) μ :=
    ae_all_iff.2 (fun i => regional_error_integrableOn_ae E n i)
  filter_upwards [E.structural_model, herrors] with w hmodel herrors_w
  intro i
  let R : Set (Point D) := (E.maps.partition n).cell i
  have hR : MeasurableSet R := (E.maps.partition n).measurable_cell i
  have hbeta : IntegrableOn (fun s => E.beta * E.treatment s) R μ :=
    (htreatment.const_mul E.beta).integrableOn
  have hcontrol : ∀ j, IntegrableOn (fun s => E.controls j s * E.gamma j) R μ := by
    intro j
    exact ((hcontrols j).mul_const (E.gamma j)).integrableOn
  have hdot : IntegrableOn
      (fun s => dotProduct (fun j => E.controls j s) E.gamma) R μ := by
    change Integrable (fun s => ∑ j, E.controls j s * E.gamma j) (μ.restrict R)
    exact integrable_finsetSum Finset.univ (fun j _ => hcontrol j)
  have hbeta_average :
      (⨍ s in R, E.beta * E.treatment s ∂μ) =
        E.beta * (⨍ s in R, E.treatment s ∂μ) := by
    rw [setAverage_eq, setAverage_eq, integral_const_mul]
    simp only [smul_eq_mul]
    ring
  have hdot_average :
      (⨍ s in R, dotProduct (fun j => E.controls j s) E.gamma ∂μ) =
        dotProduct (fun j => ⨍ s in R, E.controls j s ∂μ) E.gamma := by
    change (⨍ s in R, ∑ j, E.controls j s * E.gamma j ∂μ) =
      ∑ j, (⨍ s in R, E.controls j s ∂μ) * E.gamma j
    calc
      (⨍ s in R, ∑ j, E.controls j s * E.gamma j ∂μ) =
          ∑ j, ⨍ s in R, E.controls j s * E.gamma j ∂μ := by
        simpa using (setAverage_finsetSum (μ := μ) (s := R) (t := Finset.univ)
          (f := fun j => fun s => E.controls j s * E.gamma j)
          (fun j _ => hcontrol j))
      _ = ∑ j, (⨍ s in R, E.controls j s ∂μ) * E.gamma j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [setAverage_eq, setAverage_eq, integral_mul_const]
        simp only [smul_eq_mul]
        ring
  change (⨍ s in R, E.outcome w s ∂μ) =
    E.beta * (⨍ s in R, E.treatment s ∂μ) +
      dotProduct (fun j => ⨍ s in R, E.controls j s ∂μ) E.gamma +
        (⨍ s in R, E.error w s ∂μ)
  calc
    (⨍ s in R, E.outcome w s ∂μ) =
        (⨍ s in R, E.beta * E.treatment s +
          dotProduct (fun j => E.controls j s) E.gamma + E.error w s ∂μ) := by
      apply setAverage_congr_fun hR
      exact hmodel.mono (fun s hs _ => hs)
    _ = (⨍ s in R, E.beta * E.treatment s ∂μ) +
          (⨍ s in R, dotProduct (fun j => E.controls j s) E.gamma ∂μ) +
            (⨍ s in R, E.error w s ∂μ) := by
      simpa only [Pi.add_apply] using
        calc
          (⨍ s in R, ((fun s => E.beta * E.treatment s) +
              (fun s => dotProduct (fun j => E.controls j s) E.gamma) +
                (fun s => E.error w s)) s ∂μ) =
              (⨍ s in R, ((fun s => E.beta * E.treatment s) +
                (fun s => dotProduct (fun j => E.controls j s) E.gamma)) s ∂μ) +
                  (⨍ s in R, E.error w s ∂μ) :=
            setAverage_add (hbeta.add hdot) (herrors_w i)
          _ = (⨍ s in R, E.beta * E.treatment s ∂μ) +
                (⨍ s in R, dotProduct (fun j => E.controls j s) E.gamma ∂μ) +
                  (⨍ s in R, E.error w s ∂μ) := by
            rw [setAverage_add hbeta hdot]
    _ = _ := by rw [hbeta_average, hdot_average]

/-- Public exact estimator-to-score translation API.  At a full-rank
resolution where the selected literal minimizer has its FWL form, the
estimator error is exactly the GLS-weighted regional error.  The two displayed
hypotheses are supplied on a tail by the source-facing FWL bridge, so this is
not a replacement estimator statement.  This visibility change leaves the
statement and proof body unchanged. -/
theorem slope_error_eq_weighted_regional_error
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hFWL : ∀ w, E.betaHat n w = fwlSlope E n w) :
    ∀ᵐ w ∂P,
      E.betaHat n w - E.beta =
        finiteWeightedScore
          (glsOutcomeWeight (E.kernel n)
            (regionalControls μ E.maps E.controls n)
            (regionalValues μ E.maps E.treatment n))
          (regionalRandomValues μ E.maps E.error n) w := by
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign
        (regionalValues μ E.maps E.treatment n)
        (regionalControls μ E.maps E.controls n)).rank = E.q + 1 := by
    change (InfillGLSLean.L023.sourceDesign
      (regionalValues μ E.maps E.treatment n)
      (regionalControls μ E.maps E.controls n)).rank = E.q + 1 at hfull
    exact hfull
  have hprecision : (E.kernel n)⁻¹ |>.PosDef := (E.kernel_posDef n).inv
  rcases InfillGLSLean.L023.sourceDesign_fwl_nonsingularity_and_relevance_of_full_rank
    (regionalValues μ E.maps E.treatment n)
    (regionalControls μ E.maps E.controls n)
    (E.kernel n)⁻¹ hprecision hfull_source with ⟨hgram, hresidual⟩
  let weight := glsOutcomeWeight (E.kernel n)
    (regionalControls μ E.maps E.controls n)
    (regionalValues μ E.maps E.treatment n)
  have hunit :
      dotProduct weight (regionalValues μ E.maps E.treatment n) = 1 := by
    exact glsOutcomeWeight_dot_treatment_eq_one (E.kernel n) (E.kernel_posDef n)
      (regionalControls μ E.maps E.controls n)
      (regionalValues μ E.maps E.treatment n) hgram hresidual
  have hcontrol :
      dotProduct weight
        (regionalControls μ E.maps E.controls n *ᵥ E.gamma) = 0 := by
    exact glsOutcomeWeight_dot_controls_eq_zero (E.kernel n)
      (regionalControls μ E.maps E.controls n)
      (regionalValues μ E.maps E.treatment n) hgram E.gamma
  filter_upwards [regional_structural_model E n] with w hregional
  have hfwl_dot :
      fwlSlope E n w =
        dotProduct weight (fun i => regionalRandomValues μ E.maps E.outcome n i w) := by
    exact fwlEstimateControls_eq_glsOutcomeWeight_dot (E.kernel n) (E.kernel_posDef n)
      (regionalControls μ E.maps E.controls n)
      (regionalValues μ E.maps E.treatment n)
      (fun i => regionalRandomValues μ E.maps E.outcome n i w) hgram hresidual
  have houtcome :
      (fun i => regionalRandomValues μ E.maps E.outcome n i w) =
        E.beta • regionalValues μ E.maps E.treatment n +
          regionalControls μ E.maps E.controls n *ᵥ E.gamma +
            (fun i => regionalRandomValues μ E.maps E.error n i w) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.mulVec, regionalControls_apply]
    change regionalRandomValues μ E.maps E.outcome n i w =
      E.beta * regionalValues μ E.maps E.treatment n i +
        dotProduct (fun j => regionalValues μ E.maps (E.controls j) n i) E.gamma +
          regionalRandomValues μ E.maps E.error n i w
    exact hregional i
  calc
    E.betaHat n w - E.beta =
        dotProduct weight (fun i => regionalRandomValues μ E.maps E.outcome n i w) -
          E.beta := by rw [hFWL w, hfwl_dot]
    _ = dotProduct weight
        (E.beta • regionalValues μ E.maps E.treatment n +
          regionalControls μ E.maps E.controls n *ᵥ E.gamma +
            (fun i => regionalRandomValues μ E.maps E.error n i w)) -
          E.beta := by rw [← houtcome]
    _ = E.beta * dotProduct weight (regionalValues μ E.maps E.treatment n) +
          dotProduct weight (regionalControls μ E.maps E.controls n *ᵥ E.gamma) +
            dotProduct weight (fun i => regionalRandomValues μ E.maps E.error n i w) -
          E.beta := by
      rw [dotProduct_add, dotProduct_add, dotProduct_smul]
      simp only [smul_eq_mul]
    _ = finiteWeightedScore weight
          (regionalRandomValues μ E.maps E.error n) w := by
      rw [hunit, hcontrol]
      change E.beta * 1 + 0 +
          (∑ i, weight i * regionalRandomValues μ E.maps E.error n i w) - E.beta =
        finiteWeightedScore weight (regionalRandomValues μ E.maps E.error n) w
      simp only [finiteWeightedScore_apply]
      ring

/-- The exact displayed finite-resolution MSE inequality in the source
notation.  Every finite condition is derived from the experiment and the
literal covariance upper bound at this resolution. -/
private theorem conditional_slope_mse_bound_at_full_rank
    (E : FixedConditionalExperiment μ P) (n : ℕ) (C : ℝ) (c : Fin E.q → ℝ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1)
    (hFWL : ∀ w, E.betaHat n w = fwlSlope E n w)
    (hupper : (C • E.kernel n - trueCovariance E n).PosSemidef) :
    conditionalSlopeMSE E n ≤ (C + meanEnergy E c n) / E.information n := by
  let rawError := regionalRandomValues μ E.maps E.error n
  let mean := regionalConditionalMean E.maps P E.error n
  let controls := regionalControls μ E.maps E.controls n
  let treatment := regionalValues μ E.maps E.treatment n
  let weight := glsOutcomeWeight (E.kernel n) controls treatment
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign treatment controls).rank = E.q + 1 := by
    change (InfillGLSLean.L023.sourceDesign treatment controls).rank = E.q + 1 at hfull
    exact hfull
  have hprecision : (E.kernel n)⁻¹ |>.PosDef := (E.kernel_posDef n).inv
  rcases InfillGLSLean.L023.sourceDesign_fwl_nonsingularity_and_relevance_of_full_rank
    treatment controls (E.kernel n)⁻¹ hprecision hfull_source with ⟨hgram, hresidual⟩
  have herror : ∀ i, MemLp (rawError i) 2 P := by
    intro i
    exact regional_error_memLp_two E n i
  have hcentered : ∀ i, P[centeredFiniteError rawError mean i] = 0 := by
    intro i
    change (∫ w, regionalRandomValues μ E.maps E.error n i w -
      regionalConditionalMean E.maps P E.error n i ∂P) = 0
    rw [integral_sub ((regional_error_memLp_two E n i).integrable (by norm_num))
      (integrable_const _), integral_const]
    simp [regionalConditionalMean]
  have hcovariance :
      (C • E.kernel n - finiteErrorCovariance (centeredFiniteError rawError mean) P).PosSemidef := by
    change (C • E.kernel n -
      finiteErrorCovariance
        (centeredFiniteError (regionalRandomValues μ E.maps E.error n)
          (regionalConditionalMean E.maps P E.error n)) P).PosSemidef
    rw [centered_regional_error_covariance_eq_true E n]
    exact hupper
  have hinformation :
      E.information n = InfillGLSLean.controlInformation (E.kernel n)⁻¹ controls treatment := by
    exact InfillGLSLean.ManuscriptSpecification.L027.information_eq_controlInformation_of_full_rank
      E n hfull
  have hweight_norm :
      quadraticForm (E.kernel n) weight = 1 / E.information n := by
    rw [glsOutcomeWeight_quadraticForm_eq_inv_information (E.kernel n)
      (E.kernel_posDef n) controls treatment hresidual, hinformation]
  have hcontrols : dotProduct weight (controls *ᵥ c) = 0 := by
    exact glsOutcomeWeight_dot_controls_eq_zero (E.kernel n) controls treatment hgram c
  have hraw_mse :
      (∫ w, (finiteWeightedScore weight rawError w) ^ 2 ∂P) ≤
        (C + quadraticForm (E.kernel n)⁻¹ (mean - controls *ᵥ c)) / E.information n := by
    exact finiteGLS_rawError_MSE_bound_fixed_control (E.kernel_posDef n) weight mean controls c
      rawError herror hcentered hcovariance hweight_norm hcontrols
  have herror_identity :
      ∀ᵐ w ∂P, E.betaHat n w - E.beta =
        finiteWeightedScore weight rawError w := by
    simpa only [weight, rawError, controls, treatment] using
      slope_error_eq_weighted_regional_error E n hfull hFWL
  rw [conditionalSlopeMSE_eq]
  calc
    (∫ w, (E.betaHat n w - E.beta) ^ 2 ∂P) =
        ∫ w, (finiteWeightedScore weight rawError w) ^ 2 ∂P := by
      apply integral_congr_ae
      exact herror_identity.mono (fun w hw => congrArg (fun x : ℝ => x ^ 2) hw)
    _ ≤ (C + quadraticForm (E.kernel n)⁻¹ (mean - controls *ᵥ c)) / E.information n :=
      hraw_mse
    _ = (C + meanEnergy E c n) / E.information n := by
      rfl

/-- Complete direct proof of the literal source-facing consistency
proposition.  This theorem changes neither a source assumption nor the
proposition's conclusion. -/
theorem manuscriptConsistency_complete
    (E : FixedConditionalExperiment μ P) :
    manuscriptConsistency E := by
  rw [manuscriptConsistency_iff]
  intro upper weakMean
  rw [consistencyConclusion_iff]
  have hFWL_tail : ∀ᶠ n in atTop, ∀ w, E.betaHat n w = fwlSlope E n w := by
    exact (estimatorHasFWLForm_iff E).mp
      (InfillGLSLean.ManuscriptSpecification.L027.estimatorHasFWLForm_of_fixedLawHypotheses E)
  rcases E.eventual_full_rank with ⟨nRank, hRank⟩
  rcases (eventually_atTop.1 hFWL_tail) with ⟨nFWL, hFWL⟩
  let N : ℕ := max (max nRank nFWL) upper.start
  have hMSEAt : ∀ n, N ≤ n →
      conditionalSlopeMSE E n ≤
        (upper.C + meanEnergy E weakMean.c n) / E.information n := by
    intro n hn
    have hnRank : nRank ≤ n := by
      calc
        nRank ≤ max nRank nFWL := le_max_left _ _
        _ ≤ max (max nRank nFWL) upper.start := le_max_left _ _
        _ = N := rfl
        _ ≤ n := hn
    have hnFWL : nFWL ≤ n := by
      calc
        nFWL ≤ max nRank nFWL := le_max_right _ _
        _ ≤ max (max nRank nFWL) upper.start := le_max_left _ _
        _ = N := rfl
        _ ≤ n := hn
    have hnUpper : upper.start ≤ n := by
      calc
        upper.start ≤ max (max nRank nFWL) upper.start := le_max_right _ _
        _ = N := rfl
        _ ≤ n := hn
    exact conditional_slope_mse_bound_at_full_rank E n upper.C weakMean.c
      (hRank n hnRank) (hFWL n hnFWL) (upper.bound n hnUpper).2
  have hMSE_tail : ∀ᶠ n in atTop,
      conditionalSlopeMSE E n ≤
        (upper.C + meanEnergy E weakMean.c n) / E.information n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hMSEAt n hn
  have hInv : Tendsto (fun n => (E.information n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp E.information_tendsto
  have hC : Tendsto (fun n => upper.C / E.information n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hInv)
  have hEnvelope : Tendsto
      (fun n => (upper.C + meanEnergy E weakMean.c n) / E.information n)
      atTop (nhds 0) := by
    simpa [add_div] using hC.add weakMean.relative_energy_tendsto
  let X : ℕ → Ω → ℝ := fun n w =>
    if N ≤ n then E.betaHat n w - E.beta else 0
  let B : ℕ → ℝ≥0∞ := fun n =>
    if N ≤ n then ENNReal.ofReal
      ((upper.C + meanEnergy E weakMean.c n) / E.information n) else 0
  have hXmem : ∀ n, MemLp (X n) 2 P := by
    intro n
    by_cases hn : N ≤ n
    · let weight := glsOutcomeWeight (E.kernel n)
        (regionalControls μ E.maps E.controls n)
        (regionalValues μ E.maps E.treatment n)
      have hscore : MemLp
          (finiteWeightedScore weight (regionalRandomValues μ E.maps E.error n)) 2 P :=
        memLp_finiteWeightedScore weight (regionalRandomValues μ E.maps E.error n)
          (fun i => regional_error_memLp_two E n i)
      apply hscore.ae_eq
      have hident := slope_error_eq_weighted_regional_error E n
        (hRank n (by
          calc
            nRank ≤ max nRank nFWL := le_max_left _ _
            _ ≤ max (max nRank nFWL) upper.start := le_max_left _ _
            _ = N := rfl
            _ ≤ n := hn))
        (hFWL n (by
          calc
            nFWL ≤ max nRank nFWL := le_max_right _ _
            _ ≤ max (max nRank nFWL) upper.start := le_max_left _ _
            _ = N := rfl
            _ ≤ n := hn))
      filter_upwards [hident] with w hw
      have hXn : X n = fun w => E.betaHat n w - E.beta := by
        funext w
        simp [X, hn]
      rw [hXn]
      exact hw.symm
    · simp [X, hn]
  have hBound : ∀ n, ENNReal.ofReal (∫ w, (X n w) ^ 2 ∂P) ≤ B n := by
    intro n
    by_cases hn : N ≤ n
    · simpa [X, B, hn, conditionalSlopeMSE_eq] using
        ENNReal.ofReal_le_ofReal (hMSEAt n hn)
    · norm_num [X, B, hn]
  have hBzero : Tendsto B atTop (nhds 0) := by
    rw [tendsto_congr' (show B =ᶠ[atTop] fun n =>
      ENNReal.ofReal ((upper.C + meanEnergy E weakMean.c n) / E.information n) by
        filter_upwards [eventually_ge_atTop N] with n hn
        simp [B, hn])]
    simpa using ENNReal.tendsto_ofReal hEnvelope
  have hXzero : TendstoInMeasure P X atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_zero_of_integral_sq_bound hXmem hBound hBzero
  let F : ℕ → Ω → ℝ := fun n w =>
    if N ≤ n then E.betaHat n w else E.beta
  have hF : TendstoInMeasure P F atTop (fun _ => E.beta) := by
    rw [tendstoInMeasure_iff_dist] at hXzero ⊢
    intro epsilon hepsilon
    convert hXzero epsilon hepsilon using 1
    ext n
    congr 1
    ext w
    by_cases hn : N ≤ n
    · have hFn : F n w = E.betaHat n w := by simp [F, hn]
      have hXn : X n w = E.betaHat n w - E.beta := by simp [X, hn]
      change epsilon ≤ dist (F n w) E.beta ↔ epsilon ≤ dist (X n w) 0
      rw [hFn, hXn, Real.dist_eq]
      simp
    · simp [F, X, hn]
  refine ⟨?_, hMSE_tail, hEnvelope⟩
  apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hF
  filter_upwards [eventually_ge_atTop N] with n hn
  filter_upwards [] with w
  simp [F, hn]

end InfillGLSLean.ManuscriptSpecification.L029
