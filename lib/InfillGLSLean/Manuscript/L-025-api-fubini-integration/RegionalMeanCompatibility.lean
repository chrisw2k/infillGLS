module

public import ManuscriptSpecification
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Exact fixed-law Fubini bridge for the manuscript specification

Source: `the source manuscript`, prose immediately following
`eq:conditional-mean` (lines 122--133).

This module proves the already stated identity that the conditional mean of
each regional error equals the regional average of the fixed conditional-mean
field.  It does not add an assumption or revise a manuscript proposition.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification

open MeasureTheory
open scoped ENNReal

universe u v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The prose identity following `eq:conditional-mean`, derived from the
joint measurability and conditional second-moment hypotheses already carried
by the fixed conditional experiment. -/
theorem regionalMeanCompatibility_of_fixedLawHypotheses
    (E : FixedConditionalExperiment μ P) :
    regionalMeanCompatibility E := by
  unfold regionalMeanCompatibility
  intro n i
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
  have hsq_integrable :
      Integrable (fun z : Ω × Point D => E.error z.1 z.2 ^ 2) (P.prod μ) :=
    (lintegral_ofReal_ne_top_iff_integrable hsq_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => sq_nonneg (E.error z.1 z.2))).mp
      hsq_lintegral.ne
  have hproduct : Integrable (fun z : Ω × Point D => E.error z.1 z.2) (P.prod μ) := by
    have hmemLp : MemLp (fun z : Ω × Point D => E.error z.1 z.2) 2 (P.prod μ) :=
      (memLp_two_iff_integrable_sq E.error_jointly_measurable.aestronglyMeasurable).mpr
        hsq_integrable
    exact hmemLp.integrable (by norm_num)
  have hrestricted :
      Integrable (fun z : Ω × Point D => E.error z.1 z.2)
        (P.prod (μ.restrict ((E.maps.partition n).cell i))) := by
    have hmeasure :
        P.prod (μ.restrict ((E.maps.partition n).cell i)) =
          (P.prod μ).restrict (Set.univ ×ˢ (E.maps.partition n).cell i) := by
      calc
        P.prod (μ.restrict ((E.maps.partition n).cell i)) =
            (P.restrict Set.univ).prod (μ.restrict ((E.maps.partition n).cell i)) := by
              rw [Measure.restrict_univ]
        _ = (P.prod μ).restrict (Set.univ ×ˢ (E.maps.partition n).cell i) := by
              rw [Measure.prod_restrict]
    rw [hmeasure]
    exact hproduct.restrict
  change cellMean μ ((E.maps.partition n).cell i)
      (fun s => ∫ ω, E.error ω s ∂P) =
    ∫ ω, cellMean μ ((E.maps.partition n).cell i) (E.error ω) ∂P
  simp only [cellMean, setAverage_eq]
  rw [integral_smul]
  congr 1
  exact (integral_integral_swap hrestricted).symm

end InfillGLSLean.ManuscriptSpecification
