module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real

public section

namespace InfillGLSLean.NormalCDFCalibration

open Filter MeasureTheory ProbabilityTheory Topology

/- The following reflection lemma is adapted, API-for-API, from the
   Apache-2.0 Causalean proof cited in TASK.md. -/
theorem cdf_neg_of_map_neg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (hmap : μ.map (fun x : ℝ => -x) = μ) (t : ℝ) :
    cdf μ (-t) = 1 - cdf μ t := by
  have hreal : ∀ s : ℝ, cdf μ s = μ.real (Set.Iic s) := by
    intro s
    exact cdf_eq_real _ s
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Iic (-t) = Set.Ici t := by
    ext x
    simp
  have step1 : cdf μ (-t) = μ.real (Set.Ici t) := by
    rw [hreal (-t)]
    conv_lhs => rw [← hmap]
    rw [MeasureTheory.map_measureReal_apply measurable_neg measurableSet_Iic, hpre]
  rw [step1, ← Set.compl_Iio, MeasureTheory.measureReal_compl measurableSet_Iio,
    MeasureTheory.measureReal_congr MeasureTheory.Iio_ae_eq_Iic,
    MeasureTheory.probReal_univ, hreal t]

theorem standardNormal_cdf_neg (t : ℝ) :
    cdf (gaussianReal 0 1) (-t) = 1 - cdf (gaussianReal 0 1) t := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  let _ : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (v := 1) one_ne_zero
  exact cdf_neg_of_map_neg hmap t

theorem standardNormal_cdf_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have h := standardNormal_cdf_neg 0
  norm_num at h ⊢
  linarith

private theorem cdf_eq_of_measure_Iic {α z : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hquantile : gaussianReal 0 1 (Set.Iic z) = ENNReal.ofReal (1 - α / 2)) :
    cdf (gaussianReal 0 1) z = 1 - α / 2 := by
  rw [cdf_eq_real, MeasureTheory.measureReal_def, hquantile,
    ENNReal.toReal_ofReal]
  linarith

private theorem quantile_pos {α z : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hquantile : gaussianReal 0 1 (Set.Iic z) = ENNReal.ofReal (1 - α / 2)) :
    0 < z := by
  have hcdf := cdf_eq_of_measure_Iic hα_pos hα_lt_one hquantile
  by_contra hnot
  have hz : z ≤ 0 := le_of_not_gt hnot
  have hmono := monotone_cdf (gaussianReal 0 1) hz
  rw [hcdf, standardNormal_cdf_zero] at hmono
  linarith

private theorem standardNormal_left_tail_of_quantile {α z : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hquantile : gaussianReal 0 1 (Set.Iic z) = ENNReal.ofReal (1 - α / 2)) :
    gaussianReal 0 1 (Set.Iic (-z)) = ENNReal.ofReal (α / 2) := by
  rw [← ofReal_cdf, standardNormal_cdf_neg,
    cdf_eq_of_measure_Iic hα_pos hα_lt_one hquantile]
  congr 1
  ring

/-- The exact two-sided standard-normal calibration used by the manuscript's
confidence interval.  Its premise is the source's one-sided quantile
calibration, represented as a raw probability measure. -/
theorem standardNormal_interval_measure_of_quantile {α z : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hquantile : gaussianReal 0 1 (Set.Iic z) = ENNReal.ofReal (1 - α / 2)) :
    gaussianReal 0 1 (Set.Icc (-z) z) = ENNReal.ofReal (1 - α) := by
  let _ : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (v := 1) one_ne_zero
  have hz_pos : 0 < z := quantile_pos hα_pos hα_lt_one hquantile
  have hleft := standardNormal_left_tail_of_quantile hα_pos hα_lt_one hquantile
  have hsmall : -z ≤ z := by linarith
  have hsets : Set.Iio (-z) ∪ Set.Icc (-z) z = Set.Iic z :=
    Set.Iio_union_Icc_eq_Iic hsmall
  have hdisjoint : Disjoint (Set.Iio (-z)) (Set.Icc (-z) z) := by
    rw [Set.disjoint_left]
    intro x hx hxc
    exact (not_lt_of_ge hxc.1) hx
  have hleft_open : gaussianReal 0 1 (Set.Iio (-z)) =
      gaussianReal 0 1 (Set.Iic (-z)) := by
    exact MeasureTheory.measure_congr MeasureTheory.Iio_ae_eq_Iic
  have hsum : ENNReal.ofReal (1 - α / 2) =
      ENNReal.ofReal (α / 2) + gaussianReal 0 1 (Set.Icc (-z) z) := by
    calc
      ENNReal.ofReal (1 - α / 2) = gaussianReal 0 1 (Set.Iic z) := hquantile.symm
      _ = gaussianReal 0 1 (Set.Iio (-z) ∪ Set.Icc (-z) z) := by rw [hsets]
      _ = gaussianReal 0 1 (Set.Iio (-z)) + gaussianReal 0 1 (Set.Icc (-z) z) :=
        MeasureTheory.measure_union hdisjoint measurableSet_Icc
      _ = ENNReal.ofReal (α / 2) + gaussianReal 0 1 (Set.Icc (-z) z) := by
        rw [hleft_open, hleft]
  have halgebra : ENNReal.ofReal (1 - α / 2) =
      ENNReal.ofReal (α / 2) + ENNReal.ofReal (1 - α) := by
    rw [← ENNReal.ofReal_add]
    · congr 1
      ring
    · linarith
    · linarith
  apply (ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal (α / 2) + gaussianReal 0 1 (Set.Icc (-z) z) =
        ENNReal.ofReal (1 - α / 2) := hsum.symm
    _ = ENNReal.ofReal (α / 2) + ENNReal.ofReal (1 - α) := halgebra

theorem standardNormal_interval_toNNReal_of_quantile {α z : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hquantile : gaussianReal 0 1 (Set.Iic z) = ENNReal.ofReal (1 - α / 2)) :
    (gaussianReal 0 1 (Set.Icc (-z) z)).toNNReal = (1 - α).toNNReal := by
  rw [standardNormal_interval_measure_of_quantile hα_pos hα_lt_one hquantile]
  rfl

end InfillGLSLean.NormalCDFCalibration
