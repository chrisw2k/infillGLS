module

public import InfillGLSLean.MatrixCovarianceOrder
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Ring

public section

/-!
# Deterministic covariance-sandwich limit for GLS weights

This module formalizes the deterministic calculation in the proofs of
Propositions `prop:normality` and `prop:variance` following manuscript
equations `eq:covariance` and `eq:weight-identities`.  A two-sided Loewner
bound and the working-weight identity yield bounds on the normalized score
variance, and a vanishing covariance discrepancy squeezes that ratio to one.

This is only the variance-comparison component.  It does **not** construct a
conditional probability space, prove that a GLS score is conditionally
Gaussian, prove the negligible-bias lemma, establish residual-scale
consistency, or prove coverage.  Those are distinct steps in the manuscript.
-/

namespace InfillGLSLean

open Filter Matrix Topology

variable {ι : Type*} [Fintype ι]

/-- The finite deterministic covariance comparison behind the normality
proof.  If the true covariance is bracketed by the working covariance with
relative discrepancy `delta`, then `information * weight' truth weight /
varianceScale` is bracketed by the two scalar factors in `eq:covariance`. -/
theorem normalizedVariance_sandwich_of_matrix_covariance
    {truth working : Matrix ι ι ℝ} {weight : ι → ℝ}
    {varianceScale delta information : ℝ}
    (hscale : 0 < varianceScale) (hdelta_nonneg : 0 ≤ delta) (hdelta_lt_one : delta < 1)
    (hinformation : 0 < information)
    (hlower : (truth - (varianceScale / (1 + delta)) • working).PosSemidef)
    (hupper : ((varianceScale / (1 - delta)) • working - truth).PosSemidef)
    (hweight : quadraticForm working weight = 1 / information) :
    1 / (1 + delta) ≤ information * quadraticForm truth weight / varianceScale ∧
      information * quadraticForm truth weight / varianceScale ≤ 1 / (1 - delta) := by
  have hplus : 0 < 1 + delta := by linarith
  have hminus : 0 < 1 - delta := by linarith
  have hsandwich := quadraticForm_sandwich_div_information
    (lower := varianceScale / (1 + delta)) (upper := varianceScale / (1 - delta))
    (information := information) hlower hupper weight hweight
  constructor
  · have hleft_mul : varianceScale / (1 + delta) ≤ information * quadraticForm truth weight := by
      calc
        varianceScale / (1 + delta) =
            information * ((varianceScale / (1 + delta)) / information) := by
              field_simp [hinformation.ne', hplus.ne']
        _ ≤ information * quadraticForm truth weight :=
          mul_le_mul_of_nonneg_left hsandwich.1 (le_of_lt hinformation)
    calc
      1 / (1 + delta) = (varianceScale / (1 + delta)) / varianceScale := by
        field_simp [hscale.ne', hplus.ne']
      _ ≤ information * quadraticForm truth weight / varianceScale :=
        div_le_div_of_nonneg_right hleft_mul (le_of_lt hscale)
  · have hright_mul : information * quadraticForm truth weight ≤ varianceScale / (1 - delta) := by
      calc
        information * quadraticForm truth weight ≤
            information * ((varianceScale / (1 - delta)) / information) :=
          mul_le_mul_of_nonneg_left hsandwich.2 (le_of_lt hinformation)
        _ = varianceScale / (1 - delta) := by
          field_simp [hinformation.ne', hminus.ne']
    calc
      information * quadraticForm truth weight / varianceScale ≤
          (varianceScale / (1 - delta)) / varianceScale :=
        div_le_div_of_nonneg_right hright_mul (le_of_lt hscale)
      _ = 1 / (1 - delta) := by
        field_simp [hscale.ne', hminus.ne']

/-- The scalar squeeze consequence of `eq:covariance`: a positive common
variance scale and two-sided relative covariance bounds imply that the
normalized variance tends to one. -/
theorem normalizedVariance_tendsto_one_of_covariance_sandwich
    {normalizedVariance delta : ℕ → ℝ} {varianceScale : ℝ}
    (hscale : 0 < varianceScale)
    (hdelta_nonneg : ∀ n, 0 ≤ delta n) (hdelta_lt_one : ∀ n, delta n < 1)
    (hdelta_zero : Tendsto delta atTop (𝓝 0))
    (hsandwich : ∀ n,
      varianceScale / (1 + delta n) ≤ normalizedVariance n ∧
        normalizedVariance n ≤ varianceScale / (1 - delta n)) :
    Tendsto (fun n => normalizedVariance n / varianceScale) atTop (𝓝 1) := by
  have hratio : ∀ n,
      1 / (1 + delta n) ≤ normalizedVariance n / varianceScale ∧
        normalizedVariance n / varianceScale ≤ 1 / (1 - delta n) := by
    intro n
    have hplus : 0 < 1 + delta n := by linarith [hdelta_nonneg n]
    have hminus : 0 < 1 - delta n := by linarith [hdelta_lt_one n]
    constructor
    · calc
        1 / (1 + delta n) = (varianceScale / (1 + delta n)) / varianceScale := by
          field_simp [hscale.ne', hplus.ne']
        _ ≤ normalizedVariance n / varianceScale :=
          div_le_div_of_nonneg_right (hsandwich n).1 (le_of_lt hscale)
    · calc
        normalizedVariance n / varianceScale ≤
            (varianceScale / (1 - delta n)) / varianceScale :=
          div_le_div_of_nonneg_right (hsandwich n).2 (le_of_lt hscale)
        _ = 1 / (1 - delta n) := by
          field_simp [hscale.ne', hminus.ne']
  have hlower : Tendsto (fun n => 1 / (1 + delta n)) atTop (𝓝 1) := by
    have hdenom : Tendsto (fun n => (1 : ℝ) + delta n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add hdelta_zero)
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hdiv := hconst.div hdenom one_ne_zero
    have hfun : ((fun _ : ℕ => (1 : ℝ)) / fun n => 1 + delta n) =
        fun n => 1 / (1 + delta n) := by
      funext n
      simp only [Pi.div_apply]
    rw [hfun] at hdiv
    simpa using hdiv
  have hupper : Tendsto (fun n => 1 / (1 - delta n)) atTop (𝓝 1) := by
    have hdenom : Tendsto (fun n => (1 : ℝ) - delta n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdelta_zero)
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hdiv := hconst.div hdenom one_ne_zero
    have hfun : ((fun _ : ℕ => (1 : ℝ)) / fun n => 1 - delta n) =
        fun n => 1 / (1 - delta n) := by
      funext n
      simp only [Pi.div_apply]
    rw [hfun] at hdiv
    simpa using hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
    (fun n => (hratio n).1) (fun n => (hratio n).2)

/-- Eventual scalar form of the covariance-sandwich limit.  This is the
source-aligned version: `ass:covariance` only asserts its bounds from some
resolution onward. -/
theorem normalizedVariance_tendsto_one_of_eventually_covariance_sandwich
    {normalizedVariance delta : ℕ → ℝ} {varianceScale : ℝ}
    (hscale : 0 < varianceScale)
    (hdelta_nonneg : ∀ᶠ n in atTop, 0 ≤ delta n)
    (hdelta_lt_one : ∀ᶠ n in atTop, delta n < 1)
    (hdelta_zero : Tendsto delta atTop (𝓝 0))
    (hsandwich : ∀ᶠ n in atTop,
      varianceScale / (1 + delta n) ≤ normalizedVariance n ∧
        normalizedVariance n ≤ varianceScale / (1 - delta n)) :
    Tendsto (fun n => normalizedVariance n / varianceScale) atTop (𝓝 1) := by
  have hratio : ∀ᶠ n in atTop,
      1 / (1 + delta n) ≤ normalizedVariance n / varianceScale ∧
        normalizedVariance n / varianceScale ≤ 1 / (1 - delta n) := by
    filter_upwards [hdelta_nonneg, hdelta_lt_one, hsandwich] with n hnonneg hlt hs
    have hplus : 0 < 1 + delta n := by linarith
    have hminus : 0 < 1 - delta n := by linarith
    constructor
    · calc
        1 / (1 + delta n) = (varianceScale / (1 + delta n)) / varianceScale := by
          field_simp [hscale.ne', hplus.ne']
        _ ≤ normalizedVariance n / varianceScale :=
          div_le_div_of_nonneg_right hs.1 (le_of_lt hscale)
    · calc
        normalizedVariance n / varianceScale ≤
            (varianceScale / (1 - delta n)) / varianceScale :=
          div_le_div_of_nonneg_right hs.2 (le_of_lt hscale)
        _ = 1 / (1 - delta n) := by
          field_simp [hscale.ne', hminus.ne']
  have hlower : Tendsto (fun n => 1 / (1 + delta n)) atTop (𝓝 1) := by
    have hdenom : Tendsto (fun n => (1 : ℝ) + delta n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add hdelta_zero)
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hdiv := hconst.div hdenom one_ne_zero
    have hfun : ((fun _ : ℕ => (1 : ℝ)) / fun n => 1 + delta n) =
        fun n => 1 / (1 + delta n) := by
      funext n
      simp only [Pi.div_apply]
    rw [hfun] at hdiv
    simpa using hdiv
  have hupper : Tendsto (fun n => 1 / (1 - delta n)) atTop (𝓝 1) := by
    have hdenom : Tendsto (fun n => (1 : ℝ) - delta n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdelta_zero)
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hdiv := hconst.div hdenom one_ne_zero
    have hfun : ((fun _ : ℕ => (1 : ℝ)) / fun n => 1 - delta n) =
        fun n => 1 / (1 - delta n) := by
      funext n
      simp only [Pi.div_apply]
    rw [hfun] at hdiv
    simpa using hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hratio.mono fun _ h => h.1) (hratio.mono fun _ h => h.2)

/-- Matrix-sequence form of the deterministic inference bridge.  The
hypotheses are exactly the finite covariance sandwich and working-weight
normalization at each index; this theorem supplies only the variance-ratio
limit later consumed by the Gaussian and studentization arguments. -/
theorem matrix_normalizedVariance_tendsto_one
    {truth working : ℕ → Matrix ι ι ℝ} {weight : ℕ → ι → ℝ}
    {information delta : ℕ → ℝ} {varianceScale : ℝ}
    (hscale : 0 < varianceScale)
    (hdelta_nonneg : ∀ n, 0 ≤ delta n) (hdelta_lt_one : ∀ n, delta n < 1)
    (hdelta_zero : Tendsto delta atTop (𝓝 0))
    (hinformation : ∀ n, 0 < information n)
    (hlower : ∀ n,
      (truth n - (varianceScale / (1 + delta n)) • working n).PosSemidef)
    (hupper : ∀ n,
      ((varianceScale / (1 - delta n)) • working n - truth n).PosSemidef)
    (hweight : ∀ n, quadraticForm (working n) (weight n) = 1 / information n) :
    Tendsto (fun n =>
      (information n * quadraticForm (truth n) (weight n)) / varianceScale)
      atTop (𝓝 1) := by
  apply normalizedVariance_tendsto_one_of_covariance_sandwich hscale
    hdelta_nonneg hdelta_lt_one hdelta_zero
  intro n
  have hsandwich := normalizedVariance_sandwich_of_matrix_covariance
    hscale (hdelta_nonneg n) (hdelta_lt_one n) (hinformation n)
    (hlower n) (hupper n) (hweight n)
  constructor
  · calc
      varianceScale / (1 + delta n) = varianceScale * (1 / (1 + delta n)) := by
        simp [div_eq_mul_inv]
      _ ≤ varianceScale *
          (information n * quadraticForm (truth n) (weight n) / varianceScale) :=
        mul_le_mul_of_nonneg_left hsandwich.1 (le_of_lt hscale)
      _ = information n * quadraticForm (truth n) (weight n) := by
        field_simp [hscale.ne']
  · calc
      information n * quadraticForm (truth n) (weight n) =
          varianceScale *
            (information n * quadraticForm (truth n) (weight n) / varianceScale) := by
        field_simp [hscale.ne']
      _ ≤ varianceScale * (1 / (1 - delta n)) :=
        mul_le_mul_of_nonneg_left hsandwich.2 (le_of_lt hscale)
      _ = varianceScale / (1 - delta n) := by
        simp [div_eq_mul_inv]

/-- Eventual matrix-sequence version of the deterministic covariance bridge.
Its eventual hypotheses match the `n ≥ n₀` scope of `ass:covariance`; it still
does not provide conditional Gaussianity, the mean/bias argument, or a
residual-scale result. -/
theorem matrix_normalizedVariance_tendsto_one_of_eventually_covariance_sandwich
    {truth working : ℕ → Matrix ι ι ℝ} {weight : ℕ → ι → ℝ}
    {information delta : ℕ → ℝ} {varianceScale : ℝ}
    (hscale : 0 < varianceScale)
    (hdelta_nonneg : ∀ᶠ n in atTop, 0 ≤ delta n)
    (hdelta_lt_one : ∀ᶠ n in atTop, delta n < 1)
    (hdelta_zero : Tendsto delta atTop (𝓝 0))
    (hinformation : ∀ᶠ n in atTop, 0 < information n)
    (hlower : ∀ᶠ n in atTop,
      (truth n - (varianceScale / (1 + delta n)) • working n).PosSemidef)
    (hupper : ∀ᶠ n in atTop,
      ((varianceScale / (1 - delta n)) • working n - truth n).PosSemidef)
    (hweight : ∀ᶠ n in atTop,
      quadraticForm (working n) (weight n) = 1 / information n) :
    Tendsto (fun n =>
      (information n * quadraticForm (truth n) (weight n)) / varianceScale)
      atTop (𝓝 1) := by
  apply normalizedVariance_tendsto_one_of_eventually_covariance_sandwich hscale
    hdelta_nonneg hdelta_lt_one hdelta_zero
  filter_upwards [hdelta_nonneg, hdelta_lt_one, hinformation, hlower, hupper, hweight]
    with n hnonneg hlt hinfo hlow hupp hweight
  have hsandwich := normalizedVariance_sandwich_of_matrix_covariance
    hscale hnonneg hlt hinfo hlow hupp hweight
  constructor
  · calc
      varianceScale / (1 + delta n) = varianceScale * (1 / (1 + delta n)) := by
        simp [div_eq_mul_inv]
      _ ≤ varianceScale *
          (information n * quadraticForm (truth n) (weight n) / varianceScale) :=
        mul_le_mul_of_nonneg_left hsandwich.1 (le_of_lt hscale)
      _ = information n * quadraticForm (truth n) (weight n) := by
        field_simp [hscale.ne']
  · calc
      information n * quadraticForm (truth n) (weight n) =
          varianceScale *
            (information n * quadraticForm (truth n) (weight n) / varianceScale) := by
        field_simp [hscale.ne']
      _ ≤ varianceScale * (1 / (1 - delta n)) :=
        mul_le_mul_of_nonneg_left hsandwich.2 (le_of_lt hscale)
      _ = varianceScale / (1 - delta n) := by
        simp [div_eq_mul_inv]

/-- The eventual covariance bridge with a potentially different finite index
type at each resolution.  This accommodates the manuscript's growing regional
dimension `N_n`; it remains only the deterministic variance comparison. -/
theorem varyingIndex_normalizedVariance_tendsto_one_of_eventually_covariance_sandwich
    {index : ℕ → Type*} [∀ n, Fintype (index n)]
    {truth working : (n : ℕ) → Matrix (index n) (index n) ℝ}
    {weight : (n : ℕ) → index n → ℝ}
    {information delta : ℕ → ℝ} {varianceScale : ℝ}
    (hscale : 0 < varianceScale)
    (hdelta_nonneg : ∀ᶠ n in atTop, 0 ≤ delta n)
    (hdelta_lt_one : ∀ᶠ n in atTop, delta n < 1)
    (hdelta_zero : Tendsto delta atTop (𝓝 0))
    (hinformation : ∀ᶠ n in atTop, 0 < information n)
    (hlower : ∀ᶠ n in atTop,
      (truth n - (varianceScale / (1 + delta n)) • working n).PosSemidef)
    (hupper : ∀ᶠ n in atTop,
      ((varianceScale / (1 - delta n)) • working n - truth n).PosSemidef)
    (hweight : ∀ᶠ n in atTop,
      quadraticForm (working n) (weight n) = 1 / information n) :
    Tendsto (fun n =>
      (information n * quadraticForm (truth n) (weight n)) / varianceScale)
      atTop (𝓝 1) := by
  apply normalizedVariance_tendsto_one_of_eventually_covariance_sandwich hscale
    hdelta_nonneg hdelta_lt_one hdelta_zero
  filter_upwards [hdelta_nonneg, hdelta_lt_one, hinformation, hlower, hupper, hweight]
    with n hnonneg hlt hinfo hlow hupp hweight
  have hsandwich := normalizedVariance_sandwich_of_matrix_covariance
    hscale hnonneg hlt hinfo hlow hupp hweight
  constructor
  · calc
      varianceScale / (1 + delta n) = varianceScale * (1 / (1 + delta n)) := by
        simp [div_eq_mul_inv]
      _ ≤ varianceScale *
          (information n * quadraticForm (truth n) (weight n) / varianceScale) :=
        mul_le_mul_of_nonneg_left hsandwich.1 (le_of_lt hscale)
      _ = information n * quadraticForm (truth n) (weight n) := by
        field_simp [hscale.ne']
  · calc
      information n * quadraticForm (truth n) (weight n) =
          varianceScale *
            (information n * quadraticForm (truth n) (weight n) / varianceScale) := by
        field_simp [hscale.ne']
      _ ≤ varianceScale * (1 / (1 - delta n)) :=
        mul_le_mul_of_nonneg_left hsandwich.2 (le_of_lt hscale)
      _ = varianceScale / (1 - delta n) := by
        simp [div_eq_mul_inv]

end InfillGLSLean
