module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Finite diagonal-weight GLS and one-control FWL algebra

Task L-002 formalizes the finite algebra behind the manuscript's
`eq:information` and `eq:FWL`.  It intentionally works with a single control
and a diagonal working precision represented by finite weights.  Matrix-valued
positive-definite GLS and multiple-control projection are separate tasks.

All statements in this module are deterministic.  No distributional or
asymptotic claim is made here.
-/

public section

namespace InfillGLSLean

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A diagonal-weight inner product written as a finite sum. -/
def weightedInner (weight left right : ι → ℝ) : ℝ :=
  ∑ i, weight i * left i * right i

/-- The squared norm associated with `weightedInner`. -/
def weightedNormSq (weight vector : ι → ℝ) : ℝ :=
  weightedInner weight vector vector

/-- Residualize a vector against one control under diagonal weights. -/
noncomputable def residualize (weight control vector : ι → ℝ) : ι → ℝ :=
  fun i =>
    vector i -
      (weightedInner weight control vector / weightedNormSq weight control) * control i

theorem weightedInner_add_left (weight u v z : ι → ℝ) :
    weightedInner weight (u + v) z =
      weightedInner weight u z + weightedInner weight v z := by
  unfold weightedInner
  simp only [Pi.add_apply]
  calc
    ∑ i, weight i * (u i + v i) * z i =
        ∑ i, (weight i * u i * z i + weight i * v i * z i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i, weight i * u i * z i + ∑ i, weight i * v i * z i :=
      Finset.sum_add_distrib

theorem weightedInner_add_right (weight u v z : ι → ℝ) :
    weightedInner weight u (v + z) =
      weightedInner weight u v + weightedInner weight u z := by
  unfold weightedInner
  simp only [Pi.add_apply]
  calc
    ∑ i, weight i * u i * (v i + z i) =
        ∑ i, (weight i * u i * v i + weight i * u i * z i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i, weight i * u i * v i + ∑ i, weight i * u i * z i :=
      Finset.sum_add_distrib

theorem weightedInner_sub_right (weight u v z : ι → ℝ) :
    weightedInner weight u (v - z) =
      weightedInner weight u v - weightedInner weight u z := by
  unfold weightedInner
  simp only [Pi.sub_apply]
  calc
    ∑ i, weight i * u i * (v i - z i) =
        ∑ i, (weight i * u i * v i - weight i * u i * z i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i, weight i * u i * v i - ∑ i, weight i * u i * z i := by
      rw [Finset.sum_sub_distrib]

theorem weightedInner_smul_left (weight u v : ι → ℝ) (a : ℝ) :
    weightedInner weight (a • u) v = a * weightedInner weight u v := by
  unfold weightedInner
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ∑ i, weight i * (a * u i) * v i =
        ∑ i, a * (weight i * u i * v i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = a * ∑ i, weight i * u i * v i := by
      rw [Finset.mul_sum]

theorem weightedInner_smul_right (weight u v : ι → ℝ) (a : ℝ) :
    weightedInner weight u (a • v) = a * weightedInner weight u v := by
  unfold weightedInner
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ∑ i, weight i * u i * (a * v i) =
        ∑ i, a * (weight i * u i * v i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = a * ∑ i, weight i * u i * v i := by
      rw [Finset.mul_sum]

theorem weightedInner_symm (weight u v : ι → ℝ) :
    weightedInner weight u v = weightedInner weight v u := by
  unfold weightedInner
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem residualize_add (weight control u v : ι → ℝ) :
    residualize weight control (u + v) =
      residualize weight control u + residualize weight control v := by
  funext i
  simp only [residualize, Pi.add_apply]
  rw [weightedInner_add_right]
  ring

theorem residualize_smul (weight control u : ι → ℝ) (a : ℝ) :
    residualize weight control (a • u) = a • residualize weight control u := by
  funext i
  simp only [residualize, Pi.smul_apply, smul_eq_mul]
  rw [weightedInner_smul_right]
  ring

/-- A nondegenerate control residualizes to zero. -/
theorem residualize_control (weight control : ι → ℝ)
    (hcontrol : weightedNormSq weight control ≠ 0) :
    residualize weight control control = 0 := by
  funext i
  change control i -
      (weightedNormSq weight control / weightedNormSq weight control) * control i = 0
  rw [div_self hcontrol]
  ring

/-- The residualized vector is weighted-orthogonal to the control. -/
theorem weightedInner_control_residualize (weight control vector : ι → ℝ)
    (hcontrol : weightedNormSq weight control ≠ 0) :
    weightedInner weight control (residualize weight control vector) = 0 := by
  change weightedInner weight control
      (vector - (weightedInner weight control vector / weightedNormSq weight control) • control) = 0
  rw [weightedInner_sub_right, weightedInner_smul_right]
  change weightedInner weight control vector -
      (weightedInner weight control vector / weightedNormSq weight control) *
        weightedNormSq weight control = 0
  field_simp [hcontrol]
  ring

/-- Nonnegative diagonal weights make the weighted squared norm nonnegative. -/
theorem weightedNormSq_nonneg (weight vector : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ weightedNormSq weight vector := by
  unfold weightedNormSq weightedInner
  apply Finset.sum_nonneg
  intro i _
  rw [show weight i * vector i * vector i = weight i * (vector i * vector i) by ring]
  exact mul_nonneg (hweight i) (mul_self_nonneg _)

/-- The residualized-treatment information `Q`. -/
noncomputable def information (weight control treatment : ι → ℝ) : ℝ :=
  weightedNormSq weight (residualize weight control treatment)

/-- The diagonal-weight information is nonnegative under nonnegative weights. -/
theorem information_nonneg (weight control treatment : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ information weight control treatment :=
  weightedNormSq_nonneg weight (residualize weight control treatment) hweight

/-- The one-control, diagonal-weight Frisch--Waugh--Lovell estimator. -/
noncomputable def fwlEstimate (weight control treatment outcome : ι → ℝ) : ℝ :=
  weightedInner weight (residualize weight control treatment)
    (residualize weight control outcome) /
    information weight control treatment

/--
Under a one-control linear model, the FWL estimator equals the target
coefficient plus the residualized weighted error score divided by `Q`.
-/
theorem fwl_estimate_of_model
    (weight control treatment outcome error : ι → ℝ) (beta gamma : ℝ)
    (hcontrol : weightedNormSq weight control ≠ 0)
    (hinformation : information weight control treatment ≠ 0)
    (hmodel : outcome = beta • treatment + gamma • control + error) :
    fwlEstimate weight control treatment outcome =
      beta +
        weightedInner weight (residualize weight control treatment)
          (residualize weight control error) /
          information weight control treatment := by
  have hresidual :
      residualize weight control outcome =
        beta • residualize weight control treatment + residualize weight control error := by
    calc
      residualize weight control outcome =
          residualize weight control (beta • treatment + gamma • control + error) := by
            rw [hmodel]
      _ = residualize weight control (beta • treatment + gamma • control) +
          residualize weight control error :=
            residualize_add weight control (beta • treatment + gamma • control) error
      _ = (residualize weight control (beta • treatment) +
          residualize weight control (gamma • control)) +
          residualize weight control error := by
            rw [residualize_add]
      _ = (beta • residualize weight control treatment +
          gamma • residualize weight control control) +
          residualize weight control error := by
            rw [residualize_smul, residualize_smul]
      _ = beta • residualize weight control treatment + residualize weight control error := by
            rw [residualize_control weight control hcontrol]
            have hsmulZero : gamma • (0 : ι → ℝ) = 0 := by
              funext i
              simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero]
            rw [hsmulZero, add_zero]
  unfold fwlEstimate
  rw [hresidual, weightedInner_add_right, weightedInner_smul_right]
  change
    (beta * information weight control treatment +
      weightedInner weight (residualize weight control treatment)
        (residualize weight control error)) /
        information weight control treatment =
      beta +
        weightedInner weight (residualize weight control treatment)
          (residualize weight control error) /
          information weight control treatment
  field_simp [hinformation]

end InfillGLSLean
