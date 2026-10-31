module

public import InfillGLSLean.FiniteGaussianScore
public import InfillGLSLean.GaussianQuadraticMoments
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic

/-!
Finite Gaussian moment support for the residual quadratic form in manuscript
Appendix `app:scale`. This module intentionally proves only standard
finite-dimensional Wick/Isserlis identities; it changes neither the
manuscript propositions nor their assumptions.
-/

namespace InfillGLSLean.FiniteWickBridge

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace

/-! ## Scalar centered Gaussian moments -/

/-- The third derivative at zero of a centered Gaussian MGF vanishes. -/
private theorem centered_mgf_third_derivative (v : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) 0 = 0 := by
  let f : ℝ → ℝ := fun t => Real.exp (v * t ^ 2 / 2)
  have hf : ∀ t : ℝ, HasDerivAt f (v * t * f t) t := by
    intro t
    dsimp [f]
    convert Real.hasDerivAt_exp (v * t ^ 2 / 2) |>.comp t
      (((hasDerivAt_const (x := t) v).mul ((hasDerivAt_id t).pow 2)).div_const 2) using 1
    · ext u
      rfl
    · simp only [Pi.pow_apply, id_eq]
      ring
  have hlin : ∀ t : ℝ, HasDerivAt (fun u : ℝ => v * u) v t := by
    intro t
    convert (hasDerivAt_const (x := t) v).mul (hasDerivAt_id t) using 1
    · ext u
      rfl
    · ring
  have hquad : ∀ t : ℝ, HasDerivAt (fun u : ℝ => v + v ^ 2 * u ^ 2)
      (2 * v ^ 2 * t) t := by
    intro t
    convert (hasDerivAt_const (x := t) v).add
      ((hasDerivAt_const (x := t) (v ^ 2)).mul ((hasDerivAt_id t).pow 2)) using 1
    · ext u
      rfl
    · simp only [Pi.pow_apply, id_eq]
      ring
  have h1 : deriv f = fun t => v * t * f t := by
    funext t
    exact (hf t).deriv
  have h2 : deriv (fun t : ℝ => v * t * f t) =
      fun t => (v + v ^ 2 * t ^ 2) * f t := by
    funext t
    convert ((hlin t).mul (hf t)).deriv using 1
    ring
  have h3 : deriv (fun t : ℝ => (v + v ^ 2 * t ^ 2) * f t) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f t := by
    funext t
    convert ((hquad t).mul (hf t)).deriv using 1
    ring
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1, h2, h3]
  simp [f]

/-- A centered scalar Gaussian has vanishing third moment. -/
private theorem centered_gaussian_third_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal 0 variance) P) :
    (∫ ω, X ω ^ 3 ∂P) = 0 := by
  calc
    (∫ ω, X ω ^ 3 ∂P) = ∫ x, x ^ 3 ∂gaussianReal 0 variance := by
      simpa only [Function.comp_apply] using hX.integral_comp (f := fun x : ℝ => x ^ 3)
        ((continuous_id.pow 3).aestronglyMeasurable)
    _ = iteratedDeriv 3 (mgf (fun x : ℝ => x) (gaussianReal 0 variance)) 0 := by
      rw [iteratedDeriv_mgf_zero]
      · rfl
      · simp
    _ = 0 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      simpa using centered_mgf_third_derivative (variance : ℝ)

/-- The fourth derivative at zero of a centered Gaussian MGF. -/
private theorem centered_mgf_fourth_derivative (v : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) 0 = 3 * v ^ 2 := by
  let f : ℝ → ℝ := fun t => Real.exp (v * t ^ 2 / 2)
  have hf : ∀ t : ℝ, HasDerivAt f (v * t * f t) t := by
    intro t
    dsimp [f]
    convert Real.hasDerivAt_exp (v * t ^ 2 / 2) |>.comp t
      (((hasDerivAt_const (x := t) v).mul ((hasDerivAt_id t).pow 2)).div_const 2) using 1
    · ext u
      rfl
    · simp only [Pi.pow_apply, id_eq]
      ring
  have hlin : ∀ t : ℝ, HasDerivAt (fun u : ℝ => v * u) v t := by
    intro t
    convert (hasDerivAt_const (x := t) v).mul (hasDerivAt_id t) using 1
    · ext u
      rfl
    · ring
  have hquad : ∀ t : ℝ, HasDerivAt (fun u : ℝ => v + v ^ 2 * u ^ 2)
      (2 * v ^ 2 * t) t := by
    intro t
    convert (hasDerivAt_const (x := t) v).add
      ((hasDerivAt_const (x := t) (v ^ 2)).mul ((hasDerivAt_id t).pow 2)) using 1
    · ext u
      rfl
    · simp only [Pi.pow_apply, id_eq]
      ring
  have hcub : ∀ t : ℝ, HasDerivAt (fun u : ℝ => 3 * v ^ 2 * u + v ^ 3 * u ^ 3)
      (3 * v ^ 2 + 3 * v ^ 3 * t ^ 2) t := by
    intro t
    have hfirst : HasDerivAt (fun u : ℝ => 3 * v ^ 2 * u) (3 * v ^ 2) t := by
      convert (hasDerivAt_const (x := t) (3 * v ^ 2)).mul (hasDerivAt_id t) using 1
      · ext u
        rfl
      · ring
    have hsecond : HasDerivAt (fun u : ℝ => v ^ 3 * u ^ 3)
        (3 * v ^ 3 * t ^ 2) t := by
      convert (hasDerivAt_const (x := t) (v ^ 3)).mul ((hasDerivAt_id t).pow 3) using 1
      · ext u
        simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
      · simp only [Pi.pow_apply, id_eq]
        ring
    exact hfirst.add hsecond
  have h1 : deriv f = fun t => v * t * f t := by
    funext t
    exact (hf t).deriv
  have h2 : deriv (fun t : ℝ => v * t * f t) =
      fun t => (v + v ^ 2 * t ^ 2) * f t := by
    funext t
    convert ((hlin t).mul (hf t)).deriv using 1
    ring
  have h3 : deriv (fun t : ℝ => (v + v ^ 2 * t ^ 2) * f t) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f t := by
    funext t
    convert ((hquad t).mul (hf t)).deriv using 1
    ring
  have h4 : deriv (fun t : ℝ => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f t) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * f t := by
    funext t
    convert ((hcub t).mul (hf t)).deriv using 1
    ring
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1, h2, h3, h4]
  simp [f]

/-- A centered scalar Gaussian has fourth moment `3 * variance^2`. -/
private theorem centered_gaussian_fourth_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal 0 variance) P) :
    (∫ ω, X ω ^ 4 ∂P) = 3 * (variance : ℝ) ^ 2 := by
  calc
    (∫ ω, X ω ^ 4 ∂P) = ∫ x, x ^ 4 ∂gaussianReal 0 variance := by
      simpa only [Function.comp_apply] using hX.integral_comp (f := fun x : ℝ => x ^ 4)
        ((continuous_id.pow 4).aestronglyMeasurable)
    _ = iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 variance)) 0 := by
      rw [iteratedDeriv_mgf_zero]
      · rfl
      · simp
    _ = 3 * (variance : ℝ) ^ 2 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      simpa using centered_mgf_fourth_derivative (variance : ℝ)

/-! ## Pairwise Wick identities from scalar Gaussian laws -/

/- The scalar and finite-quadratic endpoints below are reusable source-proof
infrastructure. Opening the public boundary here changes only visibility of
already-proved finite identities; it adds no model assumption or theorem. -/
public section

private theorem gaussian_integrable_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal 0 variance) P) :
    Integrable (fun ω => X ω ^ 3) P := by
  have hmem : MemLp X 3 P :=
    hX.memLp (memLp_id_gaussianReal' 3 (by norm_num))
  refine (hmem.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)).mono'
    (hmem.aestronglyMeasurable.pow 3) ?_
  filter_upwards [] with ω
  simp only [norm_pow, Real.norm_eq_abs]
  exact le_rfl

private theorem gaussian_integrable_fourth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {variance : NNReal}
    (hX : HasLaw X (gaussianReal 0 variance) P) :
    Integrable (fun ω => X ω ^ 4) P := by
  have hmem : MemLp X 4 P :=
    hX.memLp (memLp_id_gaussianReal' 4 (by norm_num))
  refine (hmem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)).mono'
    (hmem.aestronglyMeasurable.pow 4) ?_
  filter_upwards [] with ω
  simp only [norm_pow, Real.norm_eq_abs]
  exact le_rfl

/-- The mixed centered third moment of a jointly Gaussian pair vanishes.

Only the scalar laws of `X + Y`, `X - Y`, and `Y` are used.  This is the
degree-three Wick identity needed to remove the quadratic--linear covariance
term in a noncentral Gaussian quadratic form. -/
theorem centered_gaussian_square_mul_integral_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {vPlus vMinus vY : NNReal}
    (hPlus : HasLaw (fun ω => X ω + Y ω) (gaussianReal 0 vPlus) P)
    (hMinus : HasLaw (fun ω => X ω - Y ω) (gaussianReal 0 vMinus) P)
    (hY : HasLaw Y (gaussianReal 0 vY) P) :
    (∫ ω, X ω ^ 2 * Y ω ∂P) = 0 := by
  have hPlusInt := gaussian_integrable_cube hPlus
  have hMinusInt := gaussian_integrable_cube hMinus
  have hYInt := gaussian_integrable_cube hY
  have hpoly :
      (fun ω => 6 * (X ω ^ 2 * Y ω)) =
        fun ω => (X ω + Y ω) ^ 3 - (X ω - Y ω) ^ 3 - 2 * Y ω ^ 3 := by
    funext ω
    ring
  have hscaled : 6 * (∫ ω, X ω ^ 2 * Y ω ∂P) = 0 := by
    calc
      6 * (∫ ω, X ω ^ 2 * Y ω ∂P) =
          ∫ ω, 6 * (X ω ^ 2 * Y ω) ∂P := by
            rw [integral_const_mul]
      _ = ∫ ω, (X ω + Y ω) ^ 3 - (X ω - Y ω) ^ 3 - 2 * Y ω ^ 3 ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact congrFun hpoly ω
      _ = ((∫ ω, (X ω + Y ω) ^ 3 ∂P) -
          (∫ ω, (X ω - Y ω) ^ 3 ∂P)) -
          ∫ ω, 2 * Y ω ^ 3 ∂P := by
            let A : Ω → ℝ := fun ω => (X ω + Y ω) ^ 3
            let B : Ω → ℝ := fun ω => (X ω - Y ω) ^ 3
            let C : Ω → ℝ := fun ω => 2 * Y ω ^ 3
            have hA : Integrable A P := by simpa [A] using hPlusInt
            have hB : Integrable B P := by simpa [B] using hMinusInt
            have hC : Integrable C P := by simpa [C] using hYInt.const_mul (2 : ℝ)
            have hOuter : (∫ ω, A ω - B ω - C ω ∂P) =
                (∫ ω, A ω - B ω ∂P) - ∫ ω, C ω ∂P := by
              simpa only [Pi.sub_apply] using integral_sub (hA.sub hB) hC
            have hInner : (∫ ω, A ω - B ω ∂P) =
                (∫ ω, A ω ∂P) - ∫ ω, B ω ∂P := by
              simpa only [Pi.sub_apply] using integral_sub hA hB
            simpa [A, B, C] using hOuter.trans (by rw [hInner])
      _ = 0 := by
            rw [centered_gaussian_third_integral hPlus,
              centered_gaussian_third_integral hMinus,
              integral_const_mul,
              centered_gaussian_third_integral hY]
            ring
  linarith

/-- The pairwise fourth Wick identity in a scalar-law form.

The right side is intentionally expressed through the variances of `X + Y`
and `X - Y`; `centered_gaussian_pair_wick_fourth` below rewrites it into the
usual `vX * vY + 2 * covariance^2` form once those variance identities are
available. -/
theorem centered_gaussian_pair_fourth_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {vX vY vPlus vMinus : NNReal}
    (hX : HasLaw X (gaussianReal 0 vX) P)
    (hY : HasLaw Y (gaussianReal 0 vY) P)
    (hPlus : HasLaw (fun ω => X ω + Y ω) (gaussianReal 0 vPlus) P)
    (hMinus : HasLaw (fun ω => X ω - Y ω) (gaussianReal 0 vMinus) P) :
    (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P) =
      (3 * (vPlus : ℝ) ^ 2 + 3 * (vMinus : ℝ) ^ 2 -
        6 * (vX : ℝ) ^ 2 - 6 * (vY : ℝ) ^ 2) / 12 := by
  have hXInt := gaussian_integrable_fourth hX
  have hYInt := gaussian_integrable_fourth hY
  have hPlusInt := gaussian_integrable_fourth hPlus
  have hMinusInt := gaussian_integrable_fourth hMinus
  have hpoly :
      (fun ω => 12 * (X ω ^ 2 * Y ω ^ 2)) =
        fun ω => (X ω + Y ω) ^ 4 + (X ω - Y ω) ^ 4 -
          (2 * X ω ^ 4 + 2 * Y ω ^ 4) := by
    funext ω
    ring
  have hscaled : 12 * (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P) =
      3 * (vPlus : ℝ) ^ 2 + 3 * (vMinus : ℝ) ^ 2 -
        6 * (vX : ℝ) ^ 2 - 6 * (vY : ℝ) ^ 2 := by
    calc
      12 * (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P) =
          ∫ ω, 12 * (X ω ^ 2 * Y ω ^ 2) ∂P := by
            rw [integral_const_mul]
      _ = ∫ ω, (X ω + Y ω) ^ 4 + (X ω - Y ω) ^ 4 -
          (2 * X ω ^ 4 + 2 * Y ω ^ 4) ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact congrFun hpoly ω
      _ = ((∫ ω, (X ω + Y ω) ^ 4 ∂P) +
          (∫ ω, (X ω - Y ω) ^ 4 ∂P)) -
          ((∫ ω, 2 * X ω ^ 4 ∂P) + (∫ ω, 2 * Y ω ^ 4 ∂P)) := by
            let A : Ω → ℝ := fun ω => (X ω + Y ω) ^ 4
            let B : Ω → ℝ := fun ω => (X ω - Y ω) ^ 4
            let C : Ω → ℝ := fun ω => 2 * X ω ^ 4
            let D : Ω → ℝ := fun ω => 2 * Y ω ^ 4
            have hA : Integrable A P := by simpa [A] using hPlusInt
            have hB : Integrable B P := by simpa [B] using hMinusInt
            have hC : Integrable C P := by simpa [C] using hXInt.const_mul (2 : ℝ)
            have hD : Integrable D P := by simpa [D] using hYInt.const_mul (2 : ℝ)
            have hOuter : (∫ ω, A ω + B ω - (C ω + D ω) ∂P) =
                (∫ ω, A ω + B ω ∂P) - ∫ ω, C ω + D ω ∂P := by
              simpa only [Pi.add_apply, Pi.sub_apply] using
                integral_sub (hA.add hB) (hC.add hD)
            have hLeft : (∫ ω, A ω + B ω ∂P) =
                (∫ ω, A ω ∂P) + ∫ ω, B ω ∂P := by
              simpa only [Pi.add_apply] using integral_add hA hB
            have hRight : (∫ ω, C ω + D ω ∂P) =
                (∫ ω, C ω ∂P) + ∫ ω, D ω ∂P := by
              simpa only [Pi.add_apply] using integral_add hC hD
            simpa [A, B, C, D] using hOuter.trans (by rw [hLeft, hRight])
      _ = 3 * (vPlus : ℝ) ^ 2 + 3 * (vMinus : ℝ) ^ 2 -
          6 * (vX : ℝ) ^ 2 - 6 * (vY : ℝ) ^ 2 := by
            rw [centered_gaussian_fourth_integral hPlus,
              centered_gaussian_fourth_integral hMinus,
              integral_const_mul, centered_gaussian_fourth_integral hX,
              integral_const_mul, centered_gaussian_fourth_integral hY]
            ring
  calc
    (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P) =
        (12 * (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P)) / 12 := by ring
    _ = (3 * (vPlus : ℝ) ^ 2 + 3 * (vMinus : ℝ) ^ 2 -
        6 * (vX : ℝ) ^ 2 - 6 * (vY : ℝ) ^ 2) / 12 := by rw [hscaled]

/-- The familiar two-variable Isserlis identity.

The two variance equations are the ordinary centered-Gaussian identities for
`Var (X + Y)` and `Var (X - Y)`. -/
theorem centered_gaussian_pair_wick_fourth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {vX vY vPlus vMinus : NNReal} {covXY : ℝ}
    (hX : HasLaw X (gaussianReal 0 vX) P)
    (hY : HasLaw Y (gaussianReal 0 vY) P)
    (hPlus : HasLaw (fun ω => X ω + Y ω) (gaussianReal 0 vPlus) P)
    (hMinus : HasLaw (fun ω => X ω - Y ω) (gaussianReal 0 vMinus) P)
    (hPlusVar : (vPlus : ℝ) = (vX : ℝ) + (vY : ℝ) + 2 * covXY)
    (hMinusVar : (vMinus : ℝ) = (vX : ℝ) + (vY : ℝ) - 2 * covXY) :
    (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P) =
      (vX : ℝ) * (vY : ℝ) + 2 * covXY ^ 2 := by
  rw [centered_gaussian_pair_fourth_integral hX hY hPlus hMinus]
  rw [hPlusVar, hMinusVar]
  ring

/-! ## Finite quadratic aggregation

The next layer is deliberately stated through the exact coordinate moment
identities supplied by Wick's formula.  It proves the finite algebra needed
for the residual calculation, without assuming independence or changing any
manuscript hypothesis.  The later Gaussian-score bridge specializes these
coordinate moments. -/

section FiniteQuadratic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Sum of coordinate squares of a finite real random vector. -/
noncomputable def squareSum {I : Type*} [Fintype I] (X : I → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, X i ω ^ 2

/-- A finite deterministic linear score. -/
noncomputable def linearSum {I : Type*} [Fintype I]
    (b : I → ℝ) (X : I → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, b i * X i ω

/-- Squared norm of a finite Gaussian vector after a deterministic shift. -/
@[expose]
noncomputable def noncentralSquareSum {I : Type*} [Fintype I]
    (X : I → Ω → ℝ) (b : I → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, (X i ω + b i) ^ 2

private theorem noncentralSquareSum_decomposition
    {I : Type*} [Fintype I] (X : I → Ω → ℝ) (b : I → ℝ) :
    noncentralSquareSum X b =
      fun ω => squareSum X ω + 2 * linearSum b X ω + ∑ i, b i ^ 2 := by
  funext ω
  simp only [noncentralSquareSum, squareSum, linearSum]
  simp_rw [add_pow_two]
  simp_rw [Finset.sum_add_distrib]
  have hlinear : (∑ i, 2 * X i ω * b i) = 2 * (∑ i, b i * X i ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hlinear]

private theorem square_memLp_two
    {I : Type*} [Fintype I] [IsProbabilityMeasure P] {X : I → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 4 P) (i : I) :
    MemLp (fun ω => X i ω ^ 2) 2 P := by
  have hpow := (hX i).norm_rpow_div (2 : ENNReal)
  have hfour_div_two : (4 : ENNReal) / 2 = 2 := by
    calc
      (4 : ENNReal) / 2 = (2 * 2) / 2 := by norm_num
      _ = 2 := ENNReal.mul_div_cancel_right (by norm_num) ENNReal.ofNat_ne_top
  rw [hfour_div_two] at hpow
  simpa [Real.norm_eq_abs, sq_abs] using hpow

private theorem linear_memLp_two
    {I : Type*} [Fintype I] [IsProbabilityMeasure P] {X : I → Ω → ℝ}
    (b : I → ℝ) (hX : ∀ i, MemLp (X i) 4 P) (i : I) :
    MemLp (fun ω => b i * X i ω) 2 P := by
  exact ((hX i).mono_exponent
    (by norm_num : (2 : ENNReal) ≤ (4 : ENNReal))).const_mul (b i)

private theorem squareSum_memLp_two
    {I : Type*} [Fintype I] [IsProbabilityMeasure P] {X : I → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 4 P) : MemLp (squareSum X) 2 P := by
  unfold squareSum
  exact memLp_finsetSum Finset.univ (fun i _ => square_memLp_two hX i)

private theorem linearSum_memLp_two
    {I : Type*} [Fintype I] [IsProbabilityMeasure P] {X : I → Ω → ℝ}
    (b : I → ℝ) (hX : ∀ i, MemLp (X i) 4 P) : MemLp (linearSum b X) 2 P := by
  unfold linearSum
  exact memLp_finsetSum Finset.univ (fun i _ => linear_memLp_two b hX i)

private theorem noncentralSquareSum_memLp_two
    {I : Type*} [Fintype I] [IsProbabilityMeasure P] {X : I → Ω → ℝ}
    (b : I → ℝ) (hX : ∀ i, MemLp (X i) 4 P) :
    MemLp (noncentralSquareSum X b) 2 P := by
  rw [noncentralSquareSum_decomposition]
  convert (squareSum_memLp_two hX).add
    (((linearSum_memLp_two b hX).const_mul 2).add (memLp_const (∑ i, b i ^ 2))) using 1
  ext ω
  simp only [Pi.add_apply]
  ring

private theorem coordinate_memLp_two
    {I : Type*} [Fintype I] [IsProbabilityMeasure P] {X : I → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 4 P) (i : I) : MemLp (X i) 2 P := by
  exact (hX i).mono_exponent (by norm_num : (2 : ENNReal) ≤ (4 : ENNReal))

private theorem square_integral_eq_diag
    {I : Type*} [Fintype I] {X : I → Ω → ℝ} {C : Matrix I I ℝ}
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j) (i : I) :
    (∫ ω, X i ω ^ 2 ∂P) = C i i := by
  simpa [pow_two] using hsecond i i

private theorem covariance_coordinate_eq
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ}
    (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j) (i j : I) :
    cov[X i, X j; P] = C i j := by
  rw [covariance_eq_sub (coordinate_memLp_two hX i) (coordinate_memLp_two hX j)]
  have hproduct : (∫ ω, (X i * X j) ω ∂P) =
      ∫ ω, X i ω * X j ω ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rfl
  rw [hproduct, hsecond i j, hmean i, hmean j]
  ring

private theorem covariance_square_eq
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ}
    (hX : ∀ i, MemLp (X i) 4 P)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j)
    (hfourth : ∀ i j, (∫ ω, X i ω ^ 2 * X j ω ^ 2 ∂P) =
      C i i * C j j + 2 * C i j ^ 2) (i j : I) :
    cov[fun ω => X i ω ^ 2, fun ω => X j ω ^ 2; P] = 2 * C i j ^ 2 := by
  rw [covariance_eq_sub (square_memLp_two hX i) (square_memLp_two hX j)]
  change (∫ ω, X i ω ^ 2 * X j ω ^ 2 ∂P) -
      (∫ ω, X i ω ^ 2 ∂P) * (∫ ω, X j ω ^ 2 ∂P) = _
  rw [hfourth i j, square_integral_eq_diag hsecond i,
    square_integral_eq_diag hsecond j]
  ring

private theorem covariance_square_linear_eq_zero
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ}
    (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j)
    (hthird : ∀ i j, (∫ ω, X i ω ^ 2 * X j ω ∂P) = 0)
    (b : I → ℝ) (i j : I) :
    cov[fun ω => X i ω ^ 2, fun ω => b j * X j ω; P] = 0 := by
  rw [covariance_const_mul_right]
  rw [covariance_eq_sub (square_memLp_two hX i) (coordinate_memLp_two hX j)]
  change b j * ((∫ ω, X i ω ^ 2 * X j ω ∂P) -
      (∫ ω, X i ω ^ 2 ∂P) * (∫ ω, X j ω ∂P)) = 0
  rw [hthird i j, square_integral_eq_diag hsecond i, hmean j]
  ring

private theorem squareSum_integral
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ}
    (hX : ∀ i, MemLp (X i) 4 P)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j) :
    (∫ ω, squareSum X ω ∂P) = ∑ i, C i i := by
  unfold squareSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact square_integral_eq_diag hsecond i
  · intro i hi
    exact (square_memLp_two hX i).integrable one_le_two

private theorem linearSum_integral_zero
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} (b : I → ℝ)
    (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0) :
    (∫ ω, linearSum b X ω ∂P) = 0 := by
  unfold linearSum
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, hmean, mul_zero]
    simp
  · intro i hi
    exact (linear_memLp_two b hX i).integrable one_le_two

/-- Expectation of a finite shifted quadratic statistic from the exact
second-moment identities. -/
theorem noncentralSquareSum_integral
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ} (b : I → ℝ)
    (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j) :
    (∫ ω, noncentralSquareSum X b ω ∂P) = ∑ i, C i i + ∑ i, b i ^ 2 := by
  rw [noncentralSquareSum_decomposition]
  have hQ := (squareSum_memLp_two hX).integrable one_le_two
  have hL := (linearSum_memLp_two b hX).integrable one_le_two
  let c : ℝ := ∑ i, b i ^ 2
  have hdecomp :
      (fun ω => squareSum X ω + 2 * linearSum b X ω + c) =
        squareSum X + ((fun ω => 2 * linearSum b X ω) + fun _ => c) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  change (∫ ω, squareSum X ω + 2 * linearSum b X ω + c ∂P) = _
  rw [hdecomp]
  calc
    integral P (squareSum X + ((fun ω => 2 * linearSum b X ω) + fun _ => c)) =
        integral P (squareSum X) +
          integral P ((fun ω => 2 * linearSum b X ω) + fun _ => c) :=
      integral_add hQ ((hL.const_mul 2).add (integrable_const c))
    _ = integral P (squareSum X) +
          (integral P (fun ω => 2 * linearSum b X ω) + integral P (fun _ => c)) := by
      apply congrArg (fun r : ℝ => integral P (squareSum X) + r)
      convert integral_add (hL.const_mul 2) (integrable_const c) using 1
    _ = ∑ i, C i i + ∑ i, b i ^ 2 := by
      rw [integral_const_mul, squareSum_integral hX hsecond,
        linearSum_integral_zero b hX hmean]
      simp [c]

private theorem squareSum_variance
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ}
    (hX : ∀ i, MemLp (X i) 4 P)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j)
    (hfourth : ∀ i j, (∫ ω, X i ω ^ 2 * X j ω ^ 2 ∂P) =
      C i i * C j j + 2 * C i j ^ 2) :
    Var[squareSum X; P] = 2 * ∑ i, ∑ j, C i j ^ 2 := by
  unfold squareSum
  rw [variance_fun_sum]
  · simp_rw [covariance_square_eq hX hsecond hfourth]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  · intro i
    exact square_memLp_two hX i

private theorem linearSum_variance
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ} (b : I → ℝ)
    (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j) :
    Var[linearSum b X; P] = ∑ i, ∑ j, b i * C i j * b j := by
  unfold linearSum
  rw [variance_fun_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_coordinate_eq hX hmean hsecond]
    ring
  · intro i
    exact linear_memLp_two b hX i

private theorem covariance_squareSum_linearSum_zero
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ} (b : I → ℝ)
    (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j)
    (hthird : ∀ i j, (∫ ω, X i ω ^ 2 * X j ω ∂P) = 0) :
    cov[squareSum X, linearSum b X; P] = 0 := by
  unfold squareSum linearSum
  rw [covariance_fun_sum_fun_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact covariance_square_linear_eq_zero hX hmean hsecond hthird b i j
  · intro i
    exact square_memLp_two hX i
  · intro j
    exact linear_memLp_two b hX j

/-- Variance of a finite shifted quadratic statistic from the exact centered
third and fourth Wick identities. -/
theorem noncentralSquareSum_variance
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ} (b : I → ℝ)
    (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j)
    (hthird : ∀ i j, (∫ ω, X i ω ^ 2 * X j ω ∂P) = 0)
    (hfourth : ∀ i j, (∫ ω, X i ω ^ 2 * X j ω ^ 2 ∂P) =
      C i i * C j j + 2 * C i j ^ 2) :
    Var[noncentralSquareSum X b; P] =
      2 * ∑ i, ∑ j, C i j ^ 2 +
        4 * ∑ i, ∑ j, b i * C i j * b j := by
  rw [noncentralSquareSum_decomposition]
  have hQ := squareSum_memLp_two hX
  have hL := linearSum_memLp_two b hX
  let c : ℝ := ∑ i, b i ^ 2
  have hdecomp :
      (fun ω => squareSum X ω + 2 * linearSum b X ω + c) =
        (squareSum X + fun ω => 2 * linearSum b X ω) + fun _ => c := by
    funext ω
    simp only [Pi.add_apply]
  change Var[fun ω => squareSum X ω + 2 * linearSum b X ω + c; P] = _
  rw [hdecomp]
  have hvar_scaled : Var[fun ω => 2 * linearSum b X ω; P] =
      4 * Var[linearSum b X; P] := by
    calc
      Var[fun ω => 2 * linearSum b X ω; P] =
          2 ^ 2 * Var[linearSum b X; P] := variance_const_mul 2 (linearSum b X) P
      _ = 4 * Var[linearSum b X; P] := by ring
  have hcov_scaled : cov[squareSum X, fun ω => 2 * linearSum b X ω; P] = 0 := by
    rw [covariance_const_mul_right,
      covariance_squareSum_linearSum_zero b hX hmean hsecond hthird]
    ring
  have hvar_const :
      Var[(squareSum X + (fun ω => 2 * linearSum b X ω)) + (fun _ => c); P] =
        Var[squareSum X + (fun ω => 2 * linearSum b X ω); P] := by
    have heq :
        (squareSum X + (fun ω => 2 * linearSum b X ω)) + (fun _ => c) =
          (fun ω => (squareSum X + (fun x => 2 * linearSum b X x)) ω + c) := by
      funext ω
      simp only [Pi.add_apply]
    rw [heq]
    exact variance_add_const (hQ.add (hL.const_mul 2)).aestronglyMeasurable c
  rw [hvar_const,
    variance_add hQ (hL.const_mul 2), hcov_scaled, hvar_scaled,
    squareSum_variance hX hsecond hfourth, linearSum_variance b hX hmean hsecond]
  ring

end FiniteQuadratic

/-! ## Matrix normal form -/

section MatrixNormalForm

theorem trace_eq_sum_diag {I : Type*} [Fintype I] (C : Matrix I I ℝ) :
    C.trace = ∑ i, C i i := rfl

private theorem trace_mul_eq_double_sum {I : Type*} [Fintype I] (C : Matrix I I ℝ) :
    (C * C).trace = ∑ i, ∑ j, C i j * C j i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem trace_square_eq_sum_sq {I : Type*} [Fintype I]
    {C : Matrix I I ℝ} (hC : C.IsHermitian) :
    (C * C).trace = ∑ i, ∑ j, C i j ^ 2 := by
  rw [trace_mul_eq_double_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsymm : C j i = C i j := by
    simpa using (hC.apply i j)
  rw [hsymm]
  ring

theorem quadraticForm_eq_double_sum {I : Type*} [Fintype I]
    (C : Matrix I I ℝ) (b : I → ℝ) :
    quadraticForm C b = ∑ i, ∑ j, b i * C i j * b j := by
  rw [quadraticForm_eq_dotProduct_mulVec]
  simp only [dotProduct, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem dotProduct_self_eq_sum_sq {I : Type*} [Fintype I] (b : I → ℝ) :
    b ⬝ᵥ b = ∑ i, b i ^ 2 := by
  simp only [dotProduct, pow_two]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Matrix-trace form of the exact finite quadratic expectation. -/
theorem noncentralSquareSum_integral_trace
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ} (b : I → ℝ)
    (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j) :
    (∫ ω, noncentralSquareSum X b ω ∂P) = C.trace + b ⬝ᵥ b := by
  rw [noncentralSquareSum_integral b hX hmean hsecond,
    trace_eq_sum_diag, dotProduct_self_eq_sum_sq]

/-- Matrix-trace form of the exact finite noncentral Wick variance identity. -/
theorem noncentralSquareSum_variance_trace
    {I : Type*} [Fintype I] [IsProbabilityMeasure P]
    {X : I → Ω → ℝ} {C : Matrix I I ℝ} (b : I → ℝ)
    (hC : C.IsHermitian) (hX : ∀ i, MemLp (X i) 4 P)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hsecond : ∀ i j, (∫ ω, X i ω * X j ω ∂P) = C i j)
    (hthird : ∀ i j, (∫ ω, X i ω ^ 2 * X j ω ∂P) = 0)
    (hfourth : ∀ i j, (∫ ω, X i ω ^ 2 * X j ω ^ 2 ∂P) =
      C i i * C j j + 2 * C i j ^ 2) :
    Var[noncentralSquareSum X b; P] =
      2 * (C * C).trace + 4 * quadraticForm C b := by
  rw [noncentralSquareSum_variance b hX hmean hsecond hthird hfourth,
    trace_square_eq_sum_sq hC, quadraticForm_eq_double_sum]

end MatrixNormalForm

/-! ## Finite Gaussian-score specialization

This section discharges the coordinate moment hypotheses above for a finite
family of deterministic linear scores of one centered multivariate Gaussian
vector.  It is a finite-dimensional bridge only: it does not assert the
manuscript's residual construction or any asymptotic conclusion. -/

section GaussianScore

variable {O I : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace O]

/-- The covariance bilinear form of two deterministic finite score weights. -/
@[expose]
noncomputable def scoreBilinear (C : Matrix I I ℝ) (u v : I → ℝ) : ℝ :=
  u ⬝ᵥ (C *ᵥ v)

private theorem scoreBilinear_swap {C : Matrix I I ℝ} (hC : C.IsHermitian)
    (u v : I → ℝ) :
    scoreBilinear C u v = scoreBilinear C v u := by
  classical
  rw [scoreBilinear, scoreBilinear]
  simp only [dotProduct, Matrix.mulVec]
  calc
    (∑ i, u i * ∑ j, C i j * v j) =
        ∑ i, ∑ j, u i * (C i j * v j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, u i * (C i j * v j) := Finset.sum_comm
    _ = ∑ j, ∑ i, v j * (C j i * u i) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          have hs : C i j = C j i := by
            simpa using (hC.apply i j).symm
          rw [hs]
          ring
    _ = ∑ j, v j * ∑ i, C j i * u i := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]

/-- Polarization identity for the finite real quadratic form.  This is an
already-proved deterministic helper made public for scalar-score assembly. -/
theorem quadraticForm_add {C : Matrix I I ℝ} (hC : C.IsHermitian)
    (u v : I → ℝ) :
    quadraticForm C (u + v) =
      quadraticForm C u + quadraticForm C v + 2 * scoreBilinear C u v := by
  classical
  rw [quadraticForm_eq_dotProduct_mulVec,
    quadraticForm_eq_dotProduct_mulVec,
    quadraticForm_eq_dotProduct_mulVec]
  simp only [dotProduct, Matrix.mulVec, Pi.add_apply]
  change
    (∑ i, (u i + v i) * ∑ j, C i j * (u j + v j)) =
      (∑ i, u i * ∑ j, C i j * u j) +
        (∑ i, v i * ∑ j, C i j * v j) + 2 * scoreBilinear C u v
  have hinner : ∀ i, (∑ j, C i j * (u j + v j)) =
      (∑ j, C i j * u j) + (∑ j, C i j * v j) := by
    intro i
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
  rw [show (∑ i, (u i + v i) * ∑ j, C i j * (u j + v j)) =
      (∑ i, u i * ∑ j, C i j * u j) +
      (∑ i, u i * ∑ j, C i j * v j) +
      (∑ i, v i * ∑ j, C i j * u j) +
      (∑ i, v i * ∑ j, C i j * v j) by
        simp_rw [hinner, mul_add, add_mul]
        repeat' rw [Finset.sum_add_distrib]
        ring]
  have hcross :
      (∑ x, u x * ∑ x_1, C x x_1 * v x_1) =
        (∑ x, v x * ∑ x_1, C x x_1 * u x_1) := by
    exact scoreBilinear_swap hC u v
  rw [← hcross]
  change _ = _ + _ + 2 * (∑ i, u i * ∑ j, C i j * v j)
  ring

private theorem quadraticForm_neg (C : Matrix I I ℝ) (v : I → ℝ) :
    quadraticForm C (-v) = quadraticForm C v := by
  simp [quadraticForm_eq_dotProduct_mulVec, dotProduct, Matrix.mulVec]

private theorem scoreBilinear_neg_right (C : Matrix I I ℝ) (u v : I → ℝ) :
    scoreBilinear C u (-v) = -scoreBilinear C u v := by
  rw [scoreBilinear, scoreBilinear, Matrix.mulVec_neg, dotProduct_neg]

private theorem quadraticForm_sub {C : Matrix I I ℝ} (hC : C.IsHermitian)
    (u v : I → ℝ) :
    quadraticForm C (u - v) =
      quadraticForm C u + quadraticForm C v - 2 * scoreBilinear C u v := by
  rw [sub_eq_add_neg, quadraticForm_add hC u (-v), quadraticForm_neg,
    scoreBilinear_neg_right]
  ring

private theorem score_add (u v : I → ℝ) (Z : O → EuclideanSpace ℝ I) :
    InfillGLSLean.finiteGaussianScore (u + v) Z =
      fun ω => InfillGLSLean.finiteGaussianScore u Z ω +
        InfillGLSLean.finiteGaussianScore v Z ω := by
  funext ω
  simp only [InfillGLSLean.finiteGaussianScore, Pi.add_apply]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

private theorem score_sub (u v : I → ℝ) (Z : O → EuclideanSpace ℝ I) :
    InfillGLSLean.finiteGaussianScore (u - v) Z =
      fun ω => InfillGLSLean.finiteGaussianScore u Z ω -
        InfillGLSLean.finiteGaussianScore v Z ω := by
  funext ω
  simp only [InfillGLSLean.finiteGaussianScore, Pi.sub_apply]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]

/-- Covariance of two deterministic scores of a centered finite Gaussian
vector. -/
theorem finiteGaussianScore_covariance
    {P : Measure O} {Z : O → EuclideanSpace ℝ I} {C : Matrix I I ℝ}
    (hZ : HasLaw Z (multivariateGaussian 0 C) P) (hC : C.PosSemidef)
    (u v : I → ℝ) :
    cov[InfillGLSLean.finiteGaussianScore u Z,
      InfillGLSLean.finiteGaussianScore v Z; P] = scoreBilinear C u v := by
  have hu : InfillGLSLean.finiteGaussianScore u Z =
      fun ω => (innerSL ℝ (WithLp.toLp 2 u)) (Z ω) := by
    funext ω
    exact InfillGLSLean.finiteGaussianScore_eq_inner u Z ω
  have hv : InfillGLSLean.finiteGaussianScore v Z =
      fun ω => (innerSL ℝ (WithLp.toLp 2 v)) (Z ω) := by
    funext ω
    exact InfillGLSLean.finiteGaussianScore_eq_inner v Z ω
  rw [hu, hv]
  calc
    cov[fun ω => (innerSL ℝ (WithLp.toLp 2 u)) (Z ω),
        fun ω => (innerSL ℝ (WithLp.toLp 2 v)) (Z ω); P] =
        cov[fun x => (innerSL ℝ (WithLp.toLp 2 u)) x,
          fun x => (innerSL ℝ (WithLp.toLp 2 v)) x;
          multivariateGaussian 0 C] :=
      hZ.covariance_fun_comp
        ((innerSL ℝ (WithLp.toLp 2 u)).continuous.aemeasurable)
        ((innerSL ℝ (WithLp.toLp 2 v)).continuous.aemeasurable)
    _ = covarianceBilin (multivariateGaussian 0 C)
          (WithLp.toLp 2 u) (WithLp.toLp 2 v) :=
      (covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id
        (WithLp.toLp 2 u) (WithLp.toLp 2 v)).symm
    _ = scoreBilinear C u v := by
      simpa [scoreBilinear] using
        covarianceBilin_multivariateGaussian hC
          (WithLp.toLp 2 u) (WithLp.toLp 2 v)

private theorem finiteGaussianScore_second_integral
    {P : Measure O} {Z : O → EuclideanSpace ℝ I} {C : Matrix I I ℝ}
    (hZ : HasLaw Z (multivariateGaussian 0 C) P) (hC : C.PosSemidef)
    (u v : I → ℝ) :
    (∫ ω, InfillGLSLean.finiteGaussianScore u Z ω *
      InfillGLSLean.finiteGaussianScore v Z ω ∂P) = scoreBilinear C u v := by
  letI : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  have hu : HasLaw (InfillGLSLean.finiteGaussianScore u Z)
      (gaussianReal 0 (quadraticForm C u).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hv : HasLaw (InfillGLSLean.finiteGaussianScore v Z)
      (gaussianReal 0 (quadraticForm C v).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hu2 : MemLp (InfillGLSLean.finiteGaussianScore u Z) 2 P :=
    hu.memLp (memLp_id_gaussianReal' 2 (by norm_num))
  have hv2 : MemLp (InfillGLSLean.finiteGaussianScore v Z) 2 P :=
    hv.memLp (memLp_id_gaussianReal' 2 (by norm_num))
  have hcov := finiteGaussianScore_covariance hZ hC u v
  rw [covariance_eq_sub hu2 hv2, InfillGLSLean.finiteGaussianScore_mean hZ,
    InfillGLSLean.finiteGaussianScore_mean hZ] at hcov
  simpa only [Pi.mul_apply, mul_zero, sub_zero] using hcov

private theorem finiteGaussianScore_third_integral_zero
    {P : Measure O} {Z : O → EuclideanSpace ℝ I} {C : Matrix I I ℝ}
    (hZ : HasLaw Z (multivariateGaussian 0 C) P) (hC : C.PosSemidef)
    (u v : I → ℝ) :
    (∫ ω, InfillGLSLean.finiteGaussianScore u Z ω ^ 2 *
      InfillGLSLean.finiteGaussianScore v Z ω ∂P) = 0 := by
  have hu : HasLaw (InfillGLSLean.finiteGaussianScore u Z)
      (gaussianReal 0 (quadraticForm C u).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hv : HasLaw (InfillGLSLean.finiteGaussianScore v Z)
      (gaussianReal 0 (quadraticForm C v).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hplus0 : HasLaw (InfillGLSLean.finiteGaussianScore (u + v) Z)
      (gaussianReal 0 (quadraticForm C (u + v)).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hminus0 : HasLaw (InfillGLSLean.finiteGaussianScore (u - v) Z)
      (gaussianReal 0 (quadraticForm C (u - v)).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hplus : HasLaw
      (fun ω => InfillGLSLean.finiteGaussianScore u Z ω +
        InfillGLSLean.finiteGaussianScore v Z ω)
      (gaussianReal 0 (quadraticForm C (u + v)).toNNReal) P := by
    rw [← score_add u v Z]
    exact hplus0
  have hminus : HasLaw
      (fun ω => InfillGLSLean.finiteGaussianScore u Z ω -
        InfillGLSLean.finiteGaussianScore v Z ω)
      (gaussianReal 0 (quadraticForm C (u - v)).toNNReal) P := by
    rw [← score_sub u v Z]
    exact hminus0
  exact centered_gaussian_square_mul_integral_zero hplus hminus hv

private theorem finiteGaussianScore_fourth_integral
    {P : Measure O} {Z : O → EuclideanSpace ℝ I} {C : Matrix I I ℝ}
    (hZ : HasLaw Z (multivariateGaussian 0 C) P) (hC : C.PosSemidef)
    (u v : I → ℝ) :
    (∫ ω, InfillGLSLean.finiteGaussianScore u Z ω ^ 2 *
      InfillGLSLean.finiteGaussianScore v Z ω ^ 2 ∂P) =
      scoreBilinear C u u * scoreBilinear C v v +
        2 * scoreBilinear C u v ^ 2 := by
  have hu : HasLaw (InfillGLSLean.finiteGaussianScore u Z)
      (gaussianReal 0 (quadraticForm C u).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hv : HasLaw (InfillGLSLean.finiteGaussianScore v Z)
      (gaussianReal 0 (quadraticForm C v).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hplus0 : HasLaw (InfillGLSLean.finiteGaussianScore (u + v) Z)
      (gaussianReal 0 (quadraticForm C (u + v)).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hminus0 : HasLaw (InfillGLSLean.finiteGaussianScore (u - v) Z)
      (gaussianReal 0 (quadraticForm C (u - v)).toNNReal) P :=
    InfillGLSLean.finiteGaussianScore_hasLaw hZ hC
  have hplus : HasLaw
      (fun ω => InfillGLSLean.finiteGaussianScore u Z ω +
        InfillGLSLean.finiteGaussianScore v Z ω)
      (gaussianReal 0 (quadraticForm C (u + v)).toNNReal) P := by
    rw [← score_add u v Z]
    exact hplus0
  have hminus : HasLaw
      (fun ω => InfillGLSLean.finiteGaussianScore u Z ω -
        InfillGLSLean.finiteGaussianScore v Z ω)
      (gaussianReal 0 (quadraticForm C (u - v)).toNNReal) P := by
    rw [← score_sub u v Z]
    exact hminus0
  have hplusVar : ((quadraticForm C (u + v)).toNNReal : ℝ) =
      ((quadraticForm C u).toNNReal : ℝ) +
        ((quadraticForm C v).toNNReal : ℝ) + 2 * scoreBilinear C u v := by
    simpa only [InfillGLSLean.finiteGaussianScore_varianceParameter_coe hC]
      using quadraticForm_add hC.isHermitian u v
  have hminusVar : ((quadraticForm C (u - v)).toNNReal : ℝ) =
      ((quadraticForm C u).toNNReal : ℝ) +
        ((quadraticForm C v).toNNReal : ℝ) - 2 * scoreBilinear C u v := by
    simpa only [InfillGLSLean.finiteGaussianScore_varianceParameter_coe hC]
      using quadraticForm_sub hC.isHermitian u v
  have hwick := centered_gaussian_pair_wick_fourth hu hv hplus hminus hplusVar hminusVar
  have huVar : ((quadraticForm C u).toNNReal : ℝ) = scoreBilinear C u u := by
    rw [InfillGLSLean.finiteGaussianScore_varianceParameter_coe hC]
    rfl
  have hvVar : ((quadraticForm C v).toNNReal : ℝ) = scoreBilinear C v v := by
    rw [InfillGLSLean.finiteGaussianScore_varianceParameter_coe hC]
    rfl
  rw [huVar, hvVar] at hwick
  exact hwick

/-- Covariance matrix of a finite family of deterministic scores. -/
noncomputable def scoreCovariance {J : Type*} (C : Matrix I I ℝ)
    (weights : J → I → ℝ) : Matrix J J ℝ :=
  fun j k => scoreBilinear C (weights j) (weights k)

private theorem scoreCovariance_isHermitian {J : Type*} (C : Matrix I I ℝ)
    (hC : C.IsHermitian) (weights : J → I → ℝ) :
    (scoreCovariance C weights).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext j k
  simp only [scoreCovariance, Matrix.transpose_apply]
  exact (scoreBilinear_swap hC (weights j) (weights k)).symm

/-- Exact finite noncentral quadratic-form expectation for any finite family
of deterministic scores of one centered multivariate Gaussian vector. -/
theorem finiteGaussianScore_noncentralSquareSum_integral_trace
    {J : Type*} [Fintype J] {P : Measure O}
    {Z : O → EuclideanSpace ℝ I} {C : Matrix I I ℝ}
    (hZ : HasLaw Z (multivariateGaussian 0 C) P) (hC : C.PosSemidef)
    (weights : J → I → ℝ) (b : J → ℝ) :
    (∫ ω, noncentralSquareSum
      (fun j => InfillGLSLean.finiteGaussianScore (weights j) Z) b ω ∂P) =
      (scoreCovariance C weights).trace + b ⬝ᵥ b := by
  classical
  letI : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  let X : J → O → ℝ := fun j => InfillGLSLean.finiteGaussianScore (weights j) Z
  let S : Matrix J J ℝ := scoreCovariance C weights
  have hX : ∀ j, MemLp (X j) 4 P := by
    intro j
    have hj := InfillGLSLean.finiteGaussianScore_hasLaw
      (weight := weights j) hZ hC
    simpa [X] using hj.memLp (memLp_id_gaussianReal' 4 (by norm_num))
  have hmean : ∀ j, (∫ ω, X j ω ∂P) = 0 := by
    intro j
    simpa [X] using InfillGLSLean.finiteGaussianScore_mean
      (weight := weights j) hZ
  have hsecond : ∀ j k, (∫ ω, X j ω * X k ω ∂P) = S j k := by
    intro j k
    simpa [X, S, scoreCovariance] using
      finiteGaussianScore_second_integral hZ hC (weights j) (weights k)
  simpa [X, S] using noncentralSquareSum_integral_trace b hX hmean hsecond

/-- Exact finite noncentral quadratic-form variance for any finite family of
deterministic scores of one centered multivariate Gaussian vector. -/
theorem finiteGaussianScore_noncentralSquareSum_variance_trace
    {J : Type*} [Fintype J] {P : Measure O}
    {Z : O → EuclideanSpace ℝ I} {C : Matrix I I ℝ}
    (hZ : HasLaw Z (multivariateGaussian 0 C) P) (hC : C.PosSemidef)
    (weights : J → I → ℝ) (b : J → ℝ) :
    Var[noncentralSquareSum
      (fun j => InfillGLSLean.finiteGaussianScore (weights j) Z) b; P] =
      2 * ((scoreCovariance C weights) * (scoreCovariance C weights)).trace +
        4 * quadraticForm (scoreCovariance C weights) b := by
  classical
  letI : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  let X : J → O → ℝ := fun j => InfillGLSLean.finiteGaussianScore (weights j) Z
  let S : Matrix J J ℝ := scoreCovariance C weights
  have hX : ∀ j, MemLp (X j) 4 P := by
    intro j
    have hj := InfillGLSLean.finiteGaussianScore_hasLaw
      (weight := weights j) hZ hC
    simpa [X] using hj.memLp (memLp_id_gaussianReal' 4 (by norm_num))
  have hmean : ∀ j, (∫ ω, X j ω ∂P) = 0 := by
    intro j
    simpa [X] using InfillGLSLean.finiteGaussianScore_mean
      (weight := weights j) hZ
  have hsecond : ∀ j k, (∫ ω, X j ω * X k ω ∂P) = S j k := by
    intro j k
    simpa [X, S, scoreCovariance] using
      finiteGaussianScore_second_integral hZ hC (weights j) (weights k)
  have hthird : ∀ j k, (∫ ω, X j ω ^ 2 * X k ω ∂P) = 0 := by
    intro j k
    simpa [X] using
      finiteGaussianScore_third_integral_zero hZ hC (weights j) (weights k)
  have hfourth : ∀ j k, (∫ ω, X j ω ^ 2 * X k ω ^ 2 ∂P) =
      S j j * S k k + 2 * S j k ^ 2 := by
    intro j k
    simpa [X, S, scoreCovariance] using
      finiteGaussianScore_fourth_integral hZ hC (weights j) (weights k)
  have hS : S.IsHermitian := by
    simpa [S] using scoreCovariance_isHermitian C hC.isHermitian weights
  simpa [X, S] using
    noncentralSquareSum_variance_trace b hS hX hmean hsecond hthird hfourth

/-! ### Orthogonal-projection normal form

The following deterministic rewrites connect the covariance matrix of the
row-score family to the notation used literally in Appendix `app:scale`. -/

private theorem scoreCovariance_rows_eq_projectedCovariance
    (P Γ : Matrix I I ℝ) (hP : P.IsSymm) :
    scoreCovariance Γ (fun i => P i) = P * Γ * P := by
  ext i j
  simp only [scoreCovariance, scoreBilinear, dotProduct, Matrix.mulVec,
    Matrix.mul_apply]
  calc
    (∑ a, P i a * ∑ b, Γ a b * P j b) =
        ∑ a, ∑ b, P i a * (Γ a b * P j b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
    _ = ∑ b, ∑ a, P i a * (Γ a b * P j b) := Finset.sum_comm
    _ = ∑ b, ∑ a, (P i a * Γ a b) * P b j := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro a ha
          have hsymm : P j b = P b j := by
            simpa only [Matrix.transpose_apply] using
              (congrFun (congrFun hP.eq j) b).symm
          rw [hsymm]
          ring
    _ = ∑ b, (∑ a, P i a * Γ a b) * P b j := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul]

private theorem trace_projectedCovariance
    (P Γ : Matrix I I ℝ) (hP : P * P = P) :
    (P * Γ * P).trace = (P * Γ).trace := by
  calc
    (P * Γ * P).trace = ((P * Γ) * P).trace := rfl
    _ = (P * (P * Γ)).trace := Matrix.trace_mul_comm _ _
    _ = ((P * P) * Γ).trace := by rw [Matrix.mul_assoc]
    _ = (P * Γ).trace := by rw [hP]

private theorem trace_square_projectedCovariance
    (P Γ : Matrix I I ℝ) (hP : P * P = P) :
    ((P * Γ * P) * (P * Γ * P)).trace = (P * Γ * P * Γ).trace := by
  have hs : (P * Γ * P) * (P * Γ * P) = P * (Γ * (P * (Γ * P))) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hP]
  rw [hs]
  calc
    (P * (Γ * (P * (Γ * P)))).trace =
        ((P * (Γ * (P * Γ))) * P).trace := by simp only [Matrix.mul_assoc]
    _ = (P * (P * (Γ * (P * Γ)))).trace := Matrix.trace_mul_comm _ _
    _ = ((P * P) * (Γ * (P * Γ))).trace := by rw [Matrix.mul_assoc]
    _ = (P * (Γ * (P * Γ))).trace := by rw [hP]
    _ = (P * Γ * P * Γ).trace := by simp only [Matrix.mul_assoc]

private theorem quadraticForm_projectedCovariance
    (P Γ : Matrix I I ℝ) (hP : P.IsSymm) (b : I → ℝ)
    (hb : P *ᵥ b = b) :
    quadraticForm (P * Γ * P) b = quadraticForm Γ b := by
  rw [quadraticForm_eq_dotProduct_mulVec,
    quadraticForm_eq_dotProduct_mulVec]
  calc
    b ⬝ᵥ (P * Γ * P) *ᵥ b = b ⬝ᵥ P *ᵥ (Γ *ᵥ (P *ᵥ b)) := by
      congr 1
      rw [← Matrix.mulVec_mulVec b (P * Γ) P,
        ← Matrix.mulVec_mulVec (P *ᵥ b) P Γ]
    _ = b ⬝ᵥ P *ᵥ (Γ *ᵥ b) := by rw [hb]
    _ = (Γ *ᵥ b) ⬝ᵥ (P *ᵥ b) := hP.dotProduct_mulVec_comm
    _ = (P *ᵥ b) ⬝ᵥ (Γ *ᵥ b) := dotProduct_comm _ _
    _ = b ⬝ᵥ (Γ *ᵥ b) := by rw [hb]

private theorem projected_noncentralSquareSum_eq
    (P : Matrix I I ℝ) (b : I → ℝ) (Z : O → EuclideanSpace ℝ I) :
    (fun ω => ∑ i, (b i + (P *ᵥ (Z ω).ofLp) i) ^ 2) =
      noncentralSquareSum
        (fun j => InfillGLSLean.finiteGaussianScore (P j) Z) b := by
  funext ω
  unfold noncentralSquareSum
  apply Finset.sum_congr rfl
  intro i hi
  have hcoordinate : InfillGLSLean.finiteGaussianScore (P i) Z ω =
      (P *ᵥ (Z ω).ofLp) i := by
    simp only [InfillGLSLean.finiteGaussianScore, Matrix.mulVec, dotProduct]
  change (b i + (P *ᵥ (Z ω).ofLp) i) ^ 2 =
    (InfillGLSLean.finiteGaussianScore (P i) Z ω + b i) ^ 2
  rw [hcoordinate]
  ring

/- Keep the original local public boundary for the two projection endpoints. -/
public section

/-- The Appendix `app:scale` finite expectation identity, written for a
centered Gaussian vector `Z`, an orthogonal projection `P`, and the residual
`b + P Z`.  The coordinate dot product is the finite Euclidean norm squared. -/
theorem projectedGaussian_noncentralSquareSum_integral
    {P0 : Measure O} {Z : O → EuclideanSpace ℝ I}
    {Γ P : Matrix I I ℝ}
    (hZ : HasLaw Z (multivariateGaussian 0 Γ) P0) (hΓ : Γ.PosSemidef)
    (hP : P.IsSymm) (hPidempotent : P * P = P) (b : I → ℝ) :
    (∫ ω, ∑ i, (b i + (P *ᵥ (Z ω).ofLp) i) ^ 2 ∂P0) =
      (P * Γ).trace + b ⬝ᵥ b := by
  have hscore := finiteGaussianScore_noncentralSquareSum_integral_trace
    (P := P0) hZ hΓ (fun i => P i) b
  have hcov : scoreCovariance Γ (fun i => P i) = P * Γ * P :=
    scoreCovariance_rows_eq_projectedCovariance P Γ hP
  calc
    (∫ ω, ∑ i, (b i + (P *ᵥ (Z ω).ofLp) i) ^ 2 ∂P0) =
        (∫ ω, noncentralSquareSum
          (fun j => InfillGLSLean.finiteGaussianScore (P j) Z) b ω ∂P0) := by
          rw [projected_noncentralSquareSum_eq P b Z]
    _ = (scoreCovariance Γ (fun i => P i)).trace + b ⬝ᵥ b := hscore
    _ = (P * Γ).trace + b ⬝ᵥ b := by
      rw [hcov, trace_projectedCovariance P Γ hPidempotent]

/-- The Appendix `app:scale` finite variance identity, written for a centered
Gaussian vector `Z`, an orthogonal projection `P`, and a projected mean
`b = P b`. -/
theorem projectedGaussian_noncentralSquareSum_variance
    {P0 : Measure O} {Z : O → EuclideanSpace ℝ I}
    {Γ P : Matrix I I ℝ}
    (hZ : HasLaw Z (multivariateGaussian 0 Γ) P0) (hΓ : Γ.PosSemidef)
    (hP : P.IsSymm) (hPidempotent : P * P = P) (b : I → ℝ)
    (hb : P *ᵥ b = b) :
    Var[fun ω => ∑ i, (b i + (P *ᵥ (Z ω).ofLp) i) ^ 2; P0] =
      2 * (P * Γ * P * Γ).trace + 4 * quadraticForm Γ b := by
  have hscore := finiteGaussianScore_noncentralSquareSum_variance_trace
    (P := P0) hZ hΓ (fun i => P i) b
  have hcov : scoreCovariance Γ (fun i => P i) = P * Γ * P :=
    scoreCovariance_rows_eq_projectedCovariance P Γ hP
  have htrace : ((P * Γ * P) * (P * Γ * P)).trace =
      (P * Γ * P * Γ).trace :=
    trace_square_projectedCovariance P Γ hPidempotent
  have hquadratic : quadraticForm (P * Γ * P) b = quadraticForm Γ b :=
    quadraticForm_projectedCovariance P Γ hP b hb
  rw [hcov, htrace, hquadratic] at hscore
  rw [projected_noncentralSquareSum_eq P b Z]
  exact hscore

end

end GaussianScore

end

end InfillGLSLean.FiniteWickBridge
