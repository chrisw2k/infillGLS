module

public import InfillGLSLean.MatrixCovarianceOrder
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic.Ring

/-!
# Finite random GLS score covariance

This module supplies the probability bridge for the finite covariance-order
calculation.  It identifies the variance of a weighted random-error score
with the covariance quadratic form, and therefore transfers a finite
Loewner-order covariance bound into an actual variance bound.  It is not a
claim about a spatial process or an asymptotic regime; those hypotheses must
be supplied by the layer that constructs the finite error vector.
-/

public section

namespace InfillGLSLean

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] [Fintype ι]

/-- The finite random linear score with deterministic weights. -/
@[expose]
noncomputable def finiteWeightedScore (weight : ι → ℝ)
    (error : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, weight i * error i ω

omit [MeasurableSpace Ω] in
/-- Public pointwise expansion of a finite weighted score. -/
@[simp]
theorem finiteWeightedScore_apply (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (ω : Ω) :
    finiteWeightedScore weight error ω = ∑ i, weight i * error i ω :=
  rfl

/-- The finite covariance matrix of an error vector. -/
@[expose]
noncomputable def finiteErrorCovariance (error : ι → Ω → ℝ)
    (μ : Measure Ω) : Matrix ι ι ℝ :=
  fun i j => cov[error i, error j; μ]

omit [Fintype ι] in
/-- Public entrywise expansion of the finite error covariance matrix. -/
@[simp]
theorem finiteErrorCovariance_apply (error : ι → Ω → ℝ)
    (μ : Measure Ω) (i j : ι) :
    finiteErrorCovariance error μ i j = cov[error i, error j; μ] :=
  rfl

omit [IsFiniteMeasure μ] in
/-- Coordinatewise square integrability gives square integrability of the
finite weighted score. -/
theorem memLp_finiteWeightedScore
    (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ) :
    MemLp (finiteWeightedScore weight error) 2 μ := by
  change MemLp (fun ω => ∑ i, weight i * error i ω) 2 μ
  exact memLp_finsetSum Finset.univ (fun i _ => (herror i).const_mul (weight i))

/-- If every coordinate of a finite error vector has mean zero, so does every
deterministic weighted score. -/
theorem integral_finiteWeightedScore_eq_zero
    (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ)
    (hcentered : ∀ i, μ[error i] = 0) :
    μ[finiteWeightedScore weight error] = 0 := by
  unfold finiteWeightedScore
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, hcentered, mul_zero]
    simp
  · intro i hi
    exact ((herror i).const_mul (weight i)).integrable one_le_two

/-- The variance of a finite weighted score is exactly its covariance
quadratic form. -/
theorem variance_finiteWeightedScore_eq_quadraticForm
    (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ) :
    Var[finiteWeightedScore weight error; μ] =
      quadraticForm (finiteErrorCovariance error μ) weight := by
  unfold finiteWeightedScore
  rw [variance_fun_sum (fun i => (herror i).const_mul (weight i))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  simp only [quadraticForm_eq_dotProduct_mulVec, finiteErrorCovariance, Matrix.mulVec,
    dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A finite covariance Loewner bound controls the actual variance of the
corresponding random linear score. -/
theorem variance_finiteWeightedScore_le_scale_div_information
    (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ)
    {working : Matrix ι ι ℝ} {scale information : ℝ}
    (hcovariance : (scale • working - finiteErrorCovariance error μ).PosSemidef)
    (hweight : quadraticForm working weight = 1 / information) :
    Var[finiteWeightedScore weight error; μ] ≤ scale / information := by
  rw [variance_finiteWeightedScore_eq_quadraticForm weight error herror]
  exact quadraticForm_le_scale_div_information hcovariance weight hweight

/-- A two-sided finite covariance order transfers to a two-sided bound on the
variance of the actual weighted score. -/
theorem variance_finiteWeightedScore_sandwich_div_information
    (weight : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ i, MemLp (error i) 2 μ)
    {working : Matrix ι ι ℝ} {lower upper information : ℝ}
    (hlower : (finiteErrorCovariance error μ - lower • working).PosSemidef)
    (hupper : (upper • working - finiteErrorCovariance error μ).PosSemidef)
    (hweight : quadraticForm working weight = 1 / information) :
    lower / information ≤ Var[finiteWeightedScore weight error; μ] ∧
      Var[finiteWeightedScore weight error; μ] ≤ upper / information := by
  rw [variance_finiteWeightedScore_eq_quadraticForm weight error herror]
  exact quadraticForm_sandwich_div_information hlower hupper weight hweight

end InfillGLSLean
