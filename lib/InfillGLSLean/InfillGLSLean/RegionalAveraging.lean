module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Finite regional-averaging contraction

Task L-007, supporting the regional-averaging layer in the manuscript's
Appendix `app:averaging`, especially Lemma `lem:averaging`.  The manuscript
uses regional averaging as an L2 contraction before proving convergence for a
sequence of possibly nonnested spatial partitions.  This file formalizes the
finite, equal-weight analogue: averaging a finite collection of real values
cannot increase squared error.

It deliberately does **not** formalize Borel partitions, their refinement
condition, the spatial `L2` limit, or the full nonnested-partition lemma.
Those require a separate measure-theoretic construction of the averaging
operator and its approximation properties.
-/

public section

namespace InfillGLSLean

open scoped BigOperators

variable {ι : Type*}

/-- The equally weighted empirical mean over a finite region. -/
noncomputable def regionalMean (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ i ∈ s, f i) / s.card

/-- Squaring a regional mean cannot exceed the regional mean of the squares. -/
theorem sq_regionalMean_le_regionalMean_sq (s : Finset ι) (f : ι → ℝ) :
    (regionalMean s f) ^ 2 ≤ regionalMean s (fun i => (f i) ^ 2) := by
  exact sum_div_card_sq_le_sum_sq_div_card

/-- An equally weighted regional mean preserves a constant on a nonempty
region. -/
theorem regionalMean_const (s : Finset ι) (hs : s.Nonempty) (c : ℝ) :
    regionalMean s (fun _ => c) = c := by
  simp [regionalMean, hs.card_ne_zero]

/-- Regional averaging commutes with a pointwise difference. -/
theorem regionalMean_sub (s : Finset ι) (f g : ι → ℝ) :
    regionalMean s (fun i => f i - g i) = regionalMean s f - regionalMean s g := by
  simp [regionalMean, Finset.sum_sub_distrib]
  field_simp

/-- The equally weighted regional-mean operator is an L2 contraction in
squared-error form. -/
theorem regionalMean_difference_sq_le (s : Finset ι) (f g : ι → ℝ) :
    (regionalMean s f - regionalMean s g) ^ 2 ≤
      regionalMean s (fun i => (f i - g i) ^ 2) := by
  rw [← regionalMean_sub s f g]
  exact sq_regionalMean_le_regionalMean_sq s (fun i => f i - g i)

/-- The squared error of a finite regional mean around a constant is bounded
by the finite regional mean of the pointwise squared errors. -/
theorem regionalMean_centered_sq_le (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (target : ℝ) :
    (regionalMean s f - target) ^ 2 ≤
      regionalMean s (fun i => (f i - target) ^ 2) := by
  calc
    (regionalMean s f - target) ^ 2 =
        (regionalMean s f - regionalMean s (fun _ => target)) ^ 2 := by
          rw [regionalMean_const s hs target]
    _ ≤ regionalMean s (fun i => (f i - target) ^ 2) := by
          simpa using regionalMean_difference_sq_le s f (fun _ => target)

end InfillGLSLean
