module

/-!
# Finite-dimensional GLS foundations

This first module deliberately isolates algebra from probability and spatial
asymptotics.  The next module will replace scalar operations with a
finite-dimensional inner-product space and a positive-definite working matrix.
-/

public section

namespace InfillGLSLean

/-- The minimal algebraic interface needed for the initial model-error
reduction.  Mathlib will supply a standard real-number instance once the
matrix formalization begins. -/
class CenteredAlgebra (R : Type) extends Add R, Sub R, Mul R where
  add_sub_cancel_left (a b : R) : a + b - a = b

/-- The structural-model error associated with a proposed coefficient. -/
def centeredError {R : Type} [Sub R] [Mul R]
    (outcome treatment coefficient : R) : R :=
  outcome - treatment * coefficient

/-- With no controls, residualizing treatment leaves treatment unchanged. -/
def residualizeWithoutControls {R : Type} (treatment : R) : R :=
  treatment

theorem residualize_without_controls {R : Type} (treatment : R) :
    residualizeWithoutControls treatment = treatment := by
  rfl

/-- Substitution into the structural model recovers the original error. -/
theorem centeredError_of_model {R : Type} [CenteredAlgebra R]
    {outcome treatment coefficient error : R}
    (model : outcome = treatment * coefficient + error) :
    centeredError outcome treatment coefficient = error := by
  rw [model, centeredError]
  exact CenteredAlgebra.add_sub_cancel_left _ _

/-- A scalar weighted GLS score reduces to the weighted structural error. -/
def scalarScore {R : Type} [Sub R] [Mul R]
    (weight treatment outcome coefficient : R) : R :=
  weight * treatment * centeredError outcome treatment coefficient

theorem scalarScore_of_model {R : Type} [CenteredAlgebra R]
    {weight treatment outcome coefficient error : R}
    (model : outcome = treatment * coefficient + error) :
    scalarScore weight treatment outcome coefficient =
      weight * treatment * error := by
  unfold scalarScore
  rw [centeredError_of_model model]

end InfillGLSLean
