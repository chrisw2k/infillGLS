module

public import InfillGLSLean.MultiControlGLS
public import InfillGLSLean.MatrixCovarianceOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Finite GLS outcome weights and their identities

This module is the finite post-conditioning version of the manuscript's
`eq:weights` and `eq:weight-identities` (source `main.tex`, lines 421--435).
Here `workingCovariance = K_n`, `controls = W_n`, `treatment = X_n`, and
`glsOutcomeWeight` is the displayed `omega_n`. The precision matrix is
`K_n^{-1}`; `residualizeControls` is exactly the bracketed residualized
treatment, and `controlInformation` is `Q_n`.

The rank and relevance conditions are explicit: `hgram` says
`W_n' K_n^{-1} W_n` is nonsingular and `hresidual` says the residualized
treatment is nonzero. Thus this module derives finite algebra identities only;
it does not construct `K_n`, regressors, or any sequence-level/infill condition.
-/

public section

namespace InfillGLSLean

open Matrix

variable {I Kappa : Type*} [Fintype I] [DecidableEq I]
  [Fintype Kappa] [DecidableEq Kappa]

/-- The GLS outcome-weight vector from manuscript equation `eq:weights`.
It is `K^{-1} r / Q`, where `r` is the precision-residualized treatment and
`Q = r' K^{-1} r`. -/
@[expose]
noncomputable def glsOutcomeWeight (workingCovariance : Matrix I I Real)
    (controls : Matrix I Kappa Real) (treatment : I -> Real) : I -> Real :=
  fun i => (Inv.inv (controlInformation (Inv.inv workingCovariance) controls treatment)) *
    (Matrix.mulVec (Inv.inv workingCovariance)
      (residualizeControls (Inv.inv workingCovariance) controls treatment)) i

/-- Public expansion of the finite GLS outcome weights. -/
@[simp]
theorem glsOutcomeWeight_eq (workingCovariance : Matrix I I Real)
    (controls : Matrix I Kappa Real) (treatment : I -> Real) :
    glsOutcomeWeight workingCovariance controls treatment =
      fun i => (Inv.inv (controlInformation (Inv.inv workingCovariance) controls treatment)) *
        (Matrix.mulVec (Inv.inv workingCovariance)
          (residualizeControls (Inv.inv workingCovariance) controls treatment)) i :=
  rfl

omit [DecidableEq I] in
/-- A residualized treatment is precision-orthogonal to every control
combination. This is the scalar form of the zero control score used below. -/
theorem residualizedTreatment_precision_controls_zero
    (precision : Matrix I I Real) (controls : Matrix I Kappa Real)
    (treatment : I -> Real) (coefficients : Kappa -> Real)
    (hsymm : Matrix.transpose precision = precision)
    (hgram : IsUnit (controlGram precision controls).det) :
    dotProduct (residualizeControls precision controls treatment)
      (Matrix.mulVec precision (Matrix.mulVec controls coefficients)) = 0 := by
  have hscore := controlScore_residualizeControls precision controls treatment hgram
  have hscore' : Matrix.mulVec (Matrix.transpose controls)
      (Matrix.mulVec precision
        (residualizeControls precision controls treatment)) = 0 := by
    exact hscore
  calc
    dotProduct (residualizeControls precision controls treatment)
        (Matrix.mulVec precision (Matrix.mulVec controls coefficients)) =
        dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec (Matrix.transpose precision)
            (Matrix.mulVec controls coefficients)) := by
              rw [hsymm]
    _ = dotProduct (Matrix.mulVec controls coefficients)
        (Matrix.mulVec precision
          (residualizeControls precision controls treatment)) := by
            exact Matrix.dotProduct_transpose_mulVec precision
              (residualizeControls precision controls treatment)
              (Matrix.mulVec controls coefficients)
    _ = dotProduct (Matrix.mulVec precision
          (residualizeControls precision controls treatment))
        (Matrix.mulVec controls coefficients) := by
          exact dotProduct_comm _ _
    _ = dotProduct coefficients
        (Matrix.mulVec (Matrix.transpose controls)
          (Matrix.mulVec precision
            (residualizeControls precision controls treatment))) := by
              exact (Matrix.dotProduct_transpose_mulVec controls coefficients
                (Matrix.mulVec precision
                  (residualizeControls precision controls treatment))).symm
    _ = 0 := by rw [hscore']; simp

omit [DecidableEq I] in
/-- The precision score of the residualized treatment against the original
treatment is exactly the GLS information. -/
theorem residualizedTreatment_dot_precision_treatment_eq_information
    (precision : Matrix I I Real) (controls : Matrix I Kappa Real)
    (treatment : I -> Real)
    (hsymm : Matrix.transpose precision = precision)
    (hgram : IsUnit (controlGram precision controls).det) :
    dotProduct (residualizeControls precision controls treatment)
      (Matrix.mulVec precision treatment) =
      controlInformation precision controls treatment := by
  let coefficients : Kappa -> Real := Matrix.mulVec
    (Inv.inv (controlGram precision controls))
    (controlScore precision controls treatment)
  have hsplit : treatment =
      residualizeControls precision controls treatment +
        Matrix.mulVec controls coefficients := by
    unfold residualizeControls
    dsimp [coefficients]
    abel
  have hsplitMul : Matrix.mulVec precision treatment =
      Matrix.mulVec precision
        (residualizeControls precision controls treatment +
          Matrix.mulVec controls coefficients) := by
    exact congrArg (Matrix.mulVec precision) hsplit
  calc
    dotProduct (residualizeControls precision controls treatment)
        (Matrix.mulVec precision treatment) =
        dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec precision
            (residualizeControls precision controls treatment +
              Matrix.mulVec controls coefficients)) := by
                exact congrArg
                  (dotProduct (residualizeControls precision controls treatment))
                  hsplitMul
    _ = dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec precision
            (residualizeControls precision controls treatment)) +
        dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec precision (Matrix.mulVec controls coefficients)) := by
            rw [Matrix.mulVec_add, dotProduct_add]
    _ = dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec precision
            (residualizeControls precision controls treatment)) := by
            rw [residualizedTreatment_precision_controls_zero precision controls treatment
              coefficients hsymm hgram]
            ring
    _ = controlInformation precision controls treatment := by
      rfl

/-- The first identity in `eq:weight-identities`: the actual GLS outcome
weight has unit score against the treatment. -/
theorem glsOutcomeWeight_dot_treatment_eq_one
    (workingCovariance : Matrix I I Real) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa Real) (treatment : I -> Real)
    (hgram : IsUnit
      (controlGram (Inv.inv workingCovariance) controls).det)
    (hresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0)) :
    dotProduct (glsOutcomeWeight workingCovariance controls treatment)
      treatment = 1 := by
  let precision : Matrix I I Real := Inv.inv workingCovariance
  let residual : I -> Real :=
    residualizeControls precision controls treatment
  let information : Real :=
    controlInformation precision controls treatment
  have hprecision : precision.PosDef := by
    dsimp [precision]
    exact hworking.inv
  have hsymm : Matrix.transpose precision = precision := by
    simpa using hprecision.isHermitian.eq
  have hinformation : Not (information = 0) := by
    dsimp [information]
    apply controlInformation_ne_zero hprecision
    simpa [precision, residual] using hresidual
  have hscore : dotProduct (Matrix.mulVec precision residual) treatment = information := by
    calc
      dotProduct (Matrix.mulVec precision residual) treatment =
          dotProduct treatment (Matrix.mulVec precision residual) := dotProduct_comm _ _
      _ = dotProduct residual (Matrix.mulVec (Matrix.transpose precision) treatment) := by
        exact (Matrix.dotProduct_transpose_mulVec precision residual treatment).symm
      _ = dotProduct residual (Matrix.mulVec precision treatment) := by rw [hsymm]
      _ = controlInformation precision controls treatment :=
        residualizedTreatment_dot_precision_treatment_eq_information precision controls treatment
          hsymm hgram
  change dotProduct (glsOutcomeWeight workingCovariance controls treatment)
    treatment = 1
  rw [glsOutcomeWeight_eq]
  simp only [dotProduct]
  calc
    (Finset.univ.sum fun i =>
        (Inv.inv information * (Matrix.mulVec precision residual) i) * treatment i) =
        Inv.inv information *
          (Finset.univ.sum fun i => (Matrix.mulVec precision residual) i * treatment i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = Inv.inv information *
          dotProduct (Matrix.mulVec precision residual) treatment := by rfl
    _ = 1 := by rw [hscore]; field_simp [hinformation]

/-- The column-vector form of the second identity in `eq:weight-identities`:
`W' omega = 0`. This is exactly equivalent to the manuscript's row notation
`omega' W = 0`. -/
theorem glsOutcomeWeight_controls_transpose_eq_zero
    (workingCovariance : Matrix I I Real) (controls : Matrix I Kappa Real)
    (treatment : I -> Real)
    (hgram : IsUnit
      (controlGram (Inv.inv workingCovariance) controls).det) :
    Matrix.mulVec (Matrix.transpose controls)
      (glsOutcomeWeight workingCovariance controls treatment) = 0 := by
  let precision : Matrix I I Real := Inv.inv workingCovariance
  let residual : I -> Real :=
    residualizeControls precision controls treatment
  let information : Real :=
    controlInformation precision controls treatment
  have hscore : Matrix.mulVec (Matrix.transpose controls)
      (Matrix.mulVec precision residual) = 0 := by
    exact controlScore_residualizeControls precision controls treatment hgram
  ext j
  rw [glsOutcomeWeight_eq]
  change Finset.univ.sum (fun i =>
      (Matrix.transpose controls) j i *
        (Inv.inv information * (Matrix.mulVec precision residual) i)) = 0
  calc
    Finset.univ.sum (fun i =>
        (Matrix.transpose controls) j i *
          (Inv.inv information * (Matrix.mulVec precision residual) i)) =
        Inv.inv information *
          Finset.univ.sum (fun i =>
            (Matrix.transpose controls) j i * (Matrix.mulVec precision residual) i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
    _ = Inv.inv information *
        (Matrix.mulVec (Matrix.transpose controls)
          (Matrix.mulVec precision residual)) j := by rfl
    _ = 0 := by rw [hscore]; simp

/-- The control-combination form of `omega' W = 0`, convenient for the
fixed-control bias calculation. -/
theorem glsOutcomeWeight_dot_controls_eq_zero
    (workingCovariance : Matrix I I Real) (controls : Matrix I Kappa Real)
    (treatment : I -> Real)
    (hgram : IsUnit
      (controlGram (Inv.inv workingCovariance) controls).det)
    (coefficients : Kappa -> Real) :
    dotProduct (glsOutcomeWeight workingCovariance controls treatment)
      (Matrix.mulVec controls coefficients) = 0 := by
  have horthogonal := glsOutcomeWeight_controls_transpose_eq_zero
    workingCovariance controls treatment hgram
  calc
    dotProduct (glsOutcomeWeight workingCovariance controls treatment)
        (Matrix.mulVec controls coefficients) =
        dotProduct coefficients
          (Matrix.mulVec (Matrix.transpose controls)
            (glsOutcomeWeight workingCovariance controls treatment)) := by
              exact (Matrix.dotProduct_transpose_mulVec controls coefficients
                (glsOutcomeWeight workingCovariance controls treatment)).symm
    _ = 0 := by rw [horthogonal]; simp

/-- The third identity in `eq:weight-identities`: the GLS outcome weight has
working-covariance quadratic form `1 / Q`. -/
theorem glsOutcomeWeight_working_quadratic_eq_inv_information
    (workingCovariance : Matrix I I Real) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa Real) (treatment : I -> Real)
    (hresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0)) :
    dotProduct (glsOutcomeWeight workingCovariance controls treatment)
      (Matrix.mulVec workingCovariance
        (glsOutcomeWeight workingCovariance controls treatment)) =
      1 / controlInformation (Inv.inv workingCovariance) controls treatment := by
  let precision : Matrix I I Real := Inv.inv workingCovariance
  let residual : I -> Real :=
    residualizeControls precision controls treatment
  let information : Real :=
    controlInformation precision controls treatment
  have hprecision : precision.PosDef := by
    dsimp [precision]
    exact hworking.inv
  have hinformation : Not (information = 0) := by
    dsimp [information]
    apply controlInformation_ne_zero hprecision
    simpa [precision, residual] using hresidual
  have hdet : IsUnit workingCovariance.det :=
    workingCovariance.isUnit_iff_isUnit_det.mp hworking.isUnit
  have hworking_precision : Matrix.mulVec workingCovariance
      (Matrix.mulVec precision residual) = residual := by
    calc
      Matrix.mulVec workingCovariance (Matrix.mulVec precision residual) =
          Matrix.mulVec (workingCovariance * precision) residual := by
            rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec 1 residual := by
            rw [show precision = Inv.inv workingCovariance by rfl]
            rw [Matrix.mul_nonsing_inv workingCovariance hdet]
      _ = residual := by simp
  have hworking_weight : Matrix.mulVec workingCovariance
      (glsOutcomeWeight workingCovariance controls treatment) =
      fun i => Inv.inv information * residual i := by
    ext i
    rw [glsOutcomeWeight_eq]
    change Finset.univ.sum (fun j => workingCovariance i j *
      (Inv.inv information * (Matrix.mulVec precision residual) j)) =
        Inv.inv information * residual i
    calc
      Finset.univ.sum (fun j => workingCovariance i j *
        (Inv.inv information * (Matrix.mulVec precision residual) j)) =
        Inv.inv information * Finset.univ.sum (fun j =>
          workingCovariance i j * (Matrix.mulVec precision residual) j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = Inv.inv information *
          (Matrix.mulVec workingCovariance (Matrix.mulVec precision residual)) i := by rfl
      _ = Inv.inv information * residual i := by rw [hworking_precision]
  have hquadratic : dotProduct (Matrix.mulVec precision residual) residual = information := by
    rw [dotProduct_comm]
    rfl
  rw [hworking_weight, glsOutcomeWeight_eq]
  change Finset.univ.sum (fun i =>
    (Inv.inv information * (Matrix.mulVec precision residual) i) *
      (Inv.inv information * residual i)) = 1 / information
  calc
    Finset.univ.sum (fun i =>
      (Inv.inv information * (Matrix.mulVec precision residual) i) *
        (Inv.inv information * residual i)) =
        (Inv.inv information * Inv.inv information) *
          Finset.univ.sum (fun i => (Matrix.mulVec precision residual) i * residual i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (Inv.inv information * Inv.inv information) *
          dotProduct (Matrix.mulVec precision residual) residual := by rfl
    _ = 1 / information := by rw [hquadratic]; field_simp [hinformation]

/-- The quadratic-form notation for the same working-normalization identity,
ready to supply to the covariance and bias modules. -/
theorem glsOutcomeWeight_quadraticForm_eq_inv_information
    (workingCovariance : Matrix I I Real) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa Real) (treatment : I -> Real)
    (hresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0)) :
    quadraticForm workingCovariance
      (glsOutcomeWeight workingCovariance controls treatment) =
      1 / controlInformation (Inv.inv workingCovariance) controls treatment := by
  rw [quadraticForm_eq_dotProduct_mulVec]
  exact glsOutcomeWeight_working_quadratic_eq_inv_information workingCovariance
    hworking controls treatment hresidual

omit [DecidableEq I] in
/-- Residualizing the outcome does not change its precision score against the
residualized treatment. This is the finite FWL numerator step. -/
theorem residualizedTreatment_dot_precision_residualize_eq_original
    (precision : Matrix I I Real) (controls : Matrix I Kappa Real)
    (treatment outcome : I -> Real)
    (hsymm : Matrix.transpose precision = precision)
    (hgram : IsUnit (controlGram precision controls).det) :
    dotProduct (residualizeControls precision controls treatment)
      (Matrix.mulVec precision
        (residualizeControls precision controls outcome)) =
      dotProduct (residualizeControls precision controls treatment)
        (Matrix.mulVec precision outcome) := by
  let coefficients : Kappa -> Real := Matrix.mulVec
    (Inv.inv (controlGram precision controls))
    (controlScore precision controls outcome)
  have hresidualize : residualizeControls precision controls outcome =
      outcome - Matrix.mulVec controls coefficients := by
    rfl
  have hresidualizeMul : Matrix.mulVec precision
      (residualizeControls precision controls outcome) =
      Matrix.mulVec precision (outcome - Matrix.mulVec controls coefficients) := by
        exact congrArg (Matrix.mulVec precision) hresidualize
  calc
    dotProduct (residualizeControls precision controls treatment)
        (Matrix.mulVec precision
          (residualizeControls precision controls outcome)) =
        dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec precision (outcome - Matrix.mulVec controls coefficients)) := by
            exact congrArg
              (dotProduct (residualizeControls precision controls treatment))
              hresidualizeMul
    _ = dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec precision outcome) -
        dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec precision (Matrix.mulVec controls coefficients)) := by
            rw [Matrix.mulVec_sub, dotProduct_sub]
    _ = dotProduct (residualizeControls precision controls treatment)
          (Matrix.mulVec precision outcome) := by
            rw [residualizedTreatment_precision_controls_zero precision controls treatment
              coefficients hsymm hgram]
            ring

/-- The remaining identity in `eq:weight-identities`: the finite FWL
coefficient is exactly the dot product of the actual GLS outcome weights with
the outcome vector. -/
theorem fwlEstimateControls_eq_glsOutcomeWeight_dot
    (workingCovariance : Matrix I I Real) (hworking : workingCovariance.PosDef)
    (controls : Matrix I Kappa Real) (treatment outcome : I -> Real)
    (hgram : IsUnit
      (controlGram (Inv.inv workingCovariance) controls).det)
    (hresidual : Not
      (residualizeControls (Inv.inv workingCovariance) controls treatment = 0)) :
    fwlEstimateControls (Inv.inv workingCovariance) controls treatment outcome =
      dotProduct (glsOutcomeWeight workingCovariance controls treatment) outcome := by
  let precision : Matrix I I Real := Inv.inv workingCovariance
  let residual : I -> Real :=
    residualizeControls precision controls treatment
  let information : Real :=
    controlInformation precision controls treatment
  have hprecision : precision.PosDef := by
    dsimp [precision]
    exact hworking.inv
  have hsymm : Matrix.transpose precision = precision := by
    simpa using hprecision.isHermitian.eq
  have hinformation : Not (information = 0) := by
    dsimp [information]
    apply controlInformation_ne_zero hprecision
    simpa [precision, residual] using hresidual
  have hresidual_score : dotProduct residual
      (Matrix.mulVec precision
        (residualizeControls precision controls outcome)) =
      dotProduct residual (Matrix.mulVec precision outcome) :=
    residualizedTreatment_dot_precision_residualize_eq_original precision controls treatment outcome
      hsymm hgram
  have hweight_score : dotProduct
      (glsOutcomeWeight workingCovariance controls treatment) outcome =
      dotProduct residual (Matrix.mulVec precision outcome) / information := by
    rw [glsOutcomeWeight_eq]
    change Finset.univ.sum (fun i =>
      (Inv.inv information * (Matrix.mulVec precision residual) i) * outcome i) =
      dotProduct residual (Matrix.mulVec precision outcome) / information
    calc
      Finset.univ.sum (fun i =>
        (Inv.inv information * (Matrix.mulVec precision residual) i) * outcome i) =
        Inv.inv information *
          Finset.univ.sum (fun i => (Matrix.mulVec precision residual) i * outcome i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = Inv.inv information *
          dotProduct (Matrix.mulVec precision residual) outcome := by rfl
      _ = Inv.inv information *
          dotProduct outcome (Matrix.mulVec precision residual) := by rw [dotProduct_comm]
      _ = Inv.inv information *
          dotProduct residual (Matrix.mulVec (Matrix.transpose precision) outcome) := by
            rw [Matrix.dotProduct_transpose_mulVec]
      _ = Inv.inv information *
          dotProduct residual (Matrix.mulVec precision outcome) := by rw [hsymm]
      _ = dotProduct residual (Matrix.mulVec precision outcome) / information := by
            ring
  change dotProduct residual
      (Matrix.mulVec precision
        (residualizeControls precision controls outcome)) / information =
      dotProduct (glsOutcomeWeight workingCovariance controls treatment) outcome
  apply (div_eq_iff hinformation).2
  rw [hresidual_score, hweight_score]
  field_simp [hinformation]

end InfillGLSLean
