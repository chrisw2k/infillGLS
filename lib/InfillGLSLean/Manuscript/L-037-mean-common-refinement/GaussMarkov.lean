module

public import «L-037-mean-common-refinement».CommonRefinement
public import Mathlib.Tactic.NoncommRing

/-!
# Finite true-GLS covariance minimality

This file is restricted to the finite Gauss--Markov comparison invoked in
Appendix `app:mean`: with a positive-definite covariance and a full-rank
design (rendered by positive definiteness of its GLS Gram matrix), full GLS
has no larger coefficient covariance than any other linear unbiased rule.
It does not construct a spatial common-refinement experiment.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L037

open Matrix

universe u v w

/-- The true-GLS Gram matrix `Dᵀ Σ⁻¹ D`. -/
@[expose] noncomputable def trueGLSGram {ι p : Type*} [Fintype ι] [DecidableEq ι]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ) : Matrix p p ℝ :=
  Matrix.transpose design * covariance⁻¹ * design

/-- The coefficient covariance matrix of true GLS, `B = (Dᵀ Σ⁻¹ D)⁻¹`. -/
@[expose] noncomputable def trueGLSCoefficientCovariance {ι p : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ) : Matrix p p ℝ :=
  (trueGLSGram covariance design)⁻¹

/-- The linear map from observations to the full true-GLS coefficient vector. -/
@[expose] noncomputable def trueGLSCoefficientMap {ι p : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ) : Matrix p ι ℝ :=
  trueGLSCoefficientCovariance covariance design * Matrix.transpose design * covariance⁻¹

/-- The covariance matrix of a linear coefficient rule applied to observations
with covariance `covariance`. -/
@[expose] noncomputable def linearCoefficientCovariance {ι p : Type*} [Fintype ι]
    (coefficientMap : Matrix p ι ℝ) (covariance : Matrix ι ι ℝ) : Matrix p p ℝ :=
  coefficientMap * covariance * Matrix.transpose coefficientMap

/-- Full true GLS is unbiased whenever its finite Gram matrix is positive
definite. -/
theorem trueGLSCoefficientMap_mul_design {ι p : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (hgram : (trueGLSGram covariance design).PosDef) :
    trueGLSCoefficientMap covariance design * design = 1 := by
  have hunit : IsUnit (trueGLSGram covariance design).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hgram.isUnit
  unfold trueGLSCoefficientMap trueGLSCoefficientCovariance trueGLSGram
  change (((Matrix.transpose design * covariance⁻¹ * design)⁻¹ *
      Matrix.transpose design) * covariance⁻¹) * design = 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.transpose design) covariance⁻¹ design]
  exact Matrix.nonsing_inv_mul _ hunit

/-- The true-GLS coefficient map satisfies its finite normal equation. -/
theorem trueGLSCoefficientMap_mul_covariance {ι p : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (hcovariance : covariance.PosDef) :
    trueGLSCoefficientMap covariance design * covariance =
      trueGLSCoefficientCovariance covariance design * Matrix.transpose design := by
  have hunit : IsUnit covariance.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hcovariance.isUnit
  unfold trueGLSCoefficientMap
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul covariance hunit, Matrix.mul_one]

/-- The covariance of the full true-GLS coefficient rule is exactly its
coefficient-covariance matrix. -/
theorem linearCoefficientCovariance_trueGLS {ι p : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (hcovariance : covariance.PosDef)
    (hgram : (trueGLSGram covariance design).PosDef) :
    linearCoefficientCovariance (trueGLSCoefficientMap covariance design) covariance =
      trueGLSCoefficientCovariance covariance design := by
  have hmap_design := trueGLSCoefficientMap_mul_design covariance design hgram
  have hmap_covariance := trueGLSCoefficientMap_mul_covariance covariance design hcovariance
  have htranspose := congrArg Matrix.transpose hmap_design
  rw [Matrix.transpose_mul, Matrix.transpose_one] at htranspose
  unfold linearCoefficientCovariance
  rw [hmap_covariance]
  rw [Matrix.mul_assoc]
  rw [htranspose, Matrix.mul_one]

private theorem transpose_eq_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {matrix : Matrix ι ι ℝ} (hmatrix : matrix.PosDef) : Matrix.transpose matrix = matrix := by
  calc
    Matrix.transpose matrix = Matrix.conjTranspose matrix :=
      (Matrix.conjTranspose_eq_transpose_of_trivial matrix).symm
    _ = matrix := hmatrix.isHermitian.eq

private theorem gaussMarkov_covariance_identity {ι p : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (coefficientCovariance : Matrix p p ℝ)
    (glsMap candidateMap : Matrix p ι ℝ)
    (hcovariance_symm : Matrix.transpose covariance = covariance)
    (hcoefficient_symm : Matrix.transpose coefficientCovariance = coefficientCovariance)
    (hgls_design : glsMap * design = 1)
    (hgls_covariance : glsMap * covariance =
      coefficientCovariance * Matrix.transpose design)
    (hcandidate_design : candidateMap * design = 1) :
    linearCoefficientCovariance candidateMap covariance - coefficientCovariance =
      linearCoefficientCovariance (candidateMap - glsMap) covariance := by
  have hcovariance_gls_transpose : covariance * Matrix.transpose glsMap =
      design * coefficientCovariance := by
    have htranspose := congrArg Matrix.transpose hgls_covariance
    simpa [hcovariance_symm, hcoefficient_symm] using htranspose
  have hcandidate_gls : candidateMap * covariance * Matrix.transpose glsMap =
      coefficientCovariance := by
    calc
      candidateMap * covariance * Matrix.transpose glsMap =
          candidateMap * (covariance * Matrix.transpose glsMap) :=
        Matrix.mul_assoc _ _ _
      _ = candidateMap * (design * coefficientCovariance) := by
        rw [hcovariance_gls_transpose]
      _ = (candidateMap * design) * coefficientCovariance :=
        (Matrix.mul_assoc _ _ _).symm
      _ = coefficientCovariance := by rw [hcandidate_design, Matrix.one_mul]
  have hdesign_candidate_transpose : Matrix.transpose design * Matrix.transpose candidateMap = 1 := by
    have htranspose := congrArg Matrix.transpose hcandidate_design
    simpa using htranspose
  have hgls_candidate : glsMap * covariance * Matrix.transpose candidateMap =
      coefficientCovariance := by
    calc
      glsMap * covariance * Matrix.transpose candidateMap =
          (coefficientCovariance * Matrix.transpose design) * Matrix.transpose candidateMap := by
        rw [hgls_covariance]
      _ = coefficientCovariance *
          (Matrix.transpose design * Matrix.transpose candidateMap) :=
        Matrix.mul_assoc _ _ _
      _ = coefficientCovariance := by
        rw [hdesign_candidate_transpose, Matrix.mul_one]
  have hdesign_gls_transpose : Matrix.transpose design * Matrix.transpose glsMap = 1 := by
    have htranspose := congrArg Matrix.transpose hgls_design
    simpa using htranspose
  have hgls_self : glsMap * covariance * Matrix.transpose glsMap = coefficientCovariance := by
    calc
      glsMap * covariance * Matrix.transpose glsMap =
          (coefficientCovariance * Matrix.transpose design) * Matrix.transpose glsMap := by
        rw [hgls_covariance]
      _ = coefficientCovariance *
          (Matrix.transpose design * Matrix.transpose glsMap) :=
        Matrix.mul_assoc _ _ _
      _ = coefficientCovariance := by
        rw [hdesign_gls_transpose, Matrix.mul_one]
  unfold linearCoefficientCovariance
  rw [Matrix.transpose_sub]
  calc
    candidateMap * covariance * Matrix.transpose candidateMap - coefficientCovariance =
        candidateMap * covariance * Matrix.transpose candidateMap -
          candidateMap * covariance * Matrix.transpose glsMap -
          glsMap * covariance * Matrix.transpose candidateMap +
          glsMap * covariance * Matrix.transpose glsMap := by
      rw [hcandidate_gls, hgls_candidate, hgls_self]
      abel
    _ = (candidateMap - glsMap) * covariance *
        (Matrix.transpose candidateMap - Matrix.transpose glsMap) := by
      symm
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel

/-- Finite Gauss--Markov covariance minimality.  Its hypotheses are the
positive-definite true covariance, the positive-definite GLS Gram matrix
(the finite full-rank condition), and the defining unbiasedness property of
the competing linear rule. -/
theorem trueGLSCoefficientCovariance_le_linearUnbiased {ι p : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (hcovariance : covariance.PosDef)
    (hgram : (trueGLSGram covariance design).PosDef)
    (candidateMap : Matrix p ι ℝ) (hcandidate_design : candidateMap * design = 1) :
    (linearCoefficientCovariance candidateMap covariance -
      trueGLSCoefficientCovariance covariance design).PosSemidef := by
  have hgram_covariance :
      Matrix.transpose (trueGLSCoefficientCovariance covariance design) =
        trueGLSCoefficientCovariance covariance design := by
    unfold trueGLSCoefficientCovariance
    exact transpose_eq_of_posDef hgram.inv
  have hid := gaussMarkov_covariance_identity covariance design
    (trueGLSCoefficientCovariance covariance design)
    (trueGLSCoefficientMap covariance design) candidateMap
    (transpose_eq_of_posDef hcovariance) hgram_covariance
    (trueGLSCoefficientMap_mul_design covariance design hgram)
    (trueGLSCoefficientMap_mul_covariance covariance design hcovariance)
    hcandidate_design
  rw [hid]
  unfold linearCoefficientCovariance
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hcovariance.posSemidef.mul_mul_conjTranspose_same
      (candidateMap - trueGLSCoefficientMap covariance design)

/-- The treatment-coordinate form of finite Gauss--Markov minimality.  A
linear weight whose design moments select coefficient `i` has true quadratic
variance at least the `i`-th diagonal entry of full true GLS.  This is a
finite algebraic corollary of the preceding matrix theorem, intended for the
paper's displayed bound on the hypothetical true-GLS treatment variance. -/
theorem trueGLSCoefficientCovariance_diag_le_quadraticForm_of_feasible
    {ι p : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (hcovariance : covariance.PosDef)
    (hgram : (trueGLSGram covariance design).PosDef)
    (i : p) (weight : ι → ℝ)
    (hfeasible : Matrix.mulVec (Matrix.transpose design) weight = Pi.single i 1) :
    trueGLSCoefficientCovariance covariance design i i ≤
      quadraticForm covariance weight := by
  classical
  let glsMap : Matrix p ι ℝ := trueGLSCoefficientMap covariance design
  let candidateMap : Matrix p ι ℝ := fun j r =>
    if j = i then weight r else glsMap j r
  have hgls_design : glsMap * design = 1 := by
    exact trueGLSCoefficientMap_mul_design covariance design hgram
  have hcandidate_design : candidateMap * design = 1 := by
    ext j l
    by_cases hji : j = i
    · subst j
      calc
        (candidateMap * design) i l = ∑ r, weight r * design r l := by
          change (∑ r, (if i = i then weight r else glsMap i r) * design r l) = _
          simp only [↓reduceIte]
        _ = ∑ r, design r l * weight r := by
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ = (Matrix.mulVec (Matrix.transpose design) weight) l := rfl
        _ = (1 : Matrix p p ℝ) i l := by
          rw [congrFun hfeasible l]
          by_cases hil : i = l
          · subst l
            simp
          · have hli : l ≠ i := fun h => hil h.symm
            simp [hil, hli]
    · calc
        (candidateMap * design) j l = (glsMap * design) j l := by
          change (∑ r, (if j = i then weight r else glsMap j r) * design r l) =
            ∑ r, glsMap j r * design r l
          simp only [hji, ↓reduceIte]
        _ = (1 : Matrix p p ℝ) j l := congrFun (congrFun hgls_design j) l
  have hminimal := trueGLSCoefficientCovariance_le_linearUnbiased
    covariance design hcovariance hgram candidateMap hcandidate_design
  have hcandidate_diag : linearCoefficientCovariance candidateMap covariance i i =
      quadraticForm covariance weight := by
    rw [quadraticForm_eq_dotProduct_mulVec]
    unfold linearCoefficientCovariance
    change (∑ x, (∑ y, candidateMap i y * covariance y x) * candidateMap i x) =
      ∑ y, weight y * ∑ x, covariance y x * weight x
    simp only [candidateMap, ↓reduceIte]
    calc
      (∑ x, (∑ y, weight y * covariance y x) * weight x) =
          ∑ x, ∑ y, (weight y * covariance y x) * weight x := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_mul]
      _ = ∑ y, ∑ x, weight y * (covariance y x * weight x) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = ∑ y, weight y * ∑ x, covariance y x * weight x := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum]
  have hdiag : 0 ≤
      (linearCoefficientCovariance candidateMap covariance -
        trueGLSCoefficientCovariance covariance design) i i :=
    hminimal.diag_nonneg
  rw [Matrix.sub_apply] at hdiag
  calc
    trueGLSCoefficientCovariance covariance design i i ≤
        linearCoefficientCovariance candidateMap covariance i i := by linarith
    _ = quadraticForm covariance weight := hcandidate_diag

/-- Coarsening a finite experiment through a deterministic linear observation
cannot decrease the true-GLS coefficient covariance.  This is the exact
finite Gauss--Markov comparison used in the common-refinement paragraph of
Appendix `app:mean`.  The map is an explicit theorem parameter here; L-037's
regional-average result derives its entries from intersection-cell measures.
The positive-definiteness hypotheses are precisely the finite covariance and
full-rank conditions stated for the common-refinement experiments. -/
theorem trueGLSCoefficientCovariance_mono_of_linearObservation
    {ι κ p : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype p] [DecidableEq p]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (observation : Matrix κ ι ℝ)
    (hcovariance : covariance.PosDef)
    (hobserved_covariance :
      (observation * covariance * Matrix.transpose observation).PosDef)
    (hgram : (trueGLSGram covariance design).PosDef)
    (hobserved_gram :
      (trueGLSGram (observation * covariance * Matrix.transpose observation)
        (observation * design)).PosDef) :
    (trueGLSCoefficientCovariance
      (observation * covariance * Matrix.transpose observation) (observation * design) -
      trueGLSCoefficientCovariance covariance design).PosSemidef := by
  let observedCovariance : Matrix κ κ ℝ :=
    observation * covariance * Matrix.transpose observation
  let observedDesign : Matrix κ p ℝ := observation * design
  let observedMap : Matrix p κ ℝ :=
    trueGLSCoefficientMap observedCovariance observedDesign
  let liftedObservedMap : Matrix p ι ℝ := observedMap * observation
  have hlifted_unbiased : liftedObservedMap * design = 1 := by
    change (observedMap * observation) * design = 1
    rw [Matrix.mul_assoc]
    exact trueGLSCoefficientMap_mul_design observedCovariance observedDesign
      (by simpa [observedCovariance, observedDesign] using hobserved_gram)
  have hminimal := trueGLSCoefficientCovariance_le_linearUnbiased covariance design
    hcovariance hgram liftedObservedMap hlifted_unbiased
  have hlifted_covariance :
      linearCoefficientCovariance liftedObservedMap covariance =
        linearCoefficientCovariance observedMap observedCovariance := by
    unfold linearCoefficientCovariance
    change ((observedMap * observation) * covariance) *
        Matrix.transpose (observedMap * observation) =
      (observedMap * observedCovariance) * Matrix.transpose observedMap
    rw [Matrix.transpose_mul]
    simp [observedCovariance, Matrix.mul_assoc]
  have hobserved_gls_covariance :
      linearCoefficientCovariance observedMap observedCovariance =
        trueGLSCoefficientCovariance observedCovariance observedDesign :=
    linearCoefficientCovariance_trueGLS observedCovariance observedDesign
      (by simpa [observedCovariance] using hobserved_covariance)
      (by simpa [observedCovariance, observedDesign] using hobserved_gram)
  rw [← hobserved_gls_covariance, ← hlifted_covariance]
  simpa [observedCovariance, observedDesign, observedMap, liftedObservedMap] using hminimal

end InfillGLSLean.ManuscriptSpecification.L037

end
