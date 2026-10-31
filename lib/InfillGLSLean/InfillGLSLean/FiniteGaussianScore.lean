module

public import InfillGLSLean.MatrixCovarianceOrder
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# A finite Gaussian score after conditioning

This file formalizes a narrow finite-dimensional bridge used in the Gaussian
part of the manuscript's normality and variance arguments.  It begins *after*
conditioning: `P` is a fixed probability law and `hZ` explicitly assumes that
the finite centered error vector has the indicated multivariate Gaussian law
under `P`.  Thus it can be instantiated with a conditional law after the
covariates have been fixed, but it neither constructs a conditional-distribution
kernel nor derives conditional Gaussianity from the manuscript's assumptions.

For deterministic finite weights, the literal coordinate score has mean zero,
variance `weight' * covariance * weight`, and the corresponding centered
univariate Gaussian law.  `gaussianReal` takes its variance parameter in
`NNReal`; the law theorem therefore uses
`(quadraticForm covariance weight).toNNReal`.  Positive semidefiniteness makes
the real quadratic form nonnegative, and
`finiteGaussianScore_varianceParameter_coe` records that this conversion does
not change its real value.

This is only the finite Gaussian-score step.  It does not formalize the
geographic/matrix construction of the covariance, the GLS weight identity, a
conditional kernel, a bias or remainder bound, or an asymptotic-normality
conclusion.
-/

public section

namespace InfillGLSLean

open MeasureTheory Matrix ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable section

variable {O I : Type*} [Fintype I]

/-- The literal finite-coordinate score associated with deterministic weights. -/
@[expose]
def finiteGaussianScore
    (weight : I -> Real) (Z : O -> EuclideanSpace Real I) : O -> Real :=
  fun omega => Finset.univ.sum (fun i => weight i * (Z omega).ofLp i)

/-- The literal coordinate definition agrees with the Euclidean inner-product
form used by Mathlib's multivariate-Gaussian API. -/
theorem finiteGaussianScore_eq_inner
    (weight : I -> Real) (Z : O -> EuclideanSpace Real I) (omega : O) :
    finiteGaussianScore weight Z omega =
      (innerSL Real (WithLp.toLp 2 weight)) (Z omega) := by
  simp only [finiteGaussianScore, innerSL_apply_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

variable [MeasurableSpace O]

/-- Under a centered finite multivariate Gaussian law, the deterministic
coordinate score has mean zero. -/
theorem finiteGaussianScore_mean
    [DecidableEq I]
    {P : Measure O} {Z : O -> EuclideanSpace Real I}
    {covariance : Matrix I I Real} {weight : I -> Real}
    (hZ : HasLaw Z (multivariateGaussian 0 covariance) P) :
    integral P (finiteGaussianScore weight Z) = 0 := by
  have hscore_eq : finiteGaussianScore weight Z =
      fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega) := by
    funext omega
    exact finiteGaussianScore_eq_inner weight Z omega
  rw [hscore_eq]
  have hcomp := hZ.integral_comp
    ((innerSL Real (WithLp.toLp 2 weight)).continuous.aestronglyMeasurable)
  have hmeanMeasure : integral (multivariateGaussian 0 covariance)
      (fun x => (innerSL Real (WithLp.toLp 2 weight)) x) = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id]
    simp
  calc
    integral P (fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega)) =
        integral (multivariateGaussian 0 covariance)
          (fun x => (innerSL Real (WithLp.toLp 2 weight)) x) := by
      simpa [Function.comp_def] using hcomp
    _ = 0 := hmeanMeasure

/-- Under a centered finite multivariate Gaussian law, the deterministic
coordinate score has variance equal to its covariance quadratic form. -/
theorem finiteGaussianScore_variance
    [DecidableEq I]
    {P : Measure O} {Z : O -> EuclideanSpace Real I}
    {covariance : Matrix I I Real} {weight : I -> Real}
    (hZ : HasLaw Z (multivariateGaussian 0 covariance) P)
    (hcovariance : covariance.PosSemidef) :
    variance (finiteGaussianScore weight Z) P =
      quadraticForm covariance weight := by
  have hscore_eq : finiteGaussianScore weight Z =
      fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega) := by
    funext omega
    exact finiteGaussianScore_eq_inner weight Z omega
  rw [hscore_eq]
  have hscoreG : HasGaussianLaw
      (fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega)) P :=
    hZ.hasGaussianLaw.map_fun (innerSL Real (WithLp.toLp 2 weight))
  have hmem : MemLp id 2 (multivariateGaussian 0 covariance) :=
    IsGaussian.memLp_two_id
  calc
    variance (fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega)) P =
        cov[fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega),
          fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega); P] :=
      (covariance_self hscoreG.aemeasurable).symm
    _ = cov[fun x => (innerSL Real (WithLp.toLp 2 weight)) x,
          fun x => (innerSL Real (WithLp.toLp 2 weight)) x;
          multivariateGaussian 0 covariance] :=
      hZ.covariance_fun_comp
        ((innerSL Real (WithLp.toLp 2 weight)).continuous.aemeasurable)
        ((innerSL Real (WithLp.toLp 2 weight)).continuous.aemeasurable)
    _ = covarianceBilin (multivariateGaussian 0 covariance)
          (WithLp.toLp 2 weight) (WithLp.toLp 2 weight) :=
      (covarianceBilin_apply_eq_cov hmem (WithLp.toLp 2 weight)
        (WithLp.toLp 2 weight)).symm
    _ = quadraticForm covariance weight := by
      simpa [quadraticForm] using
        covarianceBilin_multivariateGaussian hcovariance
          (WithLp.toLp 2 weight) (WithLp.toLp 2 weight)

/-- Positive semidefiniteness makes the `NNReal` variance parameter in
`finiteGaussianScore_hasLaw` an exact representation of the real quadratic
form. -/
theorem finiteGaussianScore_varianceParameter_coe
    {covariance : Matrix I I Real} {weight : I -> Real}
    (hcovariance : covariance.PosSemidef) :
    ((quadraticForm covariance weight).toNNReal : Real) =
      quadraticForm covariance weight := by
  exact Real.coe_toNNReal _ (quadraticForm_nonneg hcovariance weight)

/-- A deterministic finite-coordinate score of a centered multivariate
Gaussian vector has centered univariate Gaussian law.  This theorem is a
post-conditioning statement: the supplied measure `P` is already fixed. -/
theorem finiteGaussianScore_hasLaw
    [DecidableEq I]
    {P : Measure O} {Z : O -> EuclideanSpace Real I}
    {covariance : Matrix I I Real} {weight : I -> Real}
    (hZ : HasLaw Z (multivariateGaussian 0 covariance) P)
    (hcovariance : covariance.PosSemidef) :
    HasLaw (finiteGaussianScore weight Z)
      (gaussianReal 0 (quadraticForm covariance weight).toNNReal) P := by
  have hscore_eq : finiteGaussianScore weight Z =
      fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega) := by
    funext omega
    exact finiteGaussianScore_eq_inner weight Z omega
  have hscoreG : HasGaussianLaw
      (fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega)) P :=
    hZ.hasGaussianLaw.map_fun (innerSL Real (WithLp.toLp 2 weight))
  have hmean : integral P
      (fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega)) = 0 := by
    rw [<- hscore_eq]
    exact finiteGaussianScore_mean hZ
  have hvariance : variance
      (fun omega => (innerSL Real (WithLp.toLp 2 weight)) (Z omega)) P =
      quadraticForm covariance weight := by
    rw [<- hscore_eq]
    exact finiteGaussianScore_variance hZ hcovariance
  rw [hscore_eq]
  exact {
    aemeasurable := hscoreG.aemeasurable
    map_eq := by
      calc
        Measure.map (fun omega =>
            (innerSL Real (WithLp.toLp 2 weight)) (Z omega)) P =
            gaussianReal
              (integral P (fun omega =>
                (innerSL Real (WithLp.toLp 2 weight)) (Z omega)))
              (variance (fun omega =>
                (innerSL Real (WithLp.toLp 2 weight)) (Z omega)) P).toNNReal :=
          hscoreG.map_eq_gaussianReal
        _ = gaussianReal 0
              (quadraticForm covariance weight).toNNReal := by
          rw [hmean, hvariance]
  }

end

end InfillGLSLean
