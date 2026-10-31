module

public import «L-050-mean-weak-score-integration».WeakScoreIntegration
public import «L-048-mean-treatment-variance-sandwich».TreatmentVarianceSandwich

/-!
# Fixed-representer evaluation for Appendix `lem:mean`

This module formalizes exactly the sentence following the covariance-Hilbert
weak convergence argument: evaluating the normalized true-GLS score against
the one fixed representer of the mean residual yields the negligible
true-GLS mean contribution.  It does not transfer to working weights or make
any distributional conclusion.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L052

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal RealInnerProductSpace

open InfillGLSLean.ManuscriptSpecification.L037
open InfillGLSLean.ManuscriptSpecification.L044
open InfillGLSLean.ManuscriptSpecification.L047
open InfillGLSLean.ManuscriptSpecification.L050
open InfillGLSLean.MeanHilbertRiesz

universe v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The finite true-GLS mean score is the covariance-Hilbert pairing of its
true-GLS regional score with any fixed representer of the spatial mean
residual.  This is the literal finite bridge needed to evaluate L-050's weak
limit; it uses the same regional cell test on both sides. -/
theorem meanOffset_dot_trueGLSOutcomeWeight_eq_inner_trueGLSRegionalScore
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : covarianceHilbertSpace E covariance)
    (hrepresentation : centeredErrorPairingL2 E (V : Lp ℝ 2 P) =
      spatialMeanOffsetL2 E c)
    (n : ℕ) :
    meanOffset E c n ⬝ᵥ
        trueGLSOutcomeWeight (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) 0 =
      inner ℝ (trueGLSRegionalScore E covariance n 0) V := by
  let weight := trueGLSOutcomeWeight (trueCovariance E n)
    (regionalDesign μ E.maps E.treatment E.controls n) 0
  let test := weightedRegionalCellTestLp E n weight
  calc
    meanOffset E c n ⬝ᵥ weight =
        spatialMeanOffsetFunctional E c test :=
      (spatialMeanOffsetFunctional_weightedRegionalCellTest E c n weight).symm
    _ = inner ℝ (spatialMeanOffsetL2 E c) test :=
      spatialMeanOffsetFunctional_eq_inner E c test
    _ = inner ℝ (centeredErrorPairingL2 E (V : Lp ℝ 2 P)) test := by
      rw [hrepresentation]
    _ = inner ℝ (V : Lp ℝ 2 P) (centeredTestIntegralLp E covariance test) :=
      inner_centeredErrorPairingL2_eq_inner_centeredTestIntegralLp E covariance test
        (V : Lp ℝ 2 P)
    _ = inner ℝ V (trueGLSRegionalScore E covariance n 0) := by
      rfl
    _ = inner ℝ (trueGLSRegionalScore E covariance n 0) V := by
      rw [real_inner_comm]

/-- The preceding finite pairing after the exact true-score normalization.
The denominator is written as L-047's unchanged treatment variance `v_n`.
No positivity or limiting premise is needed for this algebraic identity. -/
theorem normalizedTrueGLSRegionalScore_inner_representer_eq
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (c : Fin E.q → ℝ) (V : covarianceHilbertSpace E covariance)
    (hrepresentation : centeredErrorPairingL2 E (V : Lp ℝ 2 P) =
      spatialMeanOffsetL2 E c)
    (n : ℕ) :
    inner ℝ (normalizedTrueGLSRegionalScore E covariance n 0) V =
      (trueGLSOutcomeWeight (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) 0 ⬝ᵥ meanOffset E c n) /
        Real.sqrt (observedTrueGLSTreatmentVariance E n) := by
  calc
    inner ℝ (normalizedTrueGLSRegionalScore E covariance n 0) V =
        (Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) 0 0))⁻¹ *
          inner ℝ (trueGLSRegionalScore E covariance n 0) V := by
      rw [normalizedTrueGLSRegionalScore]
      simpa using (inner_smul_left (trueGLSRegionalScore E covariance n 0) V
        (Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) 0 0))⁻¹)
    _ = (meanOffset E c n ⬝ᵥ
          trueGLSOutcomeWeight (trueCovariance E n)
            (regionalDesign μ E.maps E.treatment E.controls n) 0) /
          Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
            (regionalDesign μ E.maps E.treatment E.controls n) 0 0) := by
      rw [← meanOffset_dot_trueGLSOutcomeWeight_eq_inner_trueGLSRegionalScore
        E covariance c V hrepresentation n]
      simp [div_eq_mul_inv, mul_comm]
    _ = (trueGLSOutcomeWeight (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) 0 ⬝ᵥ meanOffset E c n) /
          Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
            (regionalDesign μ E.maps E.treatment E.controls n) 0 0) := by
      rw [dotProduct_comm]
    _ = _ := by
      rw [observedTrueGLSTreatmentVariance_eq,
        observedTrueGLSCoefficientCovariance_eq]

/-- Exact source-level conclusion obtained by evaluating L-050's weak score
limit at L-036's one fixed representer of the mean residual.  This is the
paper's `ω_n^{*\top} f_n / sqrt(v_n) → 0`, on the explicitly reindexed tail
where the finite true-GLS matrices are guaranteed nonsingular. -/
theorem exists_reindexed_trueGLS_mean_bias_div_sqrt_variance_tendsto_zero
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (mean : FixedMeanAssumption E) :
    ∃ start : ℕ,
      Tendsto (fun n =>
        (trueGLSOutcomeWeight (trueCovariance E (n + start))
          (regionalDesign μ E.maps E.treatment E.controls (n + start)) 0 ⬝ᵥ
          meanOffset E mean.c (n + start)) /
          Real.sqrt (observedTrueGLSTreatmentVariance E (n + start)))
        atTop (nhds 0) := by
  rcases exists_covarianceHilbert_spatial_representer_of_fixedMeanAssumption
      E covariance mean with ⟨V, hrepresentation⟩
  rcases exists_reindexed_normalizedTrueGLSRegionalScore_weakly_tendsto_zero
      E covariance with ⟨start, hweak⟩
  refine ⟨start, ?_⟩
  simpa only [normalizedTrueGLSRegionalScore_inner_representer_eq E covariance
    mean.c V hrepresentation] using hweak V

end InfillGLSLean.ManuscriptSpecification.L052

end
