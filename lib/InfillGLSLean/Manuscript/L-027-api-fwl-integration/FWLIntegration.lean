module

public import ManuscriptSpecification
public import «L-023-fwl-source-bridge».Explore

/-!
# Exact finite FWL bridge over the manuscript specification

Source: `the source manuscript`, equations `eq:information`,
`eq:estimator`, and `eq:FWL` (with the eventual full-rank condition in
`reg:maps`).  This module states the finite and tail equalities directly over
the review specification; it does not alter a source hypothesis or a main
proposition.
-/

/-!
This module packaging and public-import boundary are visibility-only.  The
three existing endpoint theorems below retain their exact statements and proof
bodies; no manuscript assumption, proposition, dependency, or toolchain is
changed.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L027

open Filter Matrix

universe v

variable {D : CompactEuclideanDomain}
variable {Ω : Type v} [MeasurableSpace Ω]
variable {μ : MeasureTheory.Measure (Point D)}
variable {P : MeasureTheory.Measure Ω}

private theorem regionalDesign_eq_sourceDesign
    (maps : RegionalMaps μ) (treatment : Point D → ℝ)
    (controls : Fin q → Point D → ℝ) (n : ℕ) :
    regionalDesign μ maps treatment controls n =
      InfillGLSLean.L023.sourceDesign
        (regionalValues μ maps treatment n)
        (regionalControls μ maps controls n) := by
  ext i j
  simp only [regionalDesign_apply, InfillGLSLean.L023.sourceDesign_apply]

private theorem source_minimum_iff
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (x : ι → ℝ) (W : Matrix ι κ ℝ) (Q : ℝ) :
    InfillGLSLean.L023.IsSourceTreatmentInformation K x W Q ↔
      IsTreatmentInformation K x W Q := by
  rw [InfillGLSLean.L023.isSourceTreatmentInformation_iff,
    isTreatmentInformation_iff]

private theorem source_minimizer_iff
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (x : ι → ℝ) (W : Matrix ι κ ℝ)
    (y : ι → ℝ) (b : ℝ) (g : κ → ℝ) :
    InfillGLSLean.L023.IsSourceGLSMinimizer K x W y b g ↔
      IsGLSMinimizer K x W y b g := by
  rw [InfillGLSLean.L023.isSourceGLSMinimizer_iff, isGLSMinimizer_iff]
  simp only [InfillGLSLean.L023.sourceGLSObjective_eq, glsObjective_eq]

/-- At a source full-rank resolution, the literal `eq:information` minimum
carried by the experiment agrees with the residualized FWL information. -/
theorem information_eq_controlInformation_of_full_rank
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    E.information n = InfillGLSLean.controlInformation (E.kernel n)⁻¹
      (regionalControls μ E.maps E.controls n)
      (regionalValues μ E.maps E.treatment n) := by
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign
        (regionalValues μ E.maps E.treatment n)
        (regionalControls μ E.maps E.controls n)).rank = E.q + 1 := by
    rw [← regionalDesign_eq_sourceDesign E.maps E.treatment E.controls n]
    exact hfull
  have hsource := InfillGLSLean.L023.sourceInformation_of_full_rank
    (E.kernel n) (E.kernel_posDef n)
    (regionalValues μ E.maps E.treatment n)
    (regionalControls μ E.maps E.controls n) hfull_source
  have hsource' : IsTreatmentInformation (E.kernel n)
      (regionalValues μ E.maps E.treatment n)
      (regionalControls μ E.maps E.controls n)
      (InfillGLSLean.controlInformation (E.kernel n)⁻¹
        (regionalControls μ E.maps E.controls n)
        (regionalValues μ E.maps E.treatment n)) :=
    (source_minimum_iff _ _ _ _).mp hsource
  rcases (isTreatmentInformation_iff _ _ _ _).mp (E.information_is_minimum n) with
    ⟨⟨ell, hE⟩, hElower⟩
  rcases hsource' with ⟨⟨ellSource, hSource⟩, hSourceLower⟩
  apply le_antisymm
  · calc
      E.information n ≤ InfillGLSLean.quadraticForm (E.kernel n)⁻¹
          (regionalValues μ E.maps E.treatment n -
            (regionalControls μ E.maps E.controls n) *ᵥ ellSource) :=
        hElower ellSource
      _ = InfillGLSLean.controlInformation (E.kernel n)⁻¹
          (regionalControls μ E.maps E.controls n)
          (regionalValues μ E.maps E.treatment n) := hSource.symm
  · calc
      InfillGLSLean.controlInformation (E.kernel n)⁻¹
          (regionalControls μ E.maps E.controls n)
          (regionalValues μ E.maps E.treatment n) ≤
          InfillGLSLean.quadraticForm (E.kernel n)⁻¹
            (regionalValues μ E.maps E.treatment n -
              (regionalControls μ E.maps E.controls n) *ᵥ ell) := hSourceLower ell
      _ = E.information n := hE.symm

/-- Tail form of the `eq:information` bridge: the experiment's literal
minimum agrees eventually with the FWL residual information. -/
theorem eventually_information_eq_controlInformation
    (E : FixedConditionalExperiment μ P) :
    ∀ᶠ n in atTop,
      E.information n = InfillGLSLean.controlInformation (E.kernel n)⁻¹
        (regionalControls μ E.maps E.controls n)
        (regionalValues μ E.maps E.treatment n) := by
  rcases E.eventual_full_rank with ⟨n₀, hfull⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  exact information_eq_controlInformation_of_full_rank E n (hfull n hn)

/-- The source's eventual full rank, positive-definite working covariance,
and selected `eq:estimator` minimizer imply the exact `eq:FWL` expression. -/
theorem estimatorHasFWLForm_of_fixedLawHypotheses
    (E : FixedConditionalExperiment μ P) :
    estimatorHasFWLForm E := by
  rw [estimatorHasFWLForm_iff]
  rcases E.eventual_full_rank with ⟨n₀, hfull⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  intro ω
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign
        (regionalValues μ E.maps E.treatment n)
        (regionalControls μ E.maps E.controls n)).rank = E.q + 1 := by
    rw [← regionalDesign_eq_sourceDesign E.maps E.treatment E.controls n]
    exact hfull n hn
  have hmin_source : InfillGLSLean.L023.IsSourceGLSMinimizer
      (E.kernel n)
      (regionalValues μ E.maps E.treatment n)
      (regionalControls μ E.maps E.controls n)
      (fun i => regionalRandomValues μ E.maps E.outcome n i ω)
      (E.betaHat n ω) (E.gammaHat n ω) :=
    (source_minimizer_iff _ _ _ _ _ _).mpr (E.estimator_minimizes n ω)
  have hfwl := InfillGLSLean.L023.sourceGLSMinimizer_beta_eq_fwl_of_full_rank
    (E.kernel n) (E.kernel_posDef n)
    (regionalValues μ E.maps E.treatment n)
    (fun i => regionalRandomValues μ E.maps E.outcome n i ω)
    (regionalControls μ E.maps E.controls n)
    (E.betaHat n ω) (E.gammaHat n ω) hfull_source hmin_source
  simpa only [fwlSlope_eq] using hfwl

end InfillGLSLean.ManuscriptSpecification.L027
