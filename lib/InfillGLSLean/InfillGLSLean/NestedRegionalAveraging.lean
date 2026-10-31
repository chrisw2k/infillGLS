module

public import InfillGLSLean.RegionalConditionalExpectation

public section

/-!
# Nested regional averaging

For nested regional resolutions, averaging first at a finer resolution and
then at a coarser one agrees almost everywhere with averaging directly at the
coarser resolution.  This is the conditional-expectation tower property and
is the exact projection compatibility needed by nested partition arguments.

The module does not identify geographic cells with sigma algebras or establish
the manuscript's nonnested refinement-in-measure condition.
-/

namespace InfillGLSLean

open MeasureTheory

variable {Ω : Type*} {mCoarse mFine m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Averaging to a finer regional sigma algebra and then to a coarser one is
the same, almost everywhere, as averaging directly to the coarser regions. -/
theorem nestedRegionalAverage_tower_ae [IsFiniteMeasure μ]
    (hCoarseFine : mCoarse ≤ mFine) (hFine : mFine ≤ m0) (f : Ω → ℝ) :
    μ[μ[f | mFine] | mCoarse] =ᵐ[μ] μ[f | mCoarse] :=
  condExp_condExp_of_le hCoarseFine hFine

/-- The innovation obtained by refining regional averages has zero average on
every coarser resolution, expressed as a zero conditional expectation. -/
theorem nestedRegionalAverage_increment_condExp_zero_ae [IsFiniteMeasure μ]
    (hCoarseFine : mCoarse ≤ mFine) (hFine : mFine ≤ m0) (f : Ω → ℝ) :
    μ[(μ[f | mFine] - μ[f | mCoarse]) | mCoarse] =ᵐ[μ] 0 := by
  have hsub :=
    condExp_sub (f := μ[f | mFine]) (g := μ[f | mCoarse])
      (integrable_condExp : Integrable (μ[f | mFine]) μ)
      (integrable_condExp : Integrable (μ[f | mCoarse]) μ) mCoarse
  have htower :
      μ[μ[f | mFine] | mCoarse] =ᵐ[μ] μ[f | mCoarse] :=
    nestedRegionalAverage_tower_ae (μ := μ) hCoarseFine hFine f
  have hid : μ[μ[f | mCoarse] | mCoarse] = μ[f | mCoarse] :=
    regionalAverage_idempotent (μ := μ) (m := mCoarse) (m0 := m0)
      (hCoarseFine.trans hFine) f
  calc
    μ[(μ[f | mFine] - μ[f | mCoarse]) | mCoarse] =ᵐ[μ]
        μ[μ[f | mFine] | mCoarse] - μ[μ[f | mCoarse] | mCoarse] := hsub
    _ =ᵐ[μ] μ[f | mCoarse] - μ[f | mCoarse] :=
      by
        filter_upwards [htower] with ω hω
        change μ[μ[f | mFine] | mCoarse] ω - μ[μ[f | mCoarse] | mCoarse] ω =
          μ[f | mCoarse] ω - μ[f | mCoarse] ω
        rw [hω, hid]
    _ =ᵐ[μ] 0 := by
      filter_upwards with ω
      simp

/-- The residual after fine regional averaging has zero coarser regional
average. -/
theorem nestedRegionalAverage_fineResidual_condExp_zero_ae [IsFiniteMeasure μ]
    (hCoarseFine : mCoarse ≤ mFine) (hFine : mFine ≤ m0) (f : Ω → ℝ)
    (hf : Integrable f μ) :
    μ[(f - μ[f | mFine]) | mCoarse] =ᵐ[μ] 0 := by
  have hsub :=
    condExp_sub (f := f) (g := μ[f | mFine])
      hf
      (integrable_condExp : Integrable (μ[f | mFine]) μ) mCoarse
  have htower :
      μ[μ[f | mFine] | mCoarse] =ᵐ[μ] μ[f | mCoarse] :=
    nestedRegionalAverage_tower_ae (μ := μ) hCoarseFine hFine f
  calc
    μ[(f - μ[f | mFine]) | mCoarse] =ᵐ[μ]
        μ[f | mCoarse] - μ[μ[f | mFine] | mCoarse] := hsub
    _ =ᵐ[μ] μ[f | mCoarse] - μ[f | mCoarse] :=
      by
        filter_upwards [htower] with ω hω
        change μ[f | mCoarse] ω - μ[μ[f | mFine] | mCoarse] ω =
          μ[f | mCoarse] ω - μ[f | mCoarse] ω
        rw [hω]
    _ =ᵐ[μ] 0 := by
      filter_upwards with ω
      simp

end InfillGLSLean
