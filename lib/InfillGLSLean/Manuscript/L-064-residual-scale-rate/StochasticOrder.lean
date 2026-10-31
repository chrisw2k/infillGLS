module

public import InfillGLSLean.ResidualMomentCore
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic

/-!
# Standard stochastic-order vocabulary for Appendix `lem:scale`

The paper uses `O_p` once, in the displayed residual-scale rate at
`the source manuscript:623`, without separately introducing notation.  This
task-local module records the conventional tail-probability meaning: after
division by a deterministic scale, the random sequence is bounded in
probability.  The definition is the same `O_p(1)` tail convention used by the
open Lean econometrics formalization of Hansen's *Econometrics*; it is local
here because the pinned Mathlib revision has deterministic `IsBigO` but no
stochastic-order API.

It is deliberately a foundational helper only.  The source-facing rate
decomposition is proved in `ResidualScaleRate.lean`.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L064

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

universe v

/-- A real random sequence is bounded in probability when every positive
probability tolerance admits an eventually valid deterministic norm bound.
This is standard `O_p(1)` tail semantics. -/
@[expose]
def BoundedInProbability {Omega : Type v} [MeasurableSpace Omega]
    (P : Measure Omega) (X : Nat → Omega → Real) : Prop :=
  ∀ epsilon : ENNReal, 0 < epsilon → ∃ M : Real, 0 < M ∧
    ∀ᶠ n in atTop, P {omega | M ≤ ‖X n omega‖} ≤ epsilon

/-- Standard stochastic big-O: `X = O_p(a)` means the deterministic-scale
normalization `a_n⁻¹ X_n` is bounded in probability.  As usual, only tail
behavior matters, so values of a scale at finitely many indices are harmless. -/
@[expose]
def IsStochasticBigO {Omega : Type v} [MeasurableSpace Omega]
    (P : Measure Omega) (X : Nat → Omega → Real) (a : Nat → Real) : Prop :=
  BoundedInProbability P (fun n omega => (a n)⁻¹ * X n omega)

/-- Public definitional expansion of standard stochastic big-O.  This is a
visibility-only API bridge for downstream source-facing rate proofs. -/
theorem isStochasticBigO_iff {Omega : Type v} [MeasurableSpace Omega]
    (P : Measure Omega) (X : Nat → Omega → Real) (a : Nat → Real) :
    IsStochasticBigO P X a ↔
      BoundedInProbability P (fun n omega => (a n)⁻¹ * X n omega) :=
  Iff.rfl

/-- Finite second-moment identity for a real statistic about an arbitrary
deterministic center.  This is the elementary identity behind the later
Chebyshev step: variance plus squared bias equals the uncentered second
moment. -/
theorem integral_sq_sub_const_eq_variance_add_bias_sq
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {X : Omega → Real} (hX : MemLp X 2 P)
    (c : Real) :
    (∫ omega, (X omega - c) ^ 2 ∂P) =
      Var[X; P] + ((∫ omega, X omega ∂P) - c) ^ 2 := by
  have hXsq : Integrable (fun omega => X omega ^ 2) P :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hX
  have hXint : Integrable X P := hX.integrable (by norm_num)
  have hlinear : Integrable (fun omega => (2 * c) * X omega) P :=
    hXint.const_mul (2 * c)
  have hpoint : (fun omega => (X omega - c) ^ 2) =
      fun omega => (X omega ^ 2 - (2 * c) * X omega) + c ^ 2 := by
    funext omega
    ring
  calc
    (∫ omega, (X omega - c) ^ 2 ∂P) =
        ∫ omega, (X omega ^ 2 - (2 * c) * X omega) + c ^ 2 ∂P := by
      exact congrArg (fun f => ∫ omega, f omega ∂P) hpoint
    _ = (∫ omega, X omega ^ 2 - (2 * c) * X omega ∂P) + c ^ 2 := by
      change (∫ omega,
          (fun omega => X omega ^ 2 - (2 * c) * X omega) omega +
            (fun _ : Omega => c ^ 2) omega ∂P) = _
      calc
        (∫ omega,
            (fun omega => X omega ^ 2 - (2 * c) * X omega) omega +
              (fun _ : Omega => c ^ 2) omega ∂P) =
            (∫ omega, X omega ^ 2 - (2 * c) * X omega ∂P) +
              ∫ _omega : Omega, c ^ 2 ∂P :=
          integral_add (hXsq.sub hlinear) (integrable_const _)
        _ = (∫ omega, X omega ^ 2 - (2 * c) * X omega ∂P) + c ^ 2 := by
          simp
    _ = (∫ omega, X omega ^ 2 ∂P) - (2 * c) * (∫ omega, X omega ∂P) + c ^ 2 := by
      rw [integral_sub hXsq hlinear, integral_const_mul]
    _ = Var[X; P] + ((∫ omega, X omega ∂P) - c) ^ 2 := by
      rw [ProbabilityTheory.variance_eq_sub hX]
      simp only [Pi.pow_apply]
      ring

/-- A direct Markov bound for a real square-integrable random variable about
zero. -/
private theorem measure_norm_ge_le_integral_sq_div_sq
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {X : Omega → Real}
    (hX : MemLp X 2 P) {M : Real} (hM : 0 < M) :
    P {omega | M ≤ ‖X omega‖} ≤
      ENNReal.ofReal ((∫ omega, X omega ^ 2 ∂P) / M ^ 2) := by
  have hXsq : Integrable (fun omega => X omega ^ 2) P :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hX
  have hset : {omega | M ≤ ‖X omega‖} = {omega | M ^ 2 ≤ X omega ^ 2} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs]
    constructor
    · intro h
      have hsq : M ^ 2 ≤ |X omega| ^ 2 :=
        (sq_le_sq₀ hM.le (abs_nonneg _)).2 h
      simpa only [sq_abs] using hsq
    · intro h
      have hsq : M ^ 2 ≤ |X omega| ^ 2 := by
        simpa only [sq_abs] using h
      exact (sq_le_sq₀ hM.le (abs_nonneg _)).1 hsq
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun omega => X omega ^ 2)
    (Filter.Eventually.of_forall fun omega => sq_nonneg (X omega)) hXsq (M ^ 2)
  rw [hset]
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  have hreal : P.real {omega | M ^ 2 ≤ X omega ^ 2} ≤
      (∫ omega, X omega ^ 2 ∂P) / M ^ 2 := by
    apply (le_div_iff₀ hM2).2
    simpa [mul_comm] using hmarkov
  rw [← ENNReal.ofReal_toReal (measure_ne_top P {omega | M ^ 2 ≤ X omega ^ 2})]
  exact ENNReal.ofReal_le_ofReal hreal

/-- An eventual uniform second-moment bound implies standard boundedness in
probability.  This is the finite-moment/Markov bridge used below for the
normalized residual-scale remainder. -/
theorem boundedInProbability_of_eventually_integral_sq_le
    {Omega : Type v} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {X : Nat → Omega → Real} {K : Real}
    (hK : 0 ≤ K) (hmem : ∀ᶠ n in atTop, MemLp (X n) 2 P)
    (hbound : ∀ᶠ n in atTop, (∫ omega, X n omega ^ 2 ∂P) ≤ K) :
    BoundedInProbability P X := by
  intro epsilon hepsilon
  by_cases hepsTop : epsilon = ∞
  · refine ⟨1, zero_lt_one, Eventually.of_forall ?_⟩
    intro n
    rw [hepsTop]
    exact le_top
  have hepsPos : 0 < epsilon.toReal :=
    ENNReal.toReal_pos (ne_of_gt hepsilon) hepsTop
  let M : Real := K / epsilon.toReal + 1
  have hM : 0 < M := by
    dsimp [M]
    have : 0 ≤ K / epsilon.toReal := div_nonneg hK hepsPos.le
    linarith
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  have hKlt : K < epsilon.toReal * M ^ 2 := by
    have hMgt : K / epsilon.toReal < M := by
      dsimp [M]
      linarith
    have hMleM2 : M ≤ M ^ 2 := by
      nlinarith [show 1 ≤ M by
        dsimp [M]
        have : 0 ≤ K / epsilon.toReal := div_nonneg hK hepsPos.le
        linarith]
    have hKM : K < epsilon.toReal * M := by
      calc
        K = epsilon.toReal * (K / epsilon.toReal) := by
          field_simp [hepsPos.ne']
        _ < epsilon.toReal * M := mul_lt_mul_of_pos_left hMgt hepsPos
    exact lt_of_lt_of_le hKM
      (mul_le_mul_of_nonneg_left hMleM2 hepsPos.le)
  have hratio : K / M ^ 2 < epsilon.toReal := by
    apply (div_lt_iff₀ hM2).2
    nlinarith [hKlt]
  refine ⟨M, hM, ?_⟩
  filter_upwards [hmem, hbound] with n hmemn hboundn
  calc
    P {omega | M ≤ ‖X n omega‖} ≤
        ENNReal.ofReal ((∫ omega, X n omega ^ 2 ∂P) / M ^ 2) :=
      measure_norm_ge_le_integral_sq_div_sq hmemn hM
    _ ≤ ENNReal.ofReal (K / M ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right hboundn (le_of_lt hM2))
    _ ≤ ENNReal.ofReal epsilon.toReal := le_of_lt
      ((ENNReal.ofReal_lt_ofReal_iff hepsPos).2 hratio)
    _ = epsilon := ENNReal.ofReal_toReal hepsTop

end InfillGLSLean.ManuscriptSpecification.L064

end
