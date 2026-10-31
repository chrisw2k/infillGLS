module

public import InfillGLSLean
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Finite positive-semidefinite support for Appendix `lem:mean`

This file isolates only the finite-dimensional positive-semidefinite algebra
used after the common-refinement information-limit construction in
`the source manuscript:559-567`.  It does not construct a spatial
refinement sequence or add a nesting condition to observed partitions.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L040

open Filter Matrix Set Topology

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Coordinate Cauchy--Schwarz for a real positive-semidefinite matrix.
This is the finite matrix fact used when the manuscript applies positivity of
`B_n - B` to two coefficient coordinates. -/
theorem posSemidef_entry_sq_le_diag_mul_diag
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    (A i j) ^ 2 ≤ A i i * A j j := by
  have hnonneg : ∀ x : ι → ℝ, 0 ≤ A.toBilin' x x := by
    intro x
    rw [Matrix.toBilin'_apply']
    simpa using hA.dotProduct_mulVec_nonneg x
  have hsymm : A.toBilin'.IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr hA.isHermitian.isSymm
  have hsymm' : LinearMap.IsSymm A.toBilin' :=
    LinearMap.BilinForm.isSymm_iff.mp hsymm
  simpa using LinearMap.BilinForm.apply_sq_le_of_symm A.toBilin' hnonneg hsymm'
    (Pi.single i 1) (Pi.single j 1)

/-- The square-root form of coordinate Cauchy--Schwarz.  It is separated from
the matrix statement so the final manuscript inequality can use the literal
positive variance `v_n` as its denominator. -/
theorem abs_div_sqrt_le_sqrt_of_sq_le
    {a b c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hbc : b ^ 2 ≤ a * c) :
    |b| / Real.sqrt a ≤ Real.sqrt c := by
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have htarget_sq : |b| ^ 2 ≤ (Real.sqrt a * Real.sqrt c) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt hc]
    exact hbc
  have habs : |b| ≤ Real.sqrt a * Real.sqrt c :=
    (sq_le_sq₀ (abs_nonneg b)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp htarget_sq
  apply (div_le_iff₀ hsqrta).mpr
  simpa [mul_comm] using habs

/-- The precise finite-coordinate consequence used in the final displayed
inequality of the `lem:mean` proof.  `upper` is the observed coefficient
covariance `B_n`, `lower` is its information-limit lower bound `B`, and the
two zero assumptions express the already-derived vanishing limit row. -/
theorem normalized_coordinate_bound_of_posSemidef_sub
    {lower upper : Matrix ι ι ℝ} (horder : (upper - lower).PosSemidef)
    (i j : ι) (hlower_ii : lower i i = 0) (hlower_ij : lower i j = 0)
    (hupper_ii : 0 < upper i i) :
    |upper i j| / Real.sqrt (upper i i) ≤ Real.sqrt ((upper - lower) j j) := by
  have hdiag : 0 ≤ (upper - lower) j j := horder.diag_nonneg
  have hsq := posSemidef_entry_sq_le_diag_mul_diag horder i j
  apply abs_div_sqrt_le_sqrt_of_sq_le hupper_ii hdiag
  simpa [hlower_ii, hlower_ij] using hsq

/- If every finite covariance matrix dominates a positive-semidefinite lower
matrix and one fixed diagonal coordinate tends to zero, that lower diagonal
coordinate is zero. -/
omit [Fintype ι] [DecidableEq ι] in
theorem lower_diagonal_eq_zero_of_tendsto_upper_diagonal_zero
    (B : Matrix ι ι ℝ) (upper : ℕ → Matrix ι ι ℝ)
    (hB : B.PosSemidef)
    (hlower : ∀ n, (upper n - B).PosSemidef)
    (i : ι) (hdiag : Tendsto (fun n => upper n i i) atTop (nhds 0)) :
    B i i = 0 := by
  have hnonneg : 0 ≤ B i i := hB.diag_nonneg
  have hbelow : ∀ n, B i i ≤ upper n i i := by
    intro n
    have hdifference : 0 ≤ (upper n - B) i i := (hlower n).diag_nonneg
    exact sub_nonneg.mp hdifference
  have hle : B i i ≤ 0 :=
    ge_of_tendsto hdiag (Eventually.of_forall hbelow)
  exact le_antisymm hle hnonneg

/-- A zero diagonal coordinate of a real positive-semidefinite matrix forces
its entire corresponding row to vanish. -/
theorem posSemidef_entry_eq_zero_of_diag_eq_zero
    {B : Matrix ι ι ℝ} (hB : B.PosSemidef) (i j : ι)
    (hdiag : B i i = 0) :
    B i j = 0 := by
  have hsq := posSemidef_entry_sq_le_diag_mul_diag hB i j
  have hle : (B i j) ^ 2 ≤ 0 := by
    calc
      (B i j) ^ 2 ≤ B i i * B j j := hsq
      _ = 0 := by simp [hdiag]
  nlinarith [sq_nonneg (B i j)]

/-- The limit-row conclusion used immediately before the manuscript's
normalized coordinate inequality. -/
theorem lower_row_eq_zero_of_tendsto_upper_diagonal_zero
    (B : Matrix ι ι ℝ) (upper : ℕ → Matrix ι ι ℝ)
    (hB : B.PosSemidef)
    (hlower : ∀ n, (upper n - B).PosSemidef)
    (i j : ι) (hdiag : Tendsto (fun n => upper n i i) atTop (nhds 0)) :
    B i j = 0 := by
  apply posSemidef_entry_eq_zero_of_diag_eq_zero hB i j
  exact lower_diagonal_eq_zero_of_tendsto_upper_diagonal_zero B upper
    hB hlower i hdiag

/-- The paper's displayed normalized-coordinate inequality, with the
vanishing limit row derived from the lower order and the shrinking diagonal
rather than supplied separately. -/
theorem normalized_coordinate_bound_of_lower_order_and_tendsto_diagonal_zero
    (B : Matrix ι ι ℝ) (upper : ℕ → Matrix ι ι ℝ)
    (hB : B.PosSemidef)
    (hlower : ∀ n, (upper n - B).PosSemidef)
    (i j : ι) (hdiag : Tendsto (fun n => upper n i i) atTop (nhds 0))
    (n : ℕ) (hupper_ii : 0 < upper n i i) :
    |upper n i j| / Real.sqrt (upper n i i) ≤
      Real.sqrt ((upper n - B) j j) := by
  apply normalized_coordinate_bound_of_posSemidef_sub (hlower n) i j
  · exact lower_diagonal_eq_zero_of_tendsto_upper_diagonal_zero B upper
      hB hlower i hdiag
  · exact lower_row_eq_zero_of_tendsto_upper_diagonal_zero B upper
      hB hlower i j hdiag
  · exact hupper_ii

/-! ## Finite descending covariance chains -/

/-- The quadratic form of a coefficient-covariance matrix at a fixed finite
coefficient vector. -/
private noncomputable def coefficientQuadratic
    (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

/-- The scalar lower limit of a descending sequence of coefficient
quadratic forms.  The existence proof below supplies the needed lower bound;
this definition itself introduces no extra premise. -/
private noncomputable def coefficientQuadraticLimit
    (B : ℕ → Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  sInf (Set.range fun n => coefficientQuadratic (B n) x)

omit [DecidableEq ι] in
private theorem coefficientQuadratic_nonneg
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (n : ℕ) (x : ι → ℝ) :
    0 ≤ coefficientQuadratic (B n) x := by
  simpa [coefficientQuadratic] using (hpsd n).dotProduct_mulVec_nonneg x

omit [DecidableEq ι] in
private theorem coefficientQuadratic_antitone
    (B : ℕ → Matrix ι ι ℝ)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef)
    (x : ι → ℝ) :
    Antitone (fun n => coefficientQuadratic (B n) x) := by
  intro m n hmn
  have hnonneg := (hdecreasing m n hmn).dotProduct_mulVec_nonneg x
  change 0 ≤ x ⬝ᵥ ((B m - B n) *ᵥ x) at hnonneg
  rw [sub_mulVec, dotProduct_sub] at hnonneg
  simpa [coefficientQuadratic] using sub_nonneg.mp hnonneg

omit [DecidableEq ι] in
private theorem coefficientQuadratic_bddBelow
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (x : ι → ℝ) :
    BddBelow (Set.range fun n => coefficientQuadratic (B n) x) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact coefficientQuadratic_nonneg B hpsd n x

omit [DecidableEq ι] in
private theorem coefficientQuadratic_tendsto
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef)
    (x : ι → ℝ) :
    Tendsto (fun n => coefficientQuadratic (B n) x) atTop
      (nhds (coefficientQuadraticLimit B x)) := by
  exact tendsto_atTop_ciInf (coefficientQuadratic_antitone B hdecreasing x)
    (coefficientQuadratic_bddBelow B hpsd x)

private theorem posSemidef_entry_eq_quadratic_polarization
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    A i j =
      (coefficientQuadratic A (Pi.single i 1 + Pi.single j 1) -
        coefficientQuadratic A (Pi.single i 1) -
        coefficientQuadratic A (Pi.single j 1)) / 2 := by
  have hsymm : A.toBilin'.IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr hA.isHermitian.isSymm
  simpa [coefficientQuadratic, Matrix.toBilin'_apply'] using
    hsymm.polarization (Pi.single i 1) (Pi.single j 1)

/-- The entrywise candidate for the lower limit of a finite descending
coefficient-covariance chain, obtained by polarization of scalar quadratic
limits. -/
private noncomputable def coefficientCovarianceLimit
    (B : ℕ → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j =>
    (coefficientQuadraticLimit B (Pi.single i 1 + Pi.single j 1) -
      coefficientQuadraticLimit B (Pi.single i 1) -
      coefficientQuadraticLimit B (Pi.single j 1)) / 2

private theorem coefficientCovariance_entry_tendsto
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef)
    (i j : ι) :
    Tendsto (fun n => B n i j) atTop
      (nhds (coefficientCovarianceLimit B i j)) := by
  have hplus := coefficientQuadratic_tendsto B hpsd hdecreasing
    (Pi.single i 1 + Pi.single j 1)
  have hi := coefficientQuadratic_tendsto B hpsd hdecreasing (Pi.single i 1)
  have hj := coefficientQuadratic_tendsto B hpsd hdecreasing (Pi.single j 1)
  have hcomb := ((hplus.sub hi).sub hj).div_const (2 : ℝ)
  convert hcomb using 1
  · ext n
    exact posSemidef_entry_eq_quadratic_polarization (hpsd n) i j
  · rfl

private theorem coefficientCovariance_tendsto
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef) :
    Tendsto B atTop (nhds (coefficientCovarianceLimit B)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact coefficientCovariance_entry_tendsto B hpsd hdecreasing i j

omit [DecidableEq ι] in
private theorem coefficientQuadratic_tendsto_of_matrix_tendsto
    (B : ℕ → Matrix ι ι ℝ) (L : Matrix ι ι ℝ)
    (hmatrix : Tendsto B atTop (nhds L)) (x : ι → ℝ) :
    Tendsto (fun n => coefficientQuadratic (B n) x) atTop
      (nhds (coefficientQuadratic L x)) := by
  have hcontinuous : Continuous (fun A : Matrix ι ι ℝ =>
      coefficientQuadratic A x) := by
    unfold coefficientQuadratic
    fun_prop
  exact (hcontinuous.tendsto L).comp hmatrix

private theorem coefficientQuadraticLimit_eq_limit_quadratic
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef)
    (x : ι → ℝ) :
    coefficientQuadraticLimit B x =
      coefficientQuadratic (coefficientCovarianceLimit B) x := by
  exact tendsto_nhds_unique
    (coefficientQuadratic_tendsto B hpsd hdecreasing x)
    (coefficientQuadratic_tendsto_of_matrix_tendsto B
      (coefficientCovarianceLimit B)
      (coefficientCovariance_tendsto B hpsd hdecreasing) x)

private theorem coefficientCovarianceLimit_isSymm
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef) :
    (coefficientCovarianceLimit B).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have hji := coefficientCovariance_entry_tendsto B hpsd hdecreasing j i
  have hij := coefficientCovariance_entry_tendsto B hpsd hdecreasing i j
  have hsame : (fun n => B n j i) = (fun n => B n i j) := by
    funext n
    exact (hpsd n).isHermitian.isSymm.apply i j
  rw [hsame] at hji
  exact tendsto_nhds_unique hji hij

private theorem coefficientCovarianceLimit_posSemidef
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef) :
    (coefficientCovarianceLimit B).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact (Matrix.isHermitian_iff_isSymm).mpr
      (coefficientCovarianceLimit_isSymm B hpsd hdecreasing)
  · intro x
    have hmatrix := coefficientQuadratic_tendsto_of_matrix_tendsto B
      (coefficientCovarianceLimit B)
      (coefficientCovariance_tendsto B hpsd hdecreasing) x
    change 0 ≤ coefficientQuadratic (coefficientCovarianceLimit B) x
    exact ge_of_tendsto hmatrix
      (Eventually.of_forall fun n => coefficientQuadratic_nonneg B hpsd n x)

private theorem coefficientCovariance_sub_limit_posSemidef
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef)
    (n : ℕ) :
    (B n - coefficientCovarianceLimit B).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact (hpsd n).isHermitian.sub
      (coefficientCovarianceLimit_posSemidef B hpsd hdecreasing).isHermitian
  · intro x
    have hle : coefficientQuadraticLimit B x ≤ coefficientQuadratic (B n) x :=
      (coefficientQuadratic_antitone B hdecreasing x).le_of_tendsto
        (coefficientQuadratic_tendsto B hpsd hdecreasing x) n
    have hlimit := coefficientQuadraticLimit_eq_limit_quadratic B hpsd hdecreasing x
    change 0 ≤ coefficientQuadratic (B n - coefficientCovarianceLimit B) x
    unfold coefficientQuadratic
    rw [sub_mulVec, dotProduct_sub]
    exact sub_nonneg.mpr (by simpa [coefficientQuadratic, hlimit] using hle)

/-- A finite-dimensional descending chain of positive-semidefinite
coefficient covariance matrices has a positive-semidefinite lower limit.
The convergence is entrywise (equivalently, in the finite product topology),
and every chain member dominates that limit in positive-semidefinite order.

This is the matrix-limit step used after the paper has constructed its
separate nested common-refinement chain.  It has no premise about nesting of
the observed regional partitions. -/
theorem exists_coefficientCovariance_limit_of_decreasing
    (B : ℕ → Matrix ι ι ℝ) (hpsd : ∀ n, (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, m ≤ n → (B m - B n).PosSemidef) :
    ∃ L : Matrix ι ι ℝ,
      L.PosSemidef ∧
        (∀ n, (B n - L).PosSemidef) ∧
        Tendsto B atTop (nhds L) := by
  refine ⟨coefficientCovarianceLimit B,
    coefficientCovarianceLimit_posSemidef B hpsd hdecreasing, ?_,
    coefficientCovariance_tendsto B hpsd hdecreasing⟩
  intro n
  exact coefficientCovariance_sub_limit_posSemidef B hpsd hdecreasing n

/-- Tail version of the descending-chain result.  This matches the paper's
wording that the common-refinement designs are full rank only from some fixed
finite resolution onward; shifting to that tail does not add a source
assumption. -/
theorem exists_coefficientCovariance_limit_of_eventually_decreasing
    (B : ℕ → Matrix ι ι ℝ) (start : ℕ)
    (hpsd : ∀ n, start ≤ n → (B n).PosSemidef)
    (hdecreasing : ∀ m n : ℕ, start ≤ m → m ≤ n →
      (B m - B n).PosSemidef) :
    ∃ L : Matrix ι ι ℝ,
      L.PosSemidef ∧
        (∀ n, start ≤ n → (B n - L).PosSemidef) ∧
        Tendsto B atTop (nhds L) := by
  let tail : ℕ → Matrix ι ι ℝ := fun n => B (n + start)
  have htail_psd : ∀ n, (tail n).PosSemidef := by
    intro n
    exact hpsd (n + start) (Nat.le_add_left start n)
  have htail_decreasing : ∀ m n : ℕ, m ≤ n →
      (tail m - tail n).PosSemidef := by
    intro m n hmn
    exact hdecreasing (m + start) (n + start)
      (Nat.le_add_left start m) (Nat.add_le_add_right hmn start)
  rcases exists_coefficientCovariance_limit_of_decreasing tail htail_psd
    htail_decreasing with ⟨L, hL, htail_lower, htail_tendsto⟩
  refine ⟨L, hL, ?_, ?_⟩
  · intro n hn
    simpa [tail, Nat.sub_add_cancel hn] using htail_lower (n - start)
  · apply (tendsto_add_atTop_iff_nat start).mp
    simpa [tail] using htail_tendsto

/-- In finite coefficient dimension, convergence of every covariance
quadratic form determines entrywise matrix convergence.  Positive
semidefiniteness supplies the symmetry needed for the polarization identity. -/
theorem tendsto_matrix_of_quadratic_tendsto
    (A : ℕ → Matrix ι ι ℝ) (L : Matrix ι ι ℝ)
    (hA : ∀ n, (A n).PosSemidef) (hL : L.PosSemidef)
    (hquadratic : ∀ x : ι → ℝ,
      Tendsto (fun n => x ⬝ᵥ ((A n) *ᵥ x)) atTop
        (nhds (x ⬝ᵥ (L *ᵥ x)))) :
    Tendsto A atTop (nhds L) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have hplus := hquadratic (Pi.single i 1 + Pi.single j 1)
  have hi := hquadratic (Pi.single i 1)
  have hj := hquadratic (Pi.single j 1)
  have hcomb := ((hplus.sub hi).sub hj).div_const (2 : ℝ)
  convert hcomb using 1
  · ext n
    simpa [coefficientQuadratic] using
      posSemidef_entry_eq_quadratic_polarization (hA n) i j
  · simpa [coefficientQuadratic] using
      posSemidef_entry_eq_quadratic_polarization hL i j

/-- The finite fixed-refinement comparison argument from the second paragraph
of the manuscript's information-limit proof.  The `hupper` premise is the
epsilon-tail form of its statement that the limit superior of every observed
quadratic form is no larger than that of any fixed common-refinement
experiment.  Together with the lower positive-semidefinite order and a
convergent refinement chain, it yields observed-level matrix convergence.

The theorem is deliberately finite and source-neutral: producing `hupper`
from projected regional averages remains the separate spatial approximation
obligation. -/
theorem tendsto_observed_of_fixed_refinement_comparisons
    (observed refinement : ℕ → Matrix ι ι ℝ) (limit : Matrix ι ι ℝ)
    (hobserved_psd : ∀ n, (observed n).PosSemidef)
    (hlimit_psd : limit.PosSemidef)
    (hlower : ∀ n, (observed n - limit).PosSemidef)
    (hrefinement : Tendsto refinement atTop (nhds limit))
    (hupper : ∀ k (x : ι → ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        x ⬝ᵥ ((observed n) *ᵥ x) ≤ x ⬝ᵥ ((refinement k) *ᵥ x) + ε) :
    Tendsto observed atTop (nhds limit) := by
  apply tendsto_matrix_of_quadratic_tendsto observed limit
    hobserved_psd hlimit_psd
  intro x
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    refine Eventually.of_forall fun n => ?_
    have hnonneg := (hlower n).dotProduct_mulVec_nonneg x
    change 0 ≤ x ⬝ᵥ ((observed n - limit) *ᵥ x) at hnonneg
    rw [sub_mulVec, dotProduct_sub] at hnonneg
    exact ha.trans_le (sub_nonneg.mp hnonneg)
  · intro a ha
    let ε : ℝ := (a - x ⬝ᵥ (limit *ᵥ x)) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hcontinuous : Continuous (fun A : Matrix ι ι ℝ =>
        x ⬝ᵥ (A *ᵥ x)) := by
      fun_prop
    have hrefinement_quadratic :
        Tendsto (fun k => x ⬝ᵥ ((refinement k) *ᵥ x)) atTop
          (nhds (x ⬝ᵥ (limit *ᵥ x))) :=
      (hcontinuous.tendsto limit).comp hrefinement
    have hrefinement_lt : ∀ᶠ k in atTop,
        x ⬝ᵥ ((refinement k) *ᵥ x) < x ⬝ᵥ (limit *ᵥ x) + ε :=
      (tendsto_order.1 hrefinement_quadratic).2 _ (by
        dsimp [ε]
        linarith)
    rcases (eventually_atTop.1 hrefinement_lt) with ⟨k, hk⟩
    filter_upwards [hupper k x ε hε] with n hn
    have hk' := hk k le_rfl
    dsimp [ε] at hn hk' ⊢
    linarith

end InfillGLSLean.ManuscriptSpecification.L040

end
