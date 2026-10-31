module

public import InfillGLSLean
public import «L-040-mean-information-limit».InformationLimit
public import «L-037-mean-common-refinement».GaussMarkov
public import «L-036-mean-hilbert-riesz».MeanHilbertRiesz

/-!
# True-GLS weak-convergence support for Appendix `lem:mean`

This module contains only exact finite identities and conditional support
lemmas for the normalized true-GLS score passage of the paper's Appendix
`lem:mean`.  Its pending source-level inputs are kept as explicit premises;
it does not add them to a manuscript assumption.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L044

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology

universe u

variable {p : Type u} [Fintype p] [DecidableEq p]

open InfillGLSLean.ManuscriptSpecification.L037
open InfillGLSLean.MeanHilbertRiesz

/-- The row of the exact true-GLS coefficient map which forms one specified
coefficient from the regional outcomes.  For `j = 0` this is the paper's
proof-only true treatment outcome-weight vector `ω_n^*`. -/
@[expose] noncomputable def trueGLSOutcomeWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ) (j : p) : ι → ℝ :=
  fun i => trueGLSCoefficientMap covariance design j i

/-- The covariance quadratic form of a true-GLS outcome-weight row is exactly
the matching diagonal entry of its coefficient-covariance matrix.  This is a
finite identity behind `Var(Z_n) = 1`; no asymptotic condition is used. -/
theorem trueGLSOutcomeWeight_quadraticForm_eq_coefficientCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (hcovariance : covariance.PosDef)
    (hgram : (trueGLSGram covariance design).PosDef) (j : p) :
    quadraticForm covariance (trueGLSOutcomeWeight covariance design j) =
      trueGLSCoefficientCovariance covariance design j j := by
  have hmatrix := linearCoefficientCovariance_trueGLS covariance design
    hcovariance hgram
  have hentry := congrFun (congrFun hmatrix j) j
  have hsymm : ∀ a b, covariance a b = covariance b a := by
    intro a b
    exact (hcovariance.isHermitian.isSymm.apply a b).symm
  rw [quadraticForm_eq_dotProduct_mulVec]
  rw [← hentry]
  simp only [trueGLSOutcomeWeight, linearCoefficientCovariance,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hsymm i k]
  ring

/-- The covariance bilinear form of a true-GLS outcome-weight row against any
finite observation weight is exactly the corresponding coefficient-covariance
row applied to `Dᵀ t`.  This is the finite identity displayed in the paper as
`e₁' B_n D_n' t`. -/
theorem trueGLSOutcomeWeight_covariance_bilinear_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (covariance : Matrix ι ι ℝ) (design : Matrix ι p ℝ)
    (hcovariance : covariance.PosDef) (j : p) (testWeight : ι → ℝ) :
    trueGLSOutcomeWeight covariance design j ⬝ᵥ (covariance *ᵥ testWeight) =
      (trueGLSCoefficientCovariance covariance design *ᵥ
        (Matrix.transpose design *ᵥ testWeight)) j := by
  change (trueGLSCoefficientMap covariance design *ᵥ
      (covariance *ᵥ testWeight)) j = _
  rw [Matrix.mulVec_mulVec,
    trueGLSCoefficientMap_mul_covariance covariance design hcovariance,
    ← Matrix.mulVec_mulVec]

/-- Cross-covariance of two finite weighted scores is the corresponding
covariance-matrix bilinear form.  This is the finite probability identity
needed for the covariance of the true-GLS score with a projected spatial
test; it does not assume a finite Gaussian-vector model. -/
theorem covariance_finiteWeightedScore_eq_bilinear
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    [Fintype ι] (left right : ι → ℝ) (error : ι → Ω → ℝ)
    (herror : ∀ k, MemLp (error k) 2 P) :
    ProbabilityTheory.covariance (finiteWeightedScore left error)
      (finiteWeightedScore right error) P =
        left ⬝ᵥ (finiteErrorCovariance error P *ᵥ right) := by
  unfold finiteWeightedScore
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum]
  · simp_rw [ProbabilityTheory.covariance_const_mul_left,
      ProbabilityTheory.covariance_const_mul_right]
    simp only [finiteErrorCovariance_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro i
    exact (herror i).const_mul (left i)
  · intro j
    exact (herror j).const_mul (right j)

/-- The manuscript's normalized-coordinate conclusion in a form directly
usable for the covariance of the normalized true-GLS score.  The hypotheses
are precisely the already-derived lower PSD order, its matrix limit, the
shrinking treatment variance, and finite positive treatment variances. -/
theorem normalized_coefficient_entry_tendsto_zero
    (lower : Matrix p p ℝ) (upper : ℕ → Matrix p p ℝ)
    (hlower_psd : lower.PosSemidef)
    (horder : ∀ n, (upper n - lower).PosSemidef)
    (hlimit : Tendsto upper atTop (nhds lower))
    (i j : p)
    (hdiag : Tendsto (fun n => upper n i i) atTop (nhds 0))
    (hpositive : ∀ n, 0 < upper n i i) :
    Tendsto (fun n => upper n i j / Real.sqrt (upper n i i)) atTop (nhds 0) := by
  have hentry : Tendsto (fun n => upper n j j) atTop (nhds (lower j j)) := by
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlimit j) j
  have hdifference : Tendsto (fun n => (upper n - lower) j j) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => lower j j) atTop (nhds (lower j j)) :=
      tendsto_const_nhds
    simpa using hentry.sub hconst
  have hsqrt : Tendsto (fun n => Real.sqrt ((upper n - lower) j j)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp hdifference
  have hbound : ∀ n,
      |upper n i j / Real.sqrt (upper n i i)| ≤ Real.sqrt ((upper n - lower) j j) := by
    intro n
    rw [abs_div]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact L040.normalized_coordinate_bound_of_lower_order_and_tendsto_diagonal_zero
      lower upper hlower_psd horder i j hdiag n (hpositive n)
  have habs : Tendsto (fun n => |upper n i j / Real.sqrt (upper n i i)|)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsqrt
      (fun n => abs_nonneg _) hbound
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

omit [DecidableEq p] in
/-- Once every normalized treatment-row coefficient vanishes, its dot product
with any finite deterministic vector converging coordinatewise also vanishes.
This is the finite algebra used for `e₁' B_n D_n' t / sqrt(v_n)` in the
paper; it adds no boundedness or rate premise because the coefficient index
set is finite. -/
theorem normalized_row_dot_tendsto_zero_of_entries
    (upper : ℕ → Matrix p p ℝ) (i : p)
    (hentries : ∀ j : p,
      Tendsto (fun n => upper n i j / Real.sqrt (upper n i i)) atTop (nhds 0))
    (r : ℕ → p → ℝ) (rlimit : p → ℝ)
    (hr : Tendsto r atTop (nhds rlimit)) :
    Tendsto (fun n => (upper n i ⬝ᵥ r n) / Real.sqrt (upper n i i))
      atTop (nhds 0) := by
  have hsum : Tendsto
      (fun n => ∑ j, (upper n i j / Real.sqrt (upper n i i)) * r n j)
      atTop (nhds (∑ j : p, (0 : ℝ))) := by
    apply tendsto_finsetSum Finset.univ
    intro j hj
    have hrj : Tendsto (fun n => r n j) atTop (nhds (rlimit j)) :=
      tendsto_pi_nhds.mp hr j
    simpa using (hentries j).mul hrj
  have hrewrite :
      (fun n => (upper n i ⬝ᵥ r n) / Real.sqrt (upper n i i)) =
        fun n => ∑ j, (upper n i j / Real.sqrt (upper n i i)) * r n j := by
    funext n
    simp only [dotProduct, div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hrewrite]
  simpa using hsum

/-- The exact finite coefficient-matrix conclusion in the paper's
weak-convergence paragraph.  It packages the PSD lower order, the
common-refinement matrix limit, `v_n → 0`, and convergence of the deterministic
test/design vector into the vanishing normalized covariance. -/
theorem normalized_row_dot_tendsto_zero_of_lower_order
    (lower : Matrix p p ℝ) (upper : ℕ → Matrix p p ℝ)
    (hlower_psd : lower.PosSemidef)
    (horder : ∀ n, (upper n - lower).PosSemidef)
    (hlimit : Tendsto upper atTop (nhds lower))
    (i : p)
    (hdiag : Tendsto (fun n => upper n i i) atTop (nhds 0))
    (hpositive : ∀ n, 0 < upper n i i)
    (r : ℕ → p → ℝ) (rlimit : p → ℝ)
    (hr : Tendsto r atTop (nhds rlimit)) :
    Tendsto (fun n => (upper n i ⬝ᵥ r n) / Real.sqrt (upper n i i))
      atTop (nhds 0) := by
  apply normalized_row_dot_tendsto_zero_of_entries upper i (r := r)
    (rlimit := rlimit) ?_ hr
  intro j
  exact normalized_coefficient_entry_tendsto_zero lower upper hlower_psd horder
    hlimit i j hdiag hpositive

/-! ## Source true-GLS score in the covariance Hilbert space -/

section SourceScore

variable {D : CompactEuclideanDomain}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The source finite regional-test map is additive in its weight vector.
This is a literal finite-sum identity, used only to polarize the already
proved diagonal covariance identity. -/
theorem weightedRegionalCellTestLp_add
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (w t : Fin (E.maps.N n) → ℝ) :
    weightedRegionalCellTestLp E n (w + t) =
      weightedRegionalCellTestLp E n w + weightedRegionalCellTestLp E n t := by
  apply Lp.ext
  simp only [weightedRegionalCellTestLp]
  filter_upwards [
    MemLp.coeFn_toLp (weightedRegionalCellTest E n (w + t)).2,
    MemLp.coeFn_toLp (weightedRegionalCellTest E n w).2,
    MemLp.coeFn_toLp (weightedRegionalCellTest E n t).2,
    Lp.coeFn_add
      ((weightedRegionalCellTest E n w).2.toLp (weightedRegionalCellTest E n w).1)
      ((weightedRegionalCellTest E n t).2.toLp (weightedRegionalCellTest E n t).1)
  ] with s hwt hw ht hadd
  calc
    (weightedRegionalCellTestLp E n (w + t) : Point D → ℝ) s =
        (weightedRegionalCellTest E n (w + t)).1 s := by
          simpa only [weightedRegionalCellTestLp] using hwt
    _ = (weightedRegionalCellTest E n w).1 s +
        (weightedRegionalCellTest E n t).1 s := by
          simp only [weightedRegionalCellTest, Pi.add_apply]
          calc
            ∑ i, (w i + t i) * (regionalCellAverageTest E n i).1 s =
                ∑ i, (w i * (regionalCellAverageTest E n i).1 s +
                  t i * (regionalCellAverageTest E n i).1 s) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
            _ = _ := Finset.sum_add_distrib
    _ = (weightedRegionalCellTestLp E n w : Point D → ℝ) s +
        (weightedRegionalCellTestLp E n t : Point D → ℝ) s := by
          simpa only [weightedRegionalCellTestLp] using congrArg₂ (· + ·) hw.symm ht.symm
    _ = ((weightedRegionalCellTestLp E n w +
        weightedRegionalCellTestLp E n t : Lp ℝ 2 μ) : Point D → ℝ) s := by
          exact hadd.symm

/-- The public diagonal finite-energy identity, stated directly for the
source `Lp` regional test representation. -/
theorem centeredTestIntegralLp_weightedRegionalCellTestLp_norm_sq_eq_trueQuadratic
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (weight : Fin (E.maps.N n) → ℝ) :
    ‖centeredTestIntegralLp E cov (weightedRegionalCellTestLp E n weight)‖ ^ 2 =
      quadraticForm (trueCovariance E n) weight := by
  rw [centeredTestIntegralLp_weightedRegionalCellTestLp]
  exact weightedRegionalCellTest_centeredIntegral_norm_sq_eq_trueQuadratic
    E cov n weight

/-- Expansion of a real symmetric quadratic form along a sum.  It supplies
the finite polarization algebra for the projected-test covariance. -/
theorem quadraticForm_add_of_isSymm
    {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) (hsymm : matrix.IsSymm)
    (w t : ι → ℝ) :
    quadraticForm matrix (w + t) =
      quadraticForm matrix w + 2 * (w ⬝ᵥ (matrix *ᵥ t)) +
        quadraticForm matrix t := by
  have hcomm : t ⬝ᵥ (matrix *ᵥ w) = w ⬝ᵥ (matrix *ᵥ t) := by
    calc
      t ⬝ᵥ (matrix *ᵥ w) = t ⬝ᵥ (matrix.transpose *ᵥ w) := by rw [hsymm]
      _ = w ⬝ᵥ (matrix *ᵥ t) := Matrix.dotProduct_transpose_mulVec matrix t w
  simp only [quadraticForm_eq_dotProduct_mulVec, Matrix.mulVec_add,
    add_dotProduct, dotProduct_add]
  rw [hcomm]
  ring

/-- Polarization specialized to a real Hilbert space, in the exact form used
to convert diagonal score energies into a cross covariance. -/
theorem inner_eq_of_norm_add
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (x y : G) (a b target : ℝ)
    (hx : ‖x‖ ^ 2 = a) (hy : ‖y‖ ^ 2 = b)
    (hxy : ‖x + y‖ ^ 2 = a + 2 * target + b) :
    inner ℝ x y = target := by
  have hnorm : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2 := by
    simpa using (norm_add_sq (𝕜 := ℝ) x y)
  rw [hx, hy, hxy] at hnorm
  linarith

/-- Exact source-level cross covariance of two finite regional tests.  This
is derived by polarization from the public diagonal energy identity, rather
than by adding a finite-vector distributional assumption. -/
theorem inner_centeredTestIntegralLp_weightedRegionalCellTestLp_eq_trueBilinear
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (w t : Fin (E.maps.N n) → ℝ)
    (hcovariance : (trueCovariance E n).PosDef) :
    inner ℝ (centeredTestIntegralLp E cov (weightedRegionalCellTestLp E n w))
      (centeredTestIntegralLp E cov (weightedRegionalCellTestLp E n t)) =
        w ⬝ᵥ (trueCovariance E n *ᵥ t) := by
  have hsum : centeredTestIntegralLp E cov
      (weightedRegionalCellTestLp E n (w + t)) =
        centeredTestIntegralLp E cov (weightedRegionalCellTestLp E n w) +
          centeredTestIntegralLp E cov (weightedRegionalCellTestLp E n t) := by
    rw [weightedRegionalCellTestLp_add, centeredTestIntegralLp_add]
  have hw := centeredTestIntegralLp_weightedRegionalCellTestLp_norm_sq_eq_trueQuadratic
    E cov n w
  have ht := centeredTestIntegralLp_weightedRegionalCellTestLp_norm_sq_eq_trueQuadratic
    E cov n t
  have hsumNorm :=
    centeredTestIntegralLp_weightedRegionalCellTestLp_norm_sq_eq_trueQuadratic
      E cov n (w + t)
  rw [hsum] at hsumNorm
  have hquad := quadraticForm_add_of_isSymm (trueCovariance E n)
    hcovariance.isHermitian.isSymm w t
  exact inner_eq_of_norm_add _ _
    (quadraticForm (trueCovariance E n) w)
    (quadraticForm (trueCovariance E n) t)
    (w ⬝ᵥ (trueCovariance E n *ᵥ t)) hw ht (hsumNorm.trans hquad)

/-- The centered true-GLS score for one coefficient, represented in exactly
the covariance Hilbert space defined from the fixed spatial error field.
The finite weight is the relevant row of the true-GLS coefficient map. -/
@[expose] noncomputable def trueGLSRegionalScore
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (j : Fin (E.q + 1)) : covarianceHilbertSpace E cov :=
  ⟨centeredTestIntegralLp E cov
      (weightedRegionalCellTestLp E n
        (trueGLSOutcomeWeight (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) j)),
    centeredTestIntegralLp_mem_covarianceHilbertSpace E cov
      (weightedRegionalCellTestLp E n
        (trueGLSOutcomeWeight (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) j))⟩

/-- A finite regional spatial test, embedded into the same covariance Hilbert
space as the true-GLS score. -/
noncomputable def regionalCellTestScore
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (weight : Fin (E.maps.N n) → ℝ) : covarianceHilbertSpace E cov :=
  ⟨centeredTestIntegralLp E cov (weightedRegionalCellTestLp E n weight),
    centeredTestIntegralLp_mem_covarianceHilbertSpace E cov
      (weightedRegionalCellTestLp E n weight)⟩

/-- The covariance-Hilbert representative of an arbitrary fixed spatial L2
test.  Its finite regional projections converge to it by the existing L-036
spatial-averaging result. -/
noncomputable def spatialTestScore
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : Lp ℝ 2 μ) : covarianceHilbertSpace E cov :=
  ⟨centeredTestIntegralLp E cov h,
    centeredTestIntegralLp_mem_covarianceHilbertSpace E cov h⟩

/-- `spatialTestScore` is exactly L-036's corestricted centered-test map.
This bridge is definitional at the source level and permits its established
dense-range theorem to be used without treating density as an extra
assumption. -/
theorem spatialTestScore_eq_centeredTestIntegralToCovarianceHilbertSpace
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : Lp ℝ 2 μ) :
    spatialTestScore E cov h =
      centeredTestIntegralToCovarianceHilbertSpace E cov h := by
  apply Subtype.ext
  exact (centeredTestIntegralToCovarianceHilbertSpace_apply_coe E cov h).symm

/-- Exact regional-projection tests converge in the covariance Hilbert space
to the fixed spatial-test score.  This is L-036's fixed-field averaging limit
with the codomain restricted to the already-defined covariance space. -/
theorem regionalCellTestScore_regionalProjection_sub_tendsto_zero
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (h : Lp ℝ 2 μ) :
    Tendsto (fun n => regionalCellTestScore E cov n
      (regionalProjectionWeights E (fun s => h s) n) - spatialTestScore E cov h)
      atTop (nhds 0) := by
  let f : Point D → ℝ := fun s => h s
  have hf : MemLp f 2 μ := by
    simpa [f] using Lp.memLp h
  have htoLp : hf.toLp f = h := by
    simp [f]
  have hbase := centeredTestIntegralLp_weightedRegionalCellTestLp_sub_tendsto_zero
    E cov f hf
  rw [htoLp] at hbase
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [regionalCellTestScore, spatialTestScore] using hbase.norm

/-- The exact squared norm of the source true-GLS score is the corresponding
diagonal true coefficient covariance.  This is the paper's `Var(ω_n^{*'}u_n)
= v_n` before normalization. -/
theorem trueGLSRegionalScore_norm_sq
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (j : Fin (E.q + 1))
    (hcovariance : (trueCovariance E n).PosDef)
    (hgram : (trueGLSGram (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n)).PosDef) :
    ‖trueGLSRegionalScore E cov n j‖ ^ 2 =
      trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) j j := by
  change ‖centeredTestIntegralLp E cov
      (weightedRegionalCellTestLp E n
        (trueGLSOutcomeWeight (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) j))‖ ^ 2 = _
  rw [centeredTestIntegralLp_weightedRegionalCellTestLp]
  rw [weightedRegionalCellTest_centeredIntegral_norm_sq_eq_trueQuadratic]
  exact trueGLSOutcomeWeight_quadraticForm_eq_coefficientCovariance
    (trueCovariance E n) (regionalDesign μ E.maps E.treatment E.controls n)
    hcovariance hgram j

/-- The exact covariance-Hilbert inner product of a true-GLS regional score
with any finite projected regional test.  The right side is precisely the
paper's finite `e_j' B_n D_n' t` expression before normalization. -/
theorem trueGLSRegionalScore_inner_weightedRegionalCellTestLp_eq
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (j : Fin (E.q + 1)) (testWeight : Fin (E.maps.N n) → ℝ)
    (hcovariance : (trueCovariance E n).PosDef) :
    inner ℝ (trueGLSRegionalScore E cov n j)
      (regionalCellTestScore E cov n testWeight) =
      (trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
          (Matrix.transpose (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
            testWeight)) j := by
  unfold trueGLSRegionalScore regionalCellTestScore
  change inner ℝ (centeredTestIntegralLp E cov
      (weightedRegionalCellTestLp E n
        (trueGLSOutcomeWeight (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) j)))
      (centeredTestIntegralLp E cov (weightedRegionalCellTestLp E n testWeight)) = _
  rw [inner_centeredTestIntegralLp_weightedRegionalCellTestLp_eq_trueBilinear
    E cov n
      (trueGLSOutcomeWeight (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) j)
      testWeight hcovariance]
  exact trueGLSOutcomeWeight_covariance_bilinear_eq
    (trueCovariance E n) (regionalDesign μ E.maps E.treatment E.controls n)
    hcovariance j testWeight

/-- The normalized true-GLS centered score `Z_n` used in the paper's weak
convergence argument.  Positivity of its denominator is proved separately
from the exact finite true-GLS hypotheses. -/
@[expose] noncomputable def normalizedTrueGLSRegionalScore
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (j : Fin (E.q + 1)) : covarianceHilbertSpace E cov :=
  (Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
    (regionalDesign μ E.maps E.treatment E.controls n) j j))⁻¹ •
    trueGLSRegionalScore E cov n j

/-- The normalized form of the exact projected-test covariance.  This is the
displayed covariance identity in the paper's weak-convergence paragraph;
strict positivity is not needed for the algebraic equality itself. -/
theorem normalizedTrueGLSRegionalScore_inner_weightedRegionalCellTestLp_eq
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (j : Fin (E.q + 1)) (testWeight : Fin (E.maps.N n) → ℝ)
    (hcovariance : (trueCovariance E n).PosDef) :
    inner ℝ (normalizedTrueGLSRegionalScore E cov n j)
      (regionalCellTestScore E cov n testWeight) =
      (trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
          (Matrix.transpose (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
            testWeight)) j /
        Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) j j) := by
  calc
    inner ℝ (normalizedTrueGLSRegionalScore E cov n j)
        (regionalCellTestScore E cov n testWeight) =
        (Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) j j))⁻¹ *
          inner ℝ (trueGLSRegionalScore E cov n j)
            (regionalCellTestScore E cov n testWeight) := by
          rw [normalizedTrueGLSRegionalScore]
          simpa using (inner_smul_left (trueGLSRegionalScore E cov n j)
            (regionalCellTestScore E cov n testWeight)
            (Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
              (regionalDesign μ E.maps E.treatment E.controls n) j j))⁻¹)
    _ = _ := by
      rw [trueGLSRegionalScore_inner_weightedRegionalCellTestLp_eq E cov n j testWeight
        hcovariance]
      simp [div_eq_mul_inv, mul_comm]

/-- Under the existing strict finite covariance and Gram conclusions, the
normalized true-GLS score has exact covariance-Hilbert norm one. -/
theorem normalizedTrueGLSRegionalScore_norm_sq_eq_one
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (n : ℕ) (j : Fin (E.q + 1))
    (hcovariance : (trueCovariance E n).PosDef)
    (hgram : (trueGLSGram (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n)).PosDef)
    (hpositive : 0 < trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n) j j) :
    ‖normalizedTrueGLSRegionalScore E cov n j‖ ^ 2 = 1 := by
  have hscore := trueGLSRegionalScore_norm_sq E cov n j hcovariance hgram
  have hsqrt : 0 < Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n) j j) :=
    Real.sqrt_pos.2 hpositive
  have hsqrt_sq : (Real.sqrt (trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n) j j)) ^ 2 =
      trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) j j :=
    Real.sq_sqrt hpositive.le
  rw [normalizedTrueGLSRegionalScore, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hsqrt), mul_pow, hscore]
  field_simp [hsqrt.ne']
  exact hsqrt_sq.symm

/-- The paper's finite projected-test weak-convergence calculation.  The
matrix limit/order, shrinking variance, and projected-design-vector
convergence are explicit inputs here: L-043 supplies the source derivations
of the first two matrix facts, while no such statement is added to a paper
assumption in this module. -/
theorem normalizedTrueGLSRegionalScore_inner_tendsto_zero_of_matrix_limit
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (j : Fin (E.q + 1)) (lower : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ)
    (hlower_psd : lower.PosSemidef)
    (horder : ∀ n,
      (trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) - lower).PosSemidef)
    (hlimit : Tendsto (fun n => trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n)) atTop (nhds lower))
    (hdiag : Tendsto (fun n => trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n) j j) atTop (nhds 0))
    (hpositive : ∀ n, 0 < trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n) j j)
    (testWeight : (n : ℕ) → Fin (E.maps.N n) → ℝ)
    (r : ℕ → Fin (E.q + 1) → ℝ) (rlimit : Fin (E.q + 1) → ℝ)
    (hr : Tendsto r atTop (nhds rlimit))
    (hdesign : ∀ n, Matrix.transpose (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
      testWeight n = r n)
    (hcovariance : ∀ n, (trueCovariance E n).PosDef) :
    Tendsto (fun n => inner ℝ (normalizedTrueGLSRegionalScore E cov n j)
      (regionalCellTestScore E cov n (testWeight n))) atTop (nhds 0) := by
  have halgebra := normalized_row_dot_tendsto_zero_of_lower_order lower
    (fun n => trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n))
    hlower_psd horder hlimit j hdiag hpositive r rlimit hr
  apply halgebra.congr'
  filter_upwards [] with n
  rw [normalizedTrueGLSRegionalScore_inner_weightedRegionalCellTestLp_eq
    E cov n j (testWeight n) (hcovariance n), hdesign n]
  rfl

end SourceScore

/-! ## Fixed-test replacement and dense weak convergence -/

/-- If uniformly bounded Hilbert-space scores are asymptotically orthogonal
to approximating tests, and those tests converge to one fixed test, then they
are asymptotically orthogonal to that fixed test.  This is the replacement of
`Π_n h` by `h` in the paper; it has no rate premise. -/
theorem inner_tendsto_zero_of_tendsto_projected_test
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (z test : ℕ → G) (v : G) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ‖z n‖ ≤ C)
    (hprojected : Tendsto (fun n => inner ℝ (z n) (test n)) atTop (nhds 0))
    (htest : Tendsto (fun n => test n - v) atTop (nhds 0)) :
    Tendsto (fun n => inner ℝ (z n) v) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdenom : 0 < 2 * (C + 1) := by linarith
  have hδ : 0 < ε / (2 * (C + 1)) := div_pos hε hdenom
  have hdiff : Tendsto (fun n => v - test n) atTop (nhds 0) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using htest.neg
  obtain ⟨Nprojected, hNprojected⟩ :=
    (Metric.tendsto_atTop.mp hprojected) (ε / 2) (by linarith)
  obtain ⟨Ntest, hNtest⟩ :=
    (Metric.tendsto_atTop.mp hdiff) (ε / (2 * (C + 1))) hδ
  refine ⟨max Nprojected Ntest, fun n hn => ?_⟩
  have hprojected_n : ‖inner ℝ (z n) (test n)‖ < ε / 2 := by
    simpa [dist_eq_norm] using hNprojected n (le_max_left _ _ |>.trans hn)
  have htest_n : ‖v - test n‖ < ε / (2 * (C + 1)) := by
    simpa [dist_eq_norm] using hNtest n (le_max_right _ _ |>.trans hn)
  have herror : ‖inner ℝ (z n) (v - test n)‖ < ε / 2 := by
    by_cases hCzero : C = 0
    · have hznorm : ‖z n‖ = 0 := le_antisymm (by simpa [hCzero] using hbound n)
        (norm_nonneg _)
      have hz : z n = 0 := norm_eq_zero.mp hznorm
      simp [hz, hε]
    · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
      calc
        ‖inner ℝ (z n) (v - test n)‖ ≤ ‖z n‖ * ‖v - test n‖ :=
          norm_inner_le_norm _ _
        _ ≤ C * ‖v - test n‖ :=
          mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
        _ < C * (ε / (2 * (C + 1))) :=
          mul_lt_mul_of_pos_left htest_n hCpos
        _ ≤ ε / 2 := by
          calc
            C * (ε / (2 * (C + 1))) ≤
                (C + 1) * (ε / (2 * (C + 1))) := by
                  exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
            _ = ε / 2 := by field_simp
  have hsum : ‖inner ℝ (z n) v‖ < ε := by
    calc
      ‖inner ℝ (z n) v‖ =
          ‖inner ℝ (z n) (test n) + inner ℝ (z n) (v - test n)‖ := by
            rw [← inner_add_right]
            congr 1
            abel_nf
      _ ≤ ‖inner ℝ (z n) (test n)‖ + ‖inner ℝ (z n) (v - test n)‖ :=
        norm_add_le _ _
      _ < ε := by linarith
  simpa [dist_eq_norm] using hsum

/-- Dense-range specialization of L-036's dense-submodule weak extension.
The covariance Hilbert space's centered spatial-integral map has this form. -/
theorem inner_tendsto_zero_of_dense_range
    {X G : Type*} [AddCommMonoid X] [Module ℝ X]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : X →ₗ[ℝ] G) (hA : DenseRange A)
    (z : ℕ → G) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖z n‖ ≤ C)
    (htest : ∀ x : X, Tendsto (fun n => inner ℝ (z n) (A x)) atTop (nhds 0))
    (v : G) :
    Tendsto (fun n => inner ℝ (z n) v) atTop (nhds 0) := by
  apply inner_tendsto_zero_of_dense_submodule z (LinearMap.range A) ?_ C hC hbound ?_ v
  · have hrange : (LinearMap.range A : Set G) = Set.range A := by
      ext y
      constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, rfl⟩
    rw [hrange]
    exact hA
  · intro w
    obtain ⟨x, hx⟩ := w.property
    simpa [hx] using htest x

/-! ## Source weak-convergence endpoints -/

section SourceWeakEndpoint

variable {D : CompactEuclideanDomain}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure (Point D)} [IsProbabilityMeasure μ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Once the normalized scores have vanishing inner products with every
finite regional projection, L-036's spatial approximation and dense-span
argument give weak convergence against every fixed element of the covariance
Hilbert space.  This is the final Hilbert-space step in the true-GLS paragraph
of Appendix `lem:mean`. -/
theorem normalizedTrueGLSRegionalScore_weakly_tendsto_zero_of_projected_test_limits
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (j : Fin (E.q + 1))
    (hbound : ∀ n, ‖normalizedTrueGLSRegionalScore E cov n j‖ ≤ 1)
    (hprojected : ∀ h : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (normalizedTrueGLSRegionalScore E cov n j)
        (regionalCellTestScore E cov n
          (regionalProjectionWeights E (fun s => h s) n))) atTop (nhds 0))
    (hdense : Dense (Submodule.span ℝ (Set.range (spatialTestScore E cov)) :
      Set (covarianceHilbertSpace E cov)))
    (v : covarianceHilbertSpace E cov) :
    Tendsto (fun n => inner ℝ (normalizedTrueGLSRegionalScore E cov n j) v)
      atTop (nhds 0) := by
  apply inner_tendsto_zero_of_dense_span
    (fun n => normalizedTrueGLSRegionalScore E cov n j)
    (Set.range (spatialTestScore E cov)) hdense 1 zero_le_one hbound ?_ v
  intro w hw
  obtain ⟨h, rfl⟩ := hw
  exact inner_tendsto_zero_of_tendsto_projected_test
    (fun n => normalizedTrueGLSRegionalScore E cov n j)
    (fun n => regionalCellTestScore E cov n
      (regionalProjectionWeights E (fun s => h s) n))
    (spatialTestScore E cov h) 1 zero_le_one hbound (hprojected h)
    (regionalCellTestScore_regionalProjection_sub_tendsto_zero E cov h)

/-- Source-specialized weak convergence on a reindexed finite-GLS tail.
The first six matrix hypotheses are the exact `B_n ⪰ B`, `B_n → B`, and
`v_n → 0` inputs from the paper.  The only spatial-design limit retained as
an explicit premise is the stated convergence of `D_nᵀ t_R`; it is not added
to `FixedConditionalExperiment` or any manuscript assumption. -/
theorem normalizedTrueGLSRegionalScore_weakly_tendsto_zero_of_matrix_limit
    (E : FixedConditionalExperiment μ P) (cov : CovarianceAssumption E)
    (j : Fin (E.q + 1)) (lower : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ)
    (hlower_psd : lower.PosSemidef)
    (horder : ∀ n,
      (trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) - lower).PosSemidef)
    (hlimit : Tendsto (fun n => trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n)) atTop (nhds lower))
    (hdiag : Tendsto (fun n => trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n) j j) atTop (nhds 0))
    (hpositive : ∀ n, 0 < trueGLSCoefficientCovariance (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n) j j)
    (hcovariance : ∀ n, (trueCovariance E n).PosDef)
    (hgram : ∀ n, (trueGLSGram (trueCovariance E n)
      (regionalDesign μ E.maps E.treatment E.controls n)).PosDef)
    (hdesign_limit : ∀ h : Lp ℝ 2 μ, ∃ rlimit : Fin (E.q + 1) → ℝ,
      Tendsto (fun n => Matrix.transpose
        (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
          regionalProjectionWeights E (fun s => h s) n) atTop (nhds rlimit))
    (hdense : Dense (Submodule.span ℝ (Set.range (spatialTestScore E cov)) :
      Set (covarianceHilbertSpace E cov)))
    (v : covarianceHilbertSpace E cov) :
    Tendsto (fun n => inner ℝ (normalizedTrueGLSRegionalScore E cov n j) v)
      atTop (nhds 0) := by
  have hbound : ∀ n, ‖normalizedTrueGLSRegionalScore E cov n j‖ ≤ 1 := by
    intro n
    have hnorm := normalizedTrueGLSRegionalScore_norm_sq_eq_one E cov n j
      (hcovariance n) (hgram n) (hpositive n)
    nlinarith [norm_nonneg (normalizedTrueGLSRegionalScore E cov n j)]
  apply normalizedTrueGLSRegionalScore_weakly_tendsto_zero_of_projected_test_limits
    E cov j hbound ?_ hdense v
  intro h
  obtain ⟨rlimit, hrlimit⟩ := hdesign_limit h
  exact normalizedTrueGLSRegionalScore_inner_tendsto_zero_of_matrix_limit
    E cov j lower hlower_psd horder hlimit hdiag hpositive
    (fun n => regionalProjectionWeights E (fun s => h s) n)
    (fun n => Matrix.transpose (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
      regionalProjectionWeights E (fun s => h s) n)
    rlimit hrlimit (fun _ => rfl) hcovariance

end SourceWeakEndpoint

end InfillGLSLean.ManuscriptSpecification.L044

end
