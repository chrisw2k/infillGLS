module

public import «L-047-mean-information-assembly».InformationAssembly
public import InfillGLSLean.GLSBiasBound
public import InfillGLSLean.CovarianceSandwichLimit

/-!
# Exact treatment-variance sandwich for Appendix `lem:mean`

This module isolates the displayed finite comparison in
`the source manuscript:533--552`.  It retains the paper's `v_n` as the
treatment diagonal of the true-GLS coefficient covariance, rather than
replacing it by the variance of the working GLS score.
-/

public section

namespace InfillGLSLean.ManuscriptSpecification.L048

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal

open InfillGLSLean.ManuscriptSpecification.L027
open InfillGLSLean.ManuscriptSpecification.L037
open InfillGLSLean.ManuscriptSpecification.L041
open InfillGLSLean.ManuscriptSpecification.L042
open InfillGLSLean.ManuscriptSpecification.L047

universe u v

/-- The proof-only true-GLS treatment outcome-weight row.  It is the first
row of the coefficient map defining the paper's `B_n`; it is introduced here
only to connect that unchanged definition of `v_n` to finite duality. -/
@[expose] noncomputable def observedTrueGLSOutcomeWeight
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} {P : Measure Ω}
    (E : FixedConditionalExperiment μ P) (n : ℕ) :
    Fin (E.maps.N n) → ℝ :=
  fun i => trueGLSCoefficientMap (trueCovariance E n)
    (regionalDesign μ E.maps E.treatment E.controls n) 0 i

/-- The true-GLS treatment row is a complete-design feasible row.  This is
the first-row specialization of the exact GLS normal identity, with no
additional rank or covariance hypothesis beyond those used to establish its
positive-definite GLS Gram matrix. -/
theorem transpose_regionalDesign_mulVec_observedTrueGLSOutcomeWeight_eq_first
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    Matrix.transpose (regionalDesign μ E.maps E.treatment E.controls n) *ᵥ
        observedTrueGLSOutcomeWeight E n =
      Pi.single (0 : Fin (E.q + 1)) 1 := by
  classical
  let design := regionalDesign μ E.maps E.treatment E.controls n
  have htrueCovariance : (trueCovariance E n).PosDef :=
    trueCovariance_posDef E covariance n
  have hgram : (trueGLSGram (trueCovariance E n) design).PosDef := by
    exact trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
      htrueCovariance hfull
  have hmap := trueGLSCoefficientMap_mul_design (trueCovariance E n) design hgram
  ext j
  have hentry := congrFun (congrFun hmap 0) j
  have hsum : Finset.univ.sum (fun i =>
      trueGLSCoefficientMap (trueCovariance E n) design 0 i * design i j) =
      if (0 : Fin (E.q + 1)) = j then (1 : ℝ) else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using hentry
  change Finset.univ.sum (fun i => design i j *
    trueGLSCoefficientMap (trueCovariance E n) design 0 i) =
      ((Pi.single (0 : Fin (E.q + 1)) (1 : ℝ)) : Fin (E.q + 1) → ℝ) j
  calc
    Finset.univ.sum (fun i => design i j *
        trueGLSCoefficientMap (trueCovariance E n) design 0 i) =
        Finset.univ.sum (fun i =>
          trueGLSCoefficientMap (trueCovariance E n) design 0 i * design i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (1 : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ) 0 j := by
      simpa [Matrix.one_apply] using hsum
    _ = ((Pi.single (0 : Fin (E.q + 1)) (1 : ℝ)) : Fin (E.q + 1) → ℝ) j := by
      by_cases hj : j = 0
      · subst j
        simp
      · have hzero : (0 : Fin (E.q + 1)) ≠ j := Ne.symm hj
        simp [hj, hzero]

/-- The covariance energy of the true-GLS treatment row is exactly the first
diagonal coefficient covariance.  This is the finite identity connecting the
proof-only feasible row to the paper's retained definition of `v_n`. -/
theorem observedTrueGLSOutcomeWeight_quadraticForm_eq_coefficientDiagonal
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    quadraticForm (trueCovariance E n) (observedTrueGLSOutcomeWeight E n) =
      trueGLSCoefficientCovariance (trueCovariance E n)
        (regionalDesign μ E.maps E.treatment E.controls n) 0 0 := by
  let design := regionalDesign μ E.maps E.treatment E.controls n
  have htrueCovariance : (trueCovariance E n).PosDef :=
    trueCovariance_posDef E covariance n
  have hgram : (trueGLSGram (trueCovariance E n) design).PosDef := by
    exact trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
      htrueCovariance hfull
  have hmatrix := linearCoefficientCovariance_trueGLS (trueCovariance E n)
    design htrueCovariance hgram
  have hentry := congrFun (congrFun hmatrix 0) 0
  have hsymm : ∀ a b, trueCovariance E n a b = trueCovariance E n b a := by
    intro a b
    exact (htrueCovariance.isHermitian.isSymm.apply a b).symm
  rw [quadraticForm_eq_dotProduct_mulVec]
  rw [← hentry]
  simp only [observedTrueGLSOutcomeWeight, design, linearCoefficientCovariance,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hsymm i k]
  ring

/-- The preceding finite energy identity stated directly for L-047's retained
source definition of `v_n`.  The two L-047 expansion lemmas are visibility
only; this theorem does not replace or redefine that variance. -/
theorem observedTrueGLSOutcomeWeight_quadraticForm_eq_treatmentVariance
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    quadraticForm (trueCovariance E n) (observedTrueGLSOutcomeWeight E n) =
      observedTrueGLSTreatmentVariance E n := by
  calc
    quadraticForm (trueCovariance E n) (observedTrueGLSOutcomeWeight E n) =
        trueGLSCoefficientCovariance (trueCovariance E n)
          (regionalDesign μ E.maps E.treatment E.controls n) 0 0 :=
      observedTrueGLSOutcomeWeight_quadraticForm_eq_coefficientDiagonal
        E covariance n hfull
    _ = observedTrueGLSTreatmentVariance E n := by
      symm
      rw [observedTrueGLSTreatmentVariance_eq,
        observedTrueGLSCoefficientCovariance_eq]

/-- The exact finite dual inequality behind the lower displayed bound for
`v_n`.  If `Q` is the attained source treatment-information minimum and `w`
is any complete-design feasible treatment row, then the `K`-energy of `w` is
at least `1 / Q`.

The proof uses the attaining residual from the literal `eq:information`
definition and matrix Cauchy--Schwarz after applying the covariance matrix to
`w`.  `hQpos` is a derived finite positivity fact at a full-rank resolution,
not an added experiment assumption. -/
theorem inv_information_le_quadraticForm_of_treatment_feasible
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Matrix ι ι ℝ) (hK : K.PosDef)
    (x : ι → ℝ) (W : Matrix ι κ ℝ) (Q : ℝ)
    (hQ : IsTreatmentInformation K x W Q) (hQpos : 0 < Q)
    (w : ι → ℝ)
    (hw_treatment : w ⬝ᵥ x = 1)
    (hw_controls : ∀ c : κ → ℝ, w ⬝ᵥ (W *ᵥ c) = 0) :
    1 / Q ≤ quadraticForm K w := by
  rcases (isTreatmentInformation_iff K x W Q).mp hQ with
    ⟨⟨ell, hattained⟩, _⟩
  let residual : ι → ℝ := x - W *ᵥ ell
  have henergy : quadraticForm K⁻¹ residual = Q := by
    simpa [residual] using hattained.symm
  have hscore : (K *ᵥ w) ⬝ᵥ (K⁻¹ *ᵥ residual) = 1 := by
    rw [workingCovariance_dual_score_eq hK w residual]
    calc
      w ⬝ᵥ residual = w ⬝ᵥ x - w ⬝ᵥ (W *ᵥ ell) := by
        simp only [residual, dotProduct_sub]
      _ = 1 := by rw [hw_treatment, hw_controls ell]; ring
  have hcauchy := precision_score_sq_le_quadraticForms hK.inv (K *ᵥ w) residual
  have hproduct : 1 ≤ quadraticForm K w * Q := by
    calc
      (1 : ℝ) = ((K *ᵥ w) ⬝ᵥ (K⁻¹ *ᵥ residual)) ^ 2 := by rw [hscore]; norm_num
      _ ≤ quadraticForm K⁻¹ (K *ᵥ w) * quadraticForm K⁻¹ residual := hcauchy
      _ = quadraticForm K w * Q := by
        rw [quadraticForm_inverse_working_mulVec_eq hK w, henergy]
  exact (div_le_iff₀ hQpos).2 hproduct

/-- Source full rank makes the literal attained treatment information
strictly positive.  This uses the existing exact FWL identification only to
obtain positivity; the dual inequality above still uses the literal attained
`IsTreatmentInformation` witness carried by the experiment. -/
theorem observed_information_pos_of_full_rank
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    0 < E.information n := by
  let controls := regionalControls μ E.maps E.controls n
  let treatment := regionalValues μ E.maps E.treatment n
  have hfull_source :
      (InfillGLSLean.L023.sourceDesign treatment controls).rank = E.q + 1 := by
    change (InfillGLSLean.L023.sourceDesign
      (regionalValues μ E.maps E.treatment n)
      (regionalControls μ E.maps E.controls n)).rank = E.q + 1 at hfull
    exact hfull
  have hprecision : (E.kernel n)⁻¹ |>.PosDef := (E.kernel_posDef n).inv
  rcases InfillGLSLean.L023.sourceDesign_fwl_nonsingularity_and_relevance_of_full_rank
    treatment controls (E.kernel n)⁻¹ hprecision hfull_source with ⟨_, hresidual⟩
  have hinformation :
      E.information n = InfillGLSLean.controlInformation (E.kernel n)⁻¹
        controls treatment :=
    information_eq_controlInformation_of_full_rank E n hfull
  rw [hinformation]
  exact InfillGLSLean.controlInformation_pos hprecision hresidual

/-- The true-GLS treatment row obeys the literal treatment and control
constraints needed by the finite information duality lemma. -/
theorem observedTrueGLSOutcomeWeight_treatment_control_feasible
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    observedTrueGLSOutcomeWeight E n ⬝ᵥ
        regionalValues μ E.maps E.treatment n = 1 ∧
      ∀ c : Fin E.q → ℝ, observedTrueGLSOutcomeWeight E n ⬝ᵥ
        ((regionalControls μ E.maps E.controls n) *ᵥ c) = 0 := by
  classical
  let design := regionalDesign μ E.maps E.treatment E.controls n
  let controls := regionalControls μ E.maps E.controls n
  let treatment := regionalValues μ E.maps E.treatment n
  have htrueCovariance : (trueCovariance E n).PosDef :=
    trueCovariance_posDef E covariance n
  have hgram : (trueGLSGram (trueCovariance E n) design).PosDef := by
    exact trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
      htrueCovariance hfull
  have hmap := trueGLSCoefficientMap_mul_design (trueCovariance E n) design hgram
  have htreatment : observedTrueGLSOutcomeWeight E n ⬝ᵥ treatment = 1 := by
    have hentry := congrFun (congrFun hmap 0) 0
    change Finset.univ.sum (fun i =>
      trueGLSCoefficientMap (trueCovariance E n) design 0 i * treatment i) = 1
    simpa [design, treatment, Matrix.mul_apply, regionalDesign_apply] using hentry
  have hcontrols_transpose : Matrix.transpose controls *ᵥ
      observedTrueGLSOutcomeWeight E n = 0 := by
    ext k
    have hentry := congrFun (congrFun hmap 0) k.succ
    change Finset.univ.sum (fun i => controls i k *
      trueGLSCoefficientMap (trueCovariance E n) design 0 i) = 0
    calc
      Finset.univ.sum (fun i => controls i k *
          trueGLSCoefficientMap (trueCovariance E n) design 0 i) =
          Finset.univ.sum (fun i =>
            trueGLSCoefficientMap (trueCovariance E n) design 0 i * controls i k) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (1 : Matrix (Fin (E.q + 1)) (Fin (E.q + 1)) ℝ) 0 k.succ := by
        simpa [design, controls, Matrix.mul_apply, regionalDesign_apply] using hentry
      _ = 0 := by
        change (if (0 : Fin (E.q + 1)) = k.succ then (1 : ℝ) else 0) = 0
        have hzero : (0 : Fin (E.q + 1)) ≠ k.succ := by
          intro h
          have hval : 0 = k.val + 1 := by
            simpa using congrArg Fin.val h
          omega
        simp [hzero]
  refine ⟨?_, ?_⟩
  · simpa [treatment] using htreatment
  · intro c
    calc
      observedTrueGLSOutcomeWeight E n ⬝ᵥ (controls *ᵥ c) =
          c ⬝ᵥ (Matrix.transpose controls *ᵥ observedTrueGLSOutcomeWeight E n) := by
            simpa using
              (Matrix.dotProduct_transpose_mulVec (Matrix.transpose controls)
                (observedTrueGLSOutcomeWeight E n) c)
      _ = (Matrix.transpose controls *ᵥ observedTrueGLSOutcomeWeight E n) ⬝ᵥ c :=
        dotProduct_comm _ _
      _ = 0 := by rw [hcontrols_transpose]; simp

/-- The paper's exact finite treatment-variance sandwich at one source
full-rank resolution.  The left bound applies covariance order to the true
GLS feasible row and the working-information dual inequality; the right
bound applies true-GLS minimality to the literal working FWL feasible row.
No asymptotic rate, nesting condition, or additional covariance/rank premise
is used. -/
theorem observedTrueGLSTreatmentVariance_sandwich_of_full_rank
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E)
    (n : ℕ) (hstart : covariance.start ≤ n)
    (hfull : (regionalDesign μ E.maps E.treatment E.controls n).rank = E.q + 1) :
    covariance.sigmaSquared / ((1 + covariance.delta n) * E.information n) ≤
        observedTrueGLSTreatmentVariance E n ∧
      observedTrueGLSTreatmentVariance E n ≤
        covariance.sigmaSquared / ((1 - covariance.delta n) * E.information n) := by
  classical
  rcases covariance.sandwich n hstart with
    ⟨hdelta_nonneg, hdelta_lt_one, hsandwich_lower, hsandwich_upper⟩
  let design := regionalDesign μ E.maps E.treatment E.controls n
  let controls := regionalControls μ E.maps E.controls n
  let treatment := regionalValues μ E.maps E.treatment n
  let trueWeight := observedTrueGLSOutcomeWeight E n
  let workingWeight := observedWorkingGLSOutcomeWeight E n
  have hinformation_pos : 0 < E.information n :=
    observed_information_pos_of_full_rank E n hfull
  have hplus_pos : 0 < 1 + covariance.delta n := by linarith
  have hminus_pos : 0 < 1 - covariance.delta n := by linarith
  have htrueCovariance : (trueCovariance E n).PosDef :=
    trueCovariance_posDef E covariance n
  have htrueGram : (trueGLSGram (trueCovariance E n) design).PosDef := by
    exact trueGLSGram_posDef_of_trueCovariance_posDef_and_full_rank E
      htrueCovariance hfull
  have htrue_feasible :=
    observedTrueGLSOutcomeWeight_treatment_control_feasible E covariance n hfull
  have hworking_dual : 1 / E.information n ≤ quadraticForm (E.kernel n) trueWeight := by
    exact inv_information_le_quadraticForm_of_treatment_feasible
      (E.kernel n) (E.kernel_posDef n) treatment controls (E.information n)
      (E.information_is_minimum n) hinformation_pos trueWeight
      (by simpa [trueWeight, treatment] using htrue_feasible.1)
      (by simpa [trueWeight, controls] using htrue_feasible.2)
  have htrue_energy : quadraticForm (trueCovariance E n) trueWeight =
      observedTrueGLSTreatmentVariance E n := by
    simpa [trueWeight] using
      observedTrueGLSOutcomeWeight_quadraticForm_eq_treatmentVariance
        E covariance n hfull
  have hlower_factor_nonneg : 0 ≤ covariance.sigmaSquared /
      (1 + covariance.delta n) := by
    exact div_nonneg covariance.sigmaSquared_pos.le hplus_pos.le
  have hlower_division : covariance.sigmaSquared /
      ((1 + covariance.delta n) * E.information n) =
      (covariance.sigmaSquared / (1 + covariance.delta n)) *
        (1 / E.information n) := by
    field_simp [ne_of_gt hplus_pos, ne_of_gt hinformation_pos]
  have hworking_lower : (covariance.sigmaSquared /
      (1 + covariance.delta n)) * quadraticForm (E.kernel n) trueWeight ≤
      quadraticForm (trueCovariance E n) trueWeight := by
    calc
      (covariance.sigmaSquared / (1 + covariance.delta n)) *
          quadraticForm (E.kernel n) trueWeight =
          quadraticForm ((covariance.sigmaSquared /
            (1 + covariance.delta n)) • E.kernel n) trueWeight :=
        (quadraticForm_smul _ _ _).symm
      _ ≤ quadraticForm (trueCovariance E n) trueWeight :=
        quadraticForm_mono_of_posSemidef_sub hsandwich_lower trueWeight
  have hlower : covariance.sigmaSquared /
      ((1 + covariance.delta n) * E.information n) ≤
      observedTrueGLSTreatmentVariance E n := by
    calc
      covariance.sigmaSquared / ((1 + covariance.delta n) * E.information n) =
          (covariance.sigmaSquared / (1 + covariance.delta n)) *
            (1 / E.information n) := hlower_division
      _ ≤ (covariance.sigmaSquared / (1 + covariance.delta n)) *
          quadraticForm (E.kernel n) trueWeight :=
        mul_le_mul_of_nonneg_left hworking_dual hlower_factor_nonneg
      _ ≤ quadraticForm (trueCovariance E n) trueWeight := hworking_lower
      _ = observedTrueGLSTreatmentVariance E n := htrue_energy
  have hworking_feasible : Matrix.transpose design *ᵥ workingWeight =
      Pi.single (0 : Fin (E.q + 1)) 1 := by
    rw [show design = regionalDesign μ E.maps E.treatment E.controls n by rfl,
      show workingWeight = observedWorkingGLSOutcomeWeight E n by rfl,
      transpose_regionalDesign_mulVec_observedWorkingGLSOutcomeWeight_eq_first E n hfull]
    ext j
    by_cases hj : j = 0
    · subst j
      simp
    · simp [hj]
  have hminimal : observedTrueGLSTreatmentVariance E n ≤
      quadraticForm (trueCovariance E n) workingWeight := by
    change trueGLSCoefficientCovariance (trueCovariance E n) design 0 0 ≤ _
    exact trueGLSCoefficientCovariance_diag_le_quadraticForm_of_feasible
      (trueCovariance E n) design htrueCovariance htrueGram 0 workingWeight hworking_feasible
  have hworking_energy : quadraticForm (E.kernel n) workingWeight =
      1 / E.information n := by
    simpa [workingWeight] using
      observedWorkingGLSOutcomeWeight_quadraticForm_eq_inv_information E n hfull
  have hworking_upper : quadraticForm (trueCovariance E n) workingWeight ≤
      (covariance.sigmaSquared / (1 - covariance.delta n)) /
        E.information n :=
    quadraticForm_le_scale_div_information hsandwich_upper workingWeight hworking_energy
  have hupper_division : (covariance.sigmaSquared /
      (1 - covariance.delta n)) / E.information n =
      covariance.sigmaSquared /
        ((1 - covariance.delta n) * E.information n) := by
    field_simp [ne_of_gt hminus_pos, ne_of_gt hinformation_pos]
  have hupper : observedTrueGLSTreatmentVariance E n ≤
      covariance.sigmaSquared / ((1 - covariance.delta n) * E.information n) := by
    exact hminimal.trans (hworking_upper.trans_eq hupper_division)
  exact ⟨hlower, hupper⟩

/-- The paper's displayed treatment-variance sandwich on its actual eventual
tail. The only discarded indices are those before the source covariance
sandwich or the existing eventual full-rank condition applies. -/
theorem eventually_observedTrueGLSTreatmentVariance_sandwich
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    ∀ᶠ n in atTop,
      covariance.sigmaSquared / ((1 + covariance.delta n) * E.information n) ≤
          observedTrueGLSTreatmentVariance E n ∧
        observedTrueGLSTreatmentVariance E n ≤
          covariance.sigmaSquared / ((1 - covariance.delta n) * E.information n) := by
  rcases E.eventual_full_rank with ⟨rankStart, hfull⟩
  filter_upwards [eventually_ge_atTop covariance.start,
    eventually_ge_atTop rankStart] with n hstart hrank
  exact observedTrueGLSTreatmentVariance_sandwich_of_full_rank E covariance n hstart
    (hfull n hrank)

/-- The exact normalized consequence following the displayed sandwich in
Appendix `lem:mean`: with the paper's unchanged `v_n`,
`Q_n v_n → sigma²`. This is a separate source bridge from L-047's narrower
`v_n → 0` result. -/
theorem information_mul_observedTrueGLSTreatmentVariance_tendsto_sigmaSquared
    {D : CompactEuclideanDomain} {Ω : Type v} [MeasurableSpace Ω]
    {μ : Measure (Point D)} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : FixedConditionalExperiment μ P) (covariance : CovarianceAssumption E) :
    Tendsto (fun n => E.information n * observedTrueGLSTreatmentVariance E n)
      atTop (nhds covariance.sigmaSquared) := by
  have hdelta : ∀ᶠ n in atTop,
      0 ≤ covariance.delta n ∧ covariance.delta n < 1 := by
    filter_upwards [eventually_ge_atTop covariance.start] with n hstart
    rcases covariance.sandwich n hstart with ⟨hnonneg, hlt, _, _⟩
    exact ⟨hnonneg, hlt⟩
  have hinformation_pos : ∀ᶠ n in atTop, 0 < E.information n :=
    E.information_tendsto.eventually (eventually_gt_atTop (0 : ℝ))
  have hsandwich :=
    eventually_observedTrueGLSTreatmentVariance_sandwich E covariance
  have hnormalized_sandwich : ∀ᶠ n in atTop,
      covariance.sigmaSquared / (1 + covariance.delta n) ≤
          E.information n * observedTrueGLSTreatmentVariance E n ∧
        E.information n * observedTrueGLSTreatmentVariance E n ≤
          covariance.sigmaSquared / (1 - covariance.delta n) := by
    filter_upwards [hdelta, hinformation_pos, hsandwich] with
      n hdelta_n hinformation hs
    have hplus_pos : 0 < 1 + covariance.delta n := by linarith [hdelta_n.1]
    have hminus_pos : 0 < 1 - covariance.delta n := by linarith [hdelta_n.2]
    constructor
    · calc
        covariance.sigmaSquared / (1 + covariance.delta n) =
            E.information n *
              (covariance.sigmaSquared /
                ((1 + covariance.delta n) * E.information n)) := by
              field_simp [ne_of_gt hplus_pos, ne_of_gt hinformation]
        _ ≤ E.information n * observedTrueGLSTreatmentVariance E n :=
          mul_le_mul_of_nonneg_left hs.1 hinformation.le
    · calc
        E.information n * observedTrueGLSTreatmentVariance E n ≤
            E.information n *
              (covariance.sigmaSquared /
                ((1 - covariance.delta n) * E.information n)) :=
          mul_le_mul_of_nonneg_left hs.2 hinformation.le
        _ = covariance.sigmaSquared / (1 - covariance.delta n) := by
          field_simp [ne_of_gt hminus_pos, ne_of_gt hinformation]
  have hratio : Tendsto
      (fun n => (E.information n * observedTrueGLSTreatmentVariance E n) /
        covariance.sigmaSquared) atTop (nhds 1) :=
    InfillGLSLean.normalizedVariance_tendsto_one_of_eventually_covariance_sandwich
      covariance.sigmaSquared_pos
      (hdelta.mono fun _ h => h.1)
      (hdelta.mono fun _ h => h.2)
      covariance.delta_tendsto_zero hnormalized_sandwich
  have hscaled : Tendsto
      (fun n => ((E.information n * observedTrueGLSTreatmentVariance E n) /
        covariance.sigmaSquared) * covariance.sigmaSquared) atTop
        (nhds (1 * covariance.sigmaSquared)) :=
    hratio.mul tendsto_const_nhds
  have hcancel : (fun n => ((E.information n *
      observedTrueGLSTreatmentVariance E n) / covariance.sigmaSquared) *
        covariance.sigmaSquared) =
      fun n => E.information n * observedTrueGLSTreatmentVariance E n := by
    funext n
    field_simp [covariance.sigmaSquared_pos.ne']
  rw [hcancel] at hscaled
  simpa using hscaled

end InfillGLSLean.ManuscriptSpecification.L048
