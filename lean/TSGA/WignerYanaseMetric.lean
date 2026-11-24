import TSGA.SpectralLipschitz
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! # Convexity and monotonicity of the matrix Fisher form, Lemma A.1

In matrix-entry coordinates the square of the Sylvester operator has
diagonal part A ⊗ I + I ⊗ Aᵀ and cross term 2 √A ⊗ √(Aᵀ).
The variational inverse quadratic form takes values in the extended
nonnegative reals, so singular matrices are included. -/

noncomputable section
namespace TSGA.ManyBody
open Matrix TSGA.Localization
open scoped ComplexOrder MatrixOrder Kronecker ENNReal

private abbrev PairIndex := Fin 2 × Fin 2
private abbrev HSTest := PairIndex → ℂ
private abbrev HSOperator := Matrix PairIndex PairIndex ℂ

/-- The superadditive form of Lieb's joint concavity theorem at exponent
one half, for tensor products of two positive matrix square roots. -/
def TensorSqrtSuperadditive : Prop :=
  ∀ A B C D : SpinMatrix, A.PosSemidef → B.PosSemidef → C.PosSemidef → D.PosSemidef →
    CFC.sqrt A ⊗ₖ CFC.sqrt C + CFC.sqrt B ⊗ₖ CFC.sqrt D ≤ CFC.sqrt (A+B) ⊗ₖ CFC.sqrt (C+D)

private def weight (A : SpinMatrix) : HSOperator :=
  A ⊗ₖ (1 : SpinMatrix) + (1 : SpinMatrix) ⊗ₖ A.transpose +
    (2 : ℝ) • (CFC.sqrt A ⊗ₖ CFC.sqrt A.transpose)

private def pairing (x y : HSTest) : ℝ := (star x ⬝ᵥ y).re
private def entries (Y : SpinMatrix) : HSTest := fun ij => Y ij.1 ij.2
private def testValue (A Y : SpinMatrix) (x : HSTest) : ℝ :=
  2*pairing x (entries Y) - pairing x (weight A *ᵥ x)

/-- The extended Wigner–Yanase form Q(A,Y), in the normalization of Lemma A.1. -/
def wignerYanase (A Y : SpinMatrix) : ℝ≥0∞ := ⨆ x : HSTest, ENNReal.ofReal (testValue A Y x)

private def sylvester (A : SpinMatrix) : HSOperator :=
  CFC.sqrt A ⊗ₖ (1 : SpinMatrix) + (1 : SpinMatrix) ⊗ₖ CFC.sqrt A.transpose

private theorem weight_eq_square {A : SpinMatrix} (hA : A.PosSemidef) :
    weight A = sylvester A * sylvester A := by
  simp only [weight,sylvester,add_mul,mul_add,← mul_kronecker_mul,mul_one,one_mul,
    CFC.sqrt_mul_sqrt_self _ hA.nonneg,CFC.sqrt_mul_sqrt_self _ hA.transpose.nonneg,two_smul]
  abel

private theorem sylvester_pos (A : SpinMatrix) : (sylvester A).PosSemidef :=
  ((nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).kronecker PosSemidef.one).add
    (PosSemidef.one.kronecker (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.transpose)))

private theorem sylvester_apply {A : SpinMatrix} (ha : A.PosSemidef) (X : SpinMatrix) :
    sylvester A *ᵥ entries X = entries (CFC.sqrt A * X + X * CFC.sqrt A) := by
  have ht : CFC.sqrt A.transpose = (CFC.sqrt A).transpose := by
    apply (CFC.sqrt_eq_iff _ _ ha.transpose.nonneg
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).transpose.nonneg).2
    rw [← transpose_mul,CFC.sqrt_mul_sqrt_self _ ha.nonneg]
  change sylvester A *ᵥ X.transpose.vec = (CFC.sqrt A * X + X * CFC.sqrt A).transpose.vec
  simp only [sylvester,ht,add_mulVec,kronecker_mulVec_vec,one_mul,mul_one,transpose_one,
    transpose_add,transpose_mul,vec_add]

private theorem pairing_self (x : HSTest) : pairing x x = ∑ i, ‖x i‖^2 := by
  simp only [pairing,dotProduct,Complex.re_sum,Pi.star_apply,Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.sq_norm]

private theorem pairing_entries (X : SpinMatrix) :
    pairing (entries X) (entries X) = hilbertSchmidt X ^ 2 := by
  rw [pairing_self,hilbertSchmidt,Real.sq_sqrt (by positivity)]
  exact Fintype.sum_prod_type _

private theorem pairing_comm (x y : HSTest) : pairing x y = pairing y x := by
  unfold pairing
  rw [star_dotProduct x y]
  rfl

private theorem sylvester_adjoint (A : SpinMatrix) (x y : HSTest) :
    pairing x (sylvester A *ᵥ y) = pairing (sylvester A *ᵥ x) y := by
  simp only [pairing,star_mulVec,(sylvester_pos A).isHermitian.eq,dotProduct_mulVec]

private theorem sylvester_test {A : SpinMatrix} (hA : A.PosSemidef) (X : SpinMatrix) (x : HSTest) :
    testValue A (CFC.sqrt A*X+X*CFC.sqrt A) x =
      hilbertSchmidt X^2 - pairing (sylvester A *ᵥ x - entries X) (sylvester A *ᵥ x - entries X) := by
  rw [testValue,← sylvester_apply hA,weight_eq_square hA,← mulVec_mulVec,
    sylvester_adjoint,sylvester_adjoint,← pairing_entries]
  have swap := pairing_comm (entries X) (sylvester A *ᵥ x)
  simp only [pairing,star_sub,sub_dotProduct,dotProduct_sub,Complex.sub_re] at swap ⊢
  linarith only [swap]

/-- Every solution of the square-root Sylvester equation bounds Q, even
for a singular density. -/
theorem wignerYanase_sylvester_le {A : SpinMatrix} (hA : A.PosSemidef) (X : SpinMatrix) :
    wignerYanase A (CFC.sqrt A*X+X*CFC.sqrt A) ≤ ENNReal.ofReal (hilbertSchmidt X^2) := by
  apply iSup_le
  intro x
  apply ENNReal.ofReal_le_ofReal
  rw [sylvester_test hA,pairing_self]
  exact sub_le_self _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- For a positive definite density the form is exactly the squared
Hilbert–Schmidt norm of the solution, as in the manuscript. -/
theorem wignerYanase_sylvester {A : SpinMatrix} (hA : A.PosDef) (X : SpinMatrix) :
    wignerYanase A (CFC.sqrt A*X+X*CFC.sqrt A) = ENNReal.ofReal (hilbertSchmidt X^2) := by
  refine le_antisymm (wignerYanase_sylvester_le hA.posSemidef X) ?_
  have root := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).2 hA.isUnit)
  have pos : (sylvester A).PosDef := (root.kronecker PosDef.one).add_posSemidef
    (PosSemidef.one.kronecker (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.transpose)))
  obtain ⟨x,hx⟩ := mulVec_surjective_iff_isUnit.mpr pos.isUnit (entries X)
  refine le_trans ?_ (le_iSup (fun v => ENNReal.ofReal
    (testValue A (CFC.sqrt A*X+X*CFC.sqrt A) v)) x)
  rw [sylvester_test hA.posSemidef,hx,sub_self,pairing_self]
  simp

private theorem weight_pos {A : SpinMatrix} (hA : A.PosSemidef) : (weight A).PosSemidef :=
  ((hA.kronecker PosSemidef.one).add (PosSemidef.one.kronecker hA.transpose)).add
    (((nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).kronecker
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.transpose))).smul (by norm_num : (0:ℝ) ≤ 2))

private theorem sqrt_scale {A : SpinMatrix} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    CFC.sqrt (t • A) = √t • CFC.sqrt A := by
  apply (CFC.sqrt_eq_iff _ _ (hA.smul ht).nonneg (smul_nonneg (Real.sqrt_nonneg _) (CFC.sqrt_nonneg _))).2
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Real.mul_self_sqrt ht,CFC.sqrt_mul_sqrt_self A hA.nonneg]

private theorem weight_scale {A : SpinMatrix} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    weight (t • A) = t • weight A := by
  simp only [weight,transpose_smul,sqrt_scale hA ht,sqrt_scale hA.transpose ht,
    smul_kronecker,kronecker_smul,smul_smul,Real.mul_self_sqrt ht,smul_add,mul_comm (2:ℝ) t]

private theorem weight_add (lieb : TensorSqrtSuperadditive) {A B : SpinMatrix}
    (ha : A.PosSemidef) (hb : B.PosSemidef) : weight A + weight B ≤ weight (A+B) := by
  let U := CFC.sqrt A ⊗ₖ CFC.sqrt A.transpose
  let V := CFC.sqrt B ⊗ₖ CFC.sqrt B.transpose
  let W := CFC.sqrt (A+B) ⊗ₖ CFC.sqrt (A.transpose+B.transpose)
  have huv : U+V ≤ W := lieb _ _ _ _ ha hb ha.transpose hb.transpose
  have double := add_le_add huv huv
  let M := A ⊗ₖ (1 : SpinMatrix) + 1 ⊗ₖ A.transpose
  let N := B ⊗ₖ (1 : SpinMatrix) + 1 ⊗ₖ B.transpose
  calc
    weight A + weight B = (M+N)+((U+V)+(U+V)) := by
      simp only [weight,M,N,U,V,two_smul]
      abel
    _ ≤ (M+N)+(W+W) := add_le_add (le_refl _) double
    _ = weight (A+B) := by
      simp only [weight,M,N,W,transpose_add,add_kronecker,kronecker_add,two_smul]
      abel

private theorem quad_mono {S T : HSOperator} (h : S ≤ T) (x : HSTest) :
    pairing x (S *ᵥ x) ≤ pairing x (T *ᵥ x) := by
  have hx := (RCLike.nonneg_iff.mp ((nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).dotProduct_mulVec_nonneg x)).1
  change 0 ≤ (star x ⬝ᵥ ((T - S) *ᵥ x)).re at hx
  simpa only [pairing,sub_mulVec,dotProduct_sub,Complex.sub_re,sub_nonneg] using hx

private theorem pairing_scale_right (x y : HSTest) (t : ℝ) :
    pairing x (t • y) = t*pairing x y := by
  simp [pairing,dotProduct_smul]

private theorem pairing_scale_left (x y : HSTest) (t : ℝ) :
    pairing (t • x) y = t*pairing x y := by
  simp [pairing,star_smul,smul_dotProduct]

/-- Joint positive homogeneity, also at zero. -/
theorem wignerYanase_homogeneous {A : SpinMatrix} (hA : A.PosSemidef) (Y : SpinMatrix)
    {t : ℝ} (ht : 0 ≤ t) :
    wignerYanase (t • A) (t • Y) = ENNReal.ofReal t*wignerYanase A Y := by
  unfold wignerYanase
  rw [ENNReal.mul_iSup]
  congr 1
  funext x
  rw [← ENNReal.ofReal_mul ht]
  congr 1
  simp only [testValue,show entries (t • Y) = t • entries Y from rfl,weight_scale hA ht,
    smul_mulVec,pairing_scale_right]
  ring

/-- Subadditivity of Q on the full positive cone. -/
theorem wignerYanase_subadd (lieb : TensorSqrtSuperadditive) {A B : SpinMatrix}
    (ha : A.PosSemidef) (hb : B.PosSemidef) (Y Z : SpinMatrix) :
    wignerYanase (A+B) (Y+Z) ≤ wignerYanase A Y + wignerYanase B Z := by
  apply iSup_le
  intro x
  apply le_trans _ ((ENNReal.ofReal_add_le (p := testValue A Y x) (q := testValue B Z x)).trans
    (add_le_add (le_iSup (fun v => ENNReal.ofReal (testValue A Y v)) x)
      (le_iSup (fun v => ENNReal.ofReal (testValue B Z v)) x)))
  apply ENNReal.ofReal_le_ofReal
  have h := quad_mono (weight_add lieb ha hb) x
  simp only [testValue,show entries (Y+Z) = entries Y + entries Z from rfl,
    pairing,add_mulVec,dotProduct_add,Complex.add_re] at h ⊢
  linarith only [h]

theorem wignerYanase_convex (lieb : TensorSqrtSuperadditive) {A B : SpinMatrix}
    (ha : A.PosSemidef) (hb : B.PosSemidef) (Y Z : SpinMatrix) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    wignerYanase (t • A + (1-t) • B) (t • Y + (1-t) • Z) ≤
      ENNReal.ofReal t*wignerYanase A Y + ENNReal.ofReal (1-t)*wignerYanase B Z := by
  simpa only [wignerYanase_homogeneous ha Y ht.1,wignerYanase_homogeneous hb Z (sub_nonneg.mpr ht.2)] using
    wignerYanase_subadd lieb (ha.smul ht.1) (hb.smul (sub_nonneg.mpr ht.2)) (t • Y) ((1-t) • Z)

/-- Enlarging the first argument by a factor c reduces the form by at least
that factor, including on singular density matrices. -/
theorem wignerYanase_order (lieb : TensorSqrtSuperadditive) {A B : SpinMatrix}
    (ha : A.PosSemidef) {c : ℝ} (hc : 0 < c) (h : c • A ≤ B) (Y : SpinMatrix) :
    wignerYanase B Y ≤ ENNReal.ofReal c⁻¹*wignerYanase A Y := by
  have rem := nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)
  have w : weight (c • A) ≤ weight B := by
    have add := weight_add lieb (ha.smul hc.le) rem
    rw [add_sub_cancel ..] at add
    exact (le_add_of_nonneg_right (weight_pos rem).nonneg).trans add
  apply iSup_le
  intro x
  apply le_trans _ (mul_le_mul_right (le_iSup (fun y => ENNReal.ofReal (testValue A Y y)) (c • x)) _)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  apply ENNReal.ofReal_le_ofReal
  have hw := quad_mono w x
  rw [weight_scale ha hc.le,smul_mulVec,pairing_scale_right] at hw
  simp only [testValue,mulVec_smul,pairing_scale_left,pairing_scale_right]
  field_simp [hc.ne']
  linarith only [hw]

open scoped Matrix.Norms.L2Operator Topology
open MeasureTheory Filter

/-- The value on a singular matrix is the right limit of the positive-density
forms obtained by adding a scalar multiple of the identity. -/
theorem wignerYanase_regularization (lieb : TensorSqrtSuperadditive)
    {A : SpinMatrix} (ha : A.PosSemidef) (Y : SpinMatrix) :
    Tendsto (fun t : ℝ => wignerYanase (A+t • 1) Y) (𝓝[>] 0) (𝓝 (wignerYanase A Y)) := by
  let B := fun t : ℝ => A + |t| • (1 : SpinMatrix)
  have hpos (t) : (B t).PosSemidef := ha.add (PosSemidef.one.smul (abs_nonneg t))
  have cb : Continuous B := by dsimp [B]; fun_prop
  have cs : Continuous (fun t => CFC.sqrt (B t)) :=
    CFC.continuousOn_sqrt.comp_continuous cb fun t => (hpos t).nonneg
  have cst : Continuous (fun t => CFC.sqrt (B t).transpose) :=
    CFC.continuousOn_sqrt.comp_continuous cb.matrix_transpose fun t => (hpos t).transpose.nonneg
  have ct (x : HSTest) : Continuous (fun t => ENNReal.ofReal (testValue (B t) Y x)) := by
    apply ENNReal.continuous_ofReal.comp
    unfold testValue pairing weight
    simp only [Matrix.mulVec,dotProduct,Matrix.add_apply,Matrix.smul_apply,kroneckerMap_apply,Matrix.transpose_apply]
    fun_prop
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro a ha'
    obtain ⟨x,hx⟩ := lt_iSup_iff.mp ha'
    have h0 : B 0 = A := by simp [B]
    rw [←h0] at hx
    filter_upwards [((ct x).continuousAt.eventually_const_lt hx).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t h ht
    change 0 < t at ht
    simp only [B,abs_of_pos ht] at h
    exact h.trans_le (le_iSup (fun v => ENNReal.ofReal (testValue (A+t • 1) Y v)) x)
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have hab : (1:ℝ) • A ≤ A+t • (1:SpinMatrix) := by
      simp only [one_smul,le_add_iff_nonneg_right]
      exact (PosSemidef.one.smul ht.le).nonneg
    have h := wignerYanase_order lieb ha zero_lt_one hab Y
    exact (by simpa using h : wignerYanase (A+t • 1) Y ≤ wignerYanase A Y).trans_lt hb

/-- Pointwise matrix Fisher density in any finite number of spatial directions.
For a Sobolev density its arguments are the density and its weak derivatives. -/
def matrixFisherDensity {d : ℕ} (A : SpinMatrix) (Y : Fin d → SpinMatrix) : ℝ≥0∞ :=
  ∑ i, wignerYanase A (Y i)

theorem matrixFisherDensity_subadd (lieb : TensorSqrtSuperadditive) {d : ℕ}
    {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) (Y Z : Fin d → SpinMatrix) :
    matrixFisherDensity (A+B) (Y+Z) ≤ matrixFisherDensity A Y + matrixFisherDensity B Z := by
  unfold matrixFisherDensity
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => wignerYanase_subadd lieb hA hB (Y i) (Z i)

/-- Convexity after integration of the extended Fisher density, including
fields of infinite energy. -/
theorem integral_matrixFisherDensity_convex (lieb : TensorSqrtSuperadditive) {d : ℕ}
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (A B : X → SpinMatrix)
    (Y Z : X → Fin d → SpinMatrix) (hA : ∀ᵐ x ∂μ, (A x).PosSemidef) (hB : ∀ᵐ x ∂μ, (B x).PosSemidef)
    (hm : AEMeasurable (fun x => matrixFisherDensity (A x) (Y x)) μ)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (∫⁻ x, matrixFisherDensity (t • A x+(1-t) • B x) (t • Y x+(1-t) • Z x) ∂μ) ≤
      ENNReal.ofReal t*(∫⁻ x, matrixFisherDensity (A x) (Y x) ∂μ) +
      ENNReal.ofReal (1-t)*(∫⁻ x, matrixFisherDensity (B x) (Z x) ∂μ) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left' (f := fun x => ENNReal.ofReal t * matrixFisherDensity (A x) (Y x))
      (aemeasurable_const.mul hm) (fun x => ENNReal.ofReal (1-t)*matrixFisherDensity (B x) (Z x))]
  apply lintegral_mono_ae
  filter_upwards [hA,hB] with x ha hb
  unfold matrixFisherDensity
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => wignerYanase_convex lieb ha hb (Y x i) (Z x i) ht

end TSGA.ManyBody
