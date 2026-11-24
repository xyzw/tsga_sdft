import TSGA.SmallBallReplacementDomains

/-! # The two ordered Poisson island pairs for a physical spiral taper -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW Set Metric Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

structure FrozenTaperRegular {K : Set Position} (t : SpiralTaper K) where
  grad : Position → Position
  shape : Continuous t.shape
  mass : Integrable t.shape
  lip : LocallyLipschitz fun x => √(t.shape x)
  weak : ∀ i, WeakPartialOn univ i (fun x => √(t.shape x)) (fun x => grad x i)
  fisher : Integrable (K.indicator (fun x => ‖grad x‖^2))

private theorem rotate_linear (q : ℝ) (a : ℝ) (A B : SpinMatrix) :
    rotate q (a • A + B) = a • rotate q A + rotate q B := by
  simp only [rotate, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem rotate_real_smul (q a : ℝ) (A : SpinMatrix) : rotate q (a • A) = a • rotate q A := by
  simp only [rotate, Matrix.mul_smul, Matrix.smul_mul]

private theorem taper_real (a : ℝ) (B : SpinMatrix) : (a : ℂ) • B = a • B := by
  ext i j
  exact (Complex.real_smul ..).symm

private theorem frozen_affine_matrix {K : Set Position} (t : SpiralTaper K) (D : Density) (b : ℝ)
    (A : SpinMatrix) (pos) (x : Position) :
    (rotatedDensity (t.affineDensity D b A pos) (frozenLinearPhase t.wavevector)).matrix x =
      t.shape x • (b • rotate ⟪t.wavevector,x⟫_ℝ (D.matrix x) + rotate ⟪t.wavevector,x⟫_ℝ A) := by
  change rotate _ (t.shape x • (b • D.matrix x+A)) = _
  rw [rotate_real_smul,rotate_linear]
  rfl

private theorem density_ext_matrix {A B : Density} (h : A.matrix = B.matrix) : A = B := by
  cases A
  cases B
  congr

/-- Construct the regular backgrounds and combined densities in both
directions. The added density itself only needs its charge and form domain. -/
theorem frozen_island_pairs {K : Set Position} (hK : IsCompact K) {t : SpiralTaper K}
    (treg : FrozenTaperRegular t) (F : FisherSobolevCalculus) (chain : WeakPhaseProduct)
    {D : Density} {S T : MatrixGradient} (cont : Continuous D.matrix) (reg : SqrtRegular D S)
    (ref : Integrable (kineticDensity T)) (cmp : ∀ᵐ x, kineticDensity S x ≤ kineticDensity T x)
    {lo hi : SpinMatrix} (pl : lo.PosSemidef) (ph : hi.PosSemidef)
    {ε dist r : ℝ} (he : 0 < ε) (hle : ε ≤ 1)
    (small : ∀ x ∈ K, lo ≤ D.matrix x ∧ D.matrix x ≤ hi ∧
      hilbertSchmidt (D.matrix x-lo) ≤ dist ∧ hilbertSchmidt (hi-D.matrix x) ≤ dist)
    (cap : ∀ x ∈ K, lo.trace.re ≤ 2*r ∧ D.charge x ≤ 2*r) :
    ∃ pairs : TileIslandPairs t D lo hi ε dist,
      sqrtKinetic pairs.lower_grad.background ≤ affineSpiralKinetic t T treg.grad 1 (2*r) ∧
      sqrtKinetic pairs.upper_grad.background ≤ affineSpiralKinetic t T treg.grad 1 (2*r) ∧
      sqrtKinetic pairs.lower_grad.mixed ≤ affineSpiralKinetic t T treg.grad ε⁻¹ (2*dist + ε*(2*r)) ∧
      sqrtKinetic pairs.upper_grad.mixed ≤ affineSpiralKinetic t T treg.grad ε⁻¹ (2*dist + ε*(2*r)) := by
  let L := constantSpinDensity lo pl
  let H := constantSpinDensity hi ph
  have low (x) (hx : x ∈ K) : L.matrix x ≤ D.matrix x := (small x hx).1
  have high (x) (hx : x ∈ K) : D.matrix x ≤ H.matrix x := (small x hx).2.1
  let obj (b : ℝ) (A : SpinMatrix) (pos) := rotatedDensity (t.affineDensity D b A pos) (frozenLinearPhase t.wavevector)
  have mk (b a δ v : ℝ) (A : SpinMatrix) (pos : ∀ x ∈ K, (b • D.matrix x + A).PosSemidef)
      (order : ∀ x ∈ K, δ • D.matrix x ≤ b • D.matrix x+A) (hδ : 0 ≤ δ)
      (hab : b^2 ≤ a*δ) (ha : 0 ≤ a) (tr : ∀ x ∈ K, (b • D.matrix x + A).trace.re ≤ v) :
      ∃ Z, SqrtRegular (obj b A pos) Z ∧ sqrtKinetic Z ≤ affineSpiralKinetic t T treg.grad a v := by
    obtain ⟨Z,ok,h⟩ := t.affine_spiral_regular hK F chain reg cont pos order hδ hab ha tr
      treg.lip treg.grad treg.weak treg.shape treg.mass treg.fisher
    have av := integral_mono_ae (window_product_integrable t.range treg.shape.aemeasurable reg.grad.integrable_sq)
      (window_product_integrable t.range treg.shape.aemeasurable ref)
      (cmp.mono fun x hx => mul_le_mul_of_nonneg_left hx (t.range x).1)
    change (∫ x, t.shape x*kineticDensity S x) ≤ (∫ x, t.shape x*kineticDensity T x) at av
    refine ⟨Z,ok,h.trans ?_⟩
    unfold affineSpiralKinetic
    linarith only [mul_le_mul_of_nonneg_left av ha]
  have zeropos : ∀ x ∈ K, ((0:ℝ) • D.matrix x + lo).PosSemidef := by simpa using (fun _ _ => pl)
  have idpos : ∀ x ∈ K, ((1:ℝ) • D.matrix x + 0).PosSemidef := by simpa using (fun x _ => D.positive x)
  obtain ⟨Zl,rl,cl⟩ := mk 0 1 0 (2*r) lo zeropos (by simpa using fun _ _ => pl.nonneg) le_rfl (by norm_num)
    zero_le_one (by simpa using fun x hx => (cap x hx).1)
  obtain ⟨Zd,rd,cd⟩ := mk 1 1 1 (2*r) 0 idpos (by simp) zero_le_one (by norm_num)
    zero_le_one (by simpa [Density.charge] using fun x hx => (cap x hx).2)
  have eLo : obj 0 lo zeropos = t.field L := by
    apply density_ext_matrix
    funext x
    rw [show (obj 0 lo zeropos).matrix x = _ from frozen_affine_matrix t D 0 lo zeropos x]
    simp only [SpiralTaper.field,L,constantSpinDensity,cutoffSpiral,taper_real,zero_smul,zero_add]
  have eD : obj 1 0 idpos = t.field D := by
    apply density_ext_matrix
    funext x
    rw [show (obj 1 0 idpos).matrix x = _ from frozen_affine_matrix t D 1 0 idpos x]
    simp only [SpiralTaper.field,cutoffSpiral,taper_real,one_smul,rotate,Matrix.mul_zero,Matrix.zero_mul,add_zero]
  rw [eLo] at rl
  rw [eD] at rd
  let b := ε-1
  have b₂ : b^2 ≤ 1 := by nlinarith only [mul_nonneg he.le (by linarith : 0 ≤ 2-ε)]
  have ol (x) (hx : x ∈ K) : ε • D.matrix x ≤ (1:ℝ) • D.matrix x + b • lo := by
    have h := smul_le_smul_of_nonneg_left (low x hx) (sub_nonneg.mpr hle)
    change (1-ε) • lo ≤ (1-ε) • D.matrix x at h
    rw [sub_smul,sub_smul,one_smul,one_smul] at h
    simp only [b,sub_smul,one_smul]
    exact sub_nonneg.mp (by convert sub_nonneg.mpr h using 1; abel)
  have oh (x) (hx : x ∈ K) : ε • D.matrix x ≤ b • D.matrix x + hi := by
    simp only [b,sub_smul,one_smul]
    have h := high x hx
    change D.matrix x ≤ hi at h
    exact sub_nonneg.mp (by convert sub_nonneg.mpr h using 1; abel)
  have lpos (x) (hx : x ∈ K) := nonneg_iff_posSemidef.mp (((D.positive x).smul he.le).nonneg.trans (ol x hx))
  have hpos (x) (hx : x ∈ K) := nonneg_iff_posSemidef.mp (((D.positive x).smul he.le).nonneg.trans (oh x hx))
  have trlo (x) (hx : x ∈ K) : ((1:ℝ) • D.matrix x + b • lo).trace.re ≤ 2*dist + ε*(2*r) := by
    have h := (le_abs_self _).trans ((abs_trace_re_le_hilbertSchmidt (D.matrix x-lo)).trans
      (mul_le_mul_of_nonneg_left (small x hx).2.2.1 (by norm_num : 0 ≤ (2:ℝ))))
    simp only [Matrix.trace_sub,Complex.sub_re] at h
    simp only [one_smul,Matrix.trace_add,Matrix.trace_smul,Complex.add_re,Complex.real_smul,Complex.re_ofReal_mul]
    dsimp only [b]
    nlinarith only [h,mul_le_mul_of_nonneg_left (cap x hx).1 he.le]
  have trhi (x) (hx : x ∈ K) : (b • D.matrix x + hi).trace.re ≤ 2*dist + ε*(2*r) := by
    have h := (le_abs_self _).trans ((abs_trace_re_le_hilbertSchmidt (hi-D.matrix x)).trans
      (mul_le_mul_of_nonneg_left (small x hx).2.2.2 (by norm_num : 0 ≤ (2:ℝ))))
    simp only [Matrix.trace_sub,Complex.sub_re] at h
    simp only [Matrix.trace_add,Matrix.trace_smul,Complex.add_re,Complex.real_smul,Complex.re_ofReal_mul]
    dsimp only [b]
    have g := (cap x hx).2
    change (D.matrix x).trace.re ≤ 2*r at g
    nlinarith only [h,mul_le_mul_of_nonneg_left g he.le]
  obtain ⟨Xl,wl,al⟩ := mk 1 ε⁻¹ ε _ (b • lo) lpos ol he.le (by simp [he.ne']) (inv_nonneg.mpr he.le) trlo
  obtain ⟨Xh,wh,ah⟩ := mk b ε⁻¹ ε _ hi hpos oh he.le (by simpa [he.ne'] using b₂) (inv_nonneg.mpr he.le) trhi
  have sum_l (x) : (obj 1 (b • lo) lpos).matrix x = (t.residual L D low).matrix x + ε • (t.field L).matrix x := by
    rw [show (obj 1 (b • lo) lpos).matrix x = _ from frozen_affine_matrix t D 1 (b • lo) lpos x]
    simp only [SpiralTaper.residual,SpiralTaper.field,L,constantSpinDensity,cutoffSpiral,taper_real,rotate_real_smul,one_smul]
    simp only [rotate, Matrix.mul_sub, Matrix.sub_mul, b, sub_smul, one_smul, smul_add, smul_sub, smul_smul]
    module
  have sum_h (x) : (obj b hi hpos).matrix x = (t.residual D H high).matrix x + ε • (t.field D).matrix x := by
    rw [show (obj b hi hpos).matrix x = _ from frozen_affine_matrix t D b hi hpos x]
    simp only [SpiralTaper.residual,SpiralTaper.field,H,constantSpinDensity,cutoffSpiral,taper_real]
    simp only [rotate, Matrix.mul_sub, Matrix.sub_mul, b, sub_smul, one_smul, smul_add, smul_sub, smul_smul]
    module
  exact ⟨⟨pl,ph,low,high,fun x hx => (small x hx).2.2.1,fun x hx => (small x hx).2.2.2,
    ⟨Zl,rl,_,sum_l,Xl,wl⟩, ⟨Zd,rd,_,sum_h,Xh,wh⟩,
    taper_domain hK t treg.shape L D continuous_const cont low,
    taper_domain hK t treg.shape D H cont continuous_const high⟩, cl, cd, al, ah⟩

end TSGA.ManyBody
