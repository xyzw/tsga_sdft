import TSGA.CoulombRotationReplacement
import TSGA.ActualTileFisher
import TSGA.VariableWindowTrial
import TSGA.MatrixChainRule

/-! # Fisher bounds for the ordered additions on a small ball

The square root required by the island trial belongs to the residual plus
ε times the background. The affine combination is positive on the support
of the window. Its derivative in the density variable costs at most 1/ε,
including when the density has a kernel.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW Set Metric Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace ContDiff

private theorem smooth_partial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : Position → F) (h : ContDiff ℝ ∞ f) (i : Fin 3) :
    WeakPartialOn univ i f (fun x => fderiv ℝ f x (PiLp.single 2 i 1)) := by
  let v : Position := PiLp.single 2 i 1
  have hd := (h.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
  refine ⟨h.continuous.locallyIntegrable.locallyIntegrableOn _, hd.locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro ψ hψ hs _
  have hψd := (hψ.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
  have ibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := ψ) (g := f) (v := v)
    ((hψd.smul h.continuous).integrable_of_hasCompactSupport (hs.fderiv_apply ℝ v).smul_right)
    ((hψ.continuous.smul hd).integrable_of_hasCompactSupport hs.smul_right)
    ((hψ.continuous.smul h.continuous).integrable_of_hasCompactSupport hs.smul_right)
    (fun x _ => hψ.differentiable (by simp) x) (fun x _ => h.differentiable (by simp) x)
  simpa only [Measure.restrict_univ, neg_neg] using congrArg Neg.neg ibp.symm

def frozenLinearPhase (q : Position) : Phase :=
  ⟨fun x => ⟪q,x⟫_ℝ, fun _ => q, fun _ _ _ => 0⟩

theorem frozenLinearPhase_regular (q : Position) : (frozenLinearPhase q).Regular 2 := by
  have loc (f : Position → ℝ) (hf : Continuous f) : LocalLpOn univ 2 f := by
    intro x _
    refine ⟨1, zero_lt_one, subset_univ _, ?_⟩
    obtain ⟨C,hC⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hf.continuousOn
    let : IsFiniteMeasure (volume.restrict (ball x 1)) := ⟨by
      simpa using measure_ball_lt_top (μ := volume) (x := x) (r := 1)⟩
    exact MemLp.of_bound hf.aestronglyMeasurable C
      ((ae_restrict_mem measurableSet_ball).mono fun y hy => hC y (ball_subset_closedBall hy))
  let l : Position →L[ℝ] ℝ := innerSL ℝ q
  refine ⟨continuous_const, loc l l.continuous, fun i => loc (fun _ => q i) continuous_const,
    fun _ _ => loc (fun _ => 0) continuous_const, ?_, ?_⟩
  · intro i
    have de (x : Position) : fderiv ℝ l x (PiLp.single 2 i 1) = q i := by
      rw [l.fderiv]
      simp [l, EuclideanSpace.inner_single_right]
    have el : (l : Position → ℝ) = (fun x => ⟪q,x⟫_ℝ) := funext fun _ => rfl
    have hw := smooth_partial l l.contDiff i
    rw [show (fun x => fderiv ℝ l x (PiLp.single 2 i 1)) = (fun _ : Position => q i) from funext de, el] at hw
    exact hw
  · intro i j
    simpa [frozenLinearPhase] using smooth_partial (fun _ : Position => q j) contDiff_const i

private theorem se_root (M : SpinMatrix) (h : M.PosSemidef) : RootTangent M M := by
  refine ⟨(1/2:ℝ) • CFC.sqrt M, ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, CFC.sqrt_mul_sqrt_self _ h.nonneg, ← add_smul]
  norm_num

private theorem fisher_zero (Q : RootFisherForm) {P : SpinMatrix} (h : P.PosSemidef) :
    Q.sq P 0 = 0 := by
  have hh := Q.order h h (se_root P h) (a := 1) (b := 0) (u := 0) zero_le_one le_rfl
    (by simp) (by simp)
  simpa only [zero_smul, zero_mul] using le_antisymm hh (by simpa using Q.nonneg P 0)

/-- Fisher estimate for differentiating a windowed affine function of a matrix.
The matrix A may have zero eigenvalues. -/
private theorem affine_fisher (Q : RootFisherForm) {D P Y : SpinMatrix} {a h g b δ : ℝ}
    (hD : D.PosSemidef) (hP : P.PosSemidef) (tangent : RootTangent D Y)
    (hd : 0 ≤ δ) (hord : δ • D ≤ P) (hb : b^2 ≤ a*δ) (ha : 0 ≤ a) :
    Q.sq (h^2 • P) ((b*h^2) • Y + (2*h*g) • P) ≤
      4*(a*h^2*Q.sq D Y+g^2*P.trace.re) := by
  have hp := hP.smul (sq_nonneg h)
  have hh := Q.order hD hp tangent (a := h^2*δ) (b := a*h^2) (u := b*h^2)
    (mul_nonneg (sq_nonneg h) hd) (mul_nonneg ha (sq_nonneg h))
    (by rw [← smul_smul]; exact smul_le_smul_of_nonneg_left hord (sq_nonneg h))
    (by nlinarith only [mul_le_mul_of_nonneg_right hb (sq_nonneg (h^2))])
  have hg := Q.order hP hp (se_root P hP) (a := h^2) (b := 4*g^2) (u := 2*h*g)
    (sq_nonneg h) (by positivity) le_rfl (by nlinarith)
  have radial := mul_le_mul_of_nonneg_left (Q.radial _ hP) (show 0 ≤ 4*g^2 by positivity)
  have add := Q.add_four (h^2 • P) ((b*h^2) • Y) ((2*h*g) • P) 0 0
  rw [add_zero, add_zero, fisher_zero Q hp, add_zero, add_zero] at add
  linarith only [add, hh, hg, radial]

/-- The density obtained by cutting off an affine positive field.
Off the comparison ball the cutoff vanishes. -/
def SpiralTaper.affineDensity {K : Set Position} (t : SpiralTaper K) (D : Density)
    (b : ℝ) (A : SpinMatrix) (pos : ∀ x ∈ K, (b • D.matrix x + A).PosSemidef) : Density where
  matrix x := t.shape x • (b • D.matrix x + A)
  positive x := by
    by_cases hx : x ∈ K
    · exact (pos x hx).smul (t.range x).1
    · simp [t.outside x hx, Matrix.PosSemidef.zero]

/-- The available weak derivative of the untapered aligned field only enters
multiplied by the cutoff. The boundary term samples its affine charge bound. -/
theorem SpiralTaper.affine_sqrt_regular {K : Set Position} (t : SpiralTaper K) (meas : MeasurableSet K) (F : FisherSobolevCalculus)
    {D : Density} {S : MatrixGradient} (reg : SqrtRegular D S) {b a δ cap : ℝ} {A : SpinMatrix}
    (pos : ∀ x ∈ K, (b • D.matrix x + A).PosSemidef) (order : ∀ x ∈ K, δ • D.matrix x ≤ b • D.matrix x + A)
    (hd : 0 ≤ δ) (hb : b^2 ≤ a*δ) (ha : 0 ≤ a)
    (charge : ∀ x ∈ K, (b • D.matrix x + A).trace.re ≤ cap)
    (lip : LocallyLipschitz fun x => √(t.shape x)) (g : Position → Position)
    (weak : ∀ i, WeakPartialOn univ i (fun x => √(t.shape x)) (fun x => g x i))
    (mass : Integrable (t.affineDensity D b A pos).charge) (shape : AEMeasurable t.shape volume)
    (fisher : Integrable (K.indicator (fun x => ‖g x‖^2))) :
    let N := t.affineDensity D b A pos
    SqrtRegular N (F.gradient N) ∧ sqrtKinetic (F.gradient N) ≤
      4*(a*(∫ x, t.shape x*kineticDensity S x)+cap*(∫ x in K, ‖g x‖^2)) := by
  classical
  intro N
  let h := fun x => √(t.shape x)
  let B := fun x => b • D.matrix x + A
  let Y := squareDerivative D S
  let Z : MatrixGradient := fun x i => (b*h x^2) • Y x i + (2*h x*(g x i)) • B x
  let w := fun x => 4*(a*(t.shape x*kineticDensity S x)+cap*(K.indicator (fun x => ‖g x‖^2) x))
  have hshape x : h x^2 = t.shape x := Real.sq_sqrt (t.range x).1
  have sqweak := F.square_weak _ _ reg
  have cweak : IsMatrixGradientOn univ (fun _ => A) (fun _ _ => 0) := by
    intro i j k
    simpa using smooth_partial (fun _ : Position => A j k) contDiff_const i
  have zw : IsMatrixGradientOn univ N.matrix Z := by
    have hw := F.product_rule _ _ _ _ h h (fun x i => g x i) (fun x i => g x i) b 1 sqweak cweak lip lip weak weak
    have efield : N.matrix = fun x => (b*h x^2) • D.matrix x + (1*h x^2) • A := by
      funext x
      simp only [N, SpiralTaper.affineDensity, ← hshape, smul_add, smul_smul, one_mul, mul_comm b]
    have egrad : Z = fun x i => (b*h x^2) • Y x i + (1*h x^2) • (0:SpinMatrix) +
        (2*b*h x*(g x i)) • D.matrix x + (2*1*h x*(g x i)) • A := by
      funext x i
      simp only [Z, B, smul_add, smul_smul, smul_zero, add_zero, mul_one, add_assoc]
      rw [show 2*h x*(g x i)*b = 2*b*h x*(g x i) by ring]
    rw [efield, egrad]
    exact hw
  have wi : Integrable (fun x => t.shape x * kineticDensity S x) := window_product_integrable t.range shape reg.grad.integrable_sq
  have imaj : Integrable w := ((wi.const_mul a).add (fisher.const_mul cap)).const_mul 4
  have hmajor : ∀ᵐ x, (∑ i, F.sq (N.matrix x) (Z x i)) ≤ w x := by
    filter_upwards [F.square_cost D S reg] with x hx
    by_cases mem : x ∈ K
    · have ss (i : Fin 3) := affine_fisher F.toRootFisherForm (h := h x) (g := g x i) (Y := Y x i)
        (hD := D.positive x) (hP := pos x mem) ⟨S x i,rfl⟩ hd (order x mem) hb ha
      change (∑ i, F.sq (t.shape x • B x) (Z x i)) ≤ _
      simp only [← hshape x, Z]
      have sum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ss i)
      refine sum.trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      have gs : (∑ i, (g x i)^2) = ‖g x‖^2 := by simp [PiLp.norm_sq_eq_of_L2]
      simp only [w, indicator_of_mem mem, gs, hshape x]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (t.range x).1) ha)
        (by simpa [mul_comm] using mul_le_mul_of_nonneg_left (charge x mem) (sq_nonneg ‖g x‖))
    · have he : h x = 0 := by simp [h,t.outside x mem]
      simp [w,N,SpiralTaper.affineDensity,Z,he,t.outside x mem,mem,fisher_zero F.toRootFisherForm PosSemidef.zero]
  obtain ⟨regular, ub⟩ := F.regularize N Z w mass zw imaj hmajor
  refine ⟨regular, (integral_mono_ae regular.grad.integrable_sq imaj ub).trans_eq ?_⟩
  dsimp only [w]
  rw [integral_const_mul,integral_add (wi.const_mul a) (fisher.const_mul cap),integral_const_mul,
    integral_const_mul, integral_indicator meas]
end TSGA.ManyBody
