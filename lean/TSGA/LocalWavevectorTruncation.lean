import TSGA.BallTruncatedGradient

/-! # The local truncation estimate for freezing the wavevector on a ball -/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Filter Metric Set TSGA.Localization PhaseLocalization
open scoped Topology

/-- Local hypotheses for the finite right-hand side of Lemma 4.18.
The gradient is given by its continuous representative on the closed ball. -/
structure LocalWavevectorData (D : Density) (φ : Phase) (G : MatrixGradient)
    (p : ℝ) (c : Position) (R : ℝ) : Prop where
  continuous_grad : ContinuousOn φ.grad (closedBall c R)
  grad_Lp : ∀ i, MemLp (fun x => φ.grad x i) (ENNReal.ofReal p) (volume.restrict (ball c R))
  hessian_Lp : ∀ i j, MemLp (fun x => φ.hessian x i j) (ENNReal.ofReal p) (volume.restrict (ball c R))
  weak_hessian : ∀ i j, WeakPartialOn (ball c R) i (fun x => φ.grad x j) (fun x => φ.hessian x i j)
  root_regular : RootRegularOn (ball c R ∩ φ.active) D p G
  charge : IntegrableOn D.charge (closedBall c R)
  weighted : IntegrableOn (weightedRoot φ G p) (closedBall c R)
  curvature : IntegrableOn (fun x => D.charge x * φ.hessianNorm x^p) (closedBall c R)

/-- First-order Sobolev calculus used on a ball. The Leibniz rule for two
Lipschitz compositions is stated in its p-power form. The first factor need
only be locally Sobolev where the second does not vanish in a neighborhood.
The second rule is the ball Morrey inequality integrated from a zero of
the continuous representative. A relative zero neighborhood identifies that
value even when the data are specified only almost everywhere. -/
structure BallTruncationRules (p C : ℝ) : Prop where
  product_chain : ∀ {c : Position} {R : ℝ} {V : Set Position}
    {X : Position → SpinMatrix} {G : MatrixGradient}
    {Y : Position → Position} {H : Position → Fin 3 → Fin 3 → ℝ}
    {u v : Position → ℝ} {a b : ℝ}, 3 < p → 0 < R → V ⊆ ball c R → 0 ≤ a → 0 ≤ b →
    (∀ x ∈ V, ∃ r > 0, ball x r ⊆ V ∧ IsMatrixGradientOn (ball x r) X G ∧
      (∀ j k, MemLp (fun y => X y j k) (ENNReal.ofReal p) (volume.restrict (ball x r))) ∧
      MemLp (matrixGradNorm G) (ENNReal.ofReal p) (volume.restrict (ball x r))) →
    (∀ i, MemLp (fun x => Y x i) (ENNReal.ofReal p) (volume.restrict (ball c R))) →
    (∀ i j, MemLp (fun x => H x i j) (ENNReal.ofReal p) (volume.restrict (ball c R))) →
    (∀ i j, WeakPartialOn (ball c R) i (fun x => Y x j) (fun x => H x i j)) →
    (∀ x ∈ V, ∀ y ∈ V, |u x - u y| ≤ a * hilbertSchmidt (X x - X y)) →
    (∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R, |v x - v y| ≤ b * ‖Y x - Y y‖) →
    (∀ x ∈ ball c R, x ∉ V → ∀ᶠ y in 𝓝[closedBall c R] x, v y = 0) →
    ∃ Z : Position → Position, AEStronglyMeasurable Z (volume.restrict (closedBall c R)) ∧
      (∀ i, WeakPartialOn (ball c R) i (fun x => u x * v x) (fun x => Z x i)) ∧
      ∀ᵐ x ∂volume.restrict (closedBall c R), ‖Z x‖^p ≤ (2 : ℝ)^p *
        ((a * |v x| * matrixGradNorm G x)^p +
          (|u x| * b * Real.sqrt (∑ i, ∑ j, H x i j ^ 2))^p)
  anchored_morrey : ∀ {c z : Position} {R : ℝ} {f : Position → ℝ} {Z : Position → Position},
    3 < p → 0 < R → z ∈ closedBall c R → (∀ᶠ y in 𝓝[closedBall c R] z, f y = 0) →
    (∀ i, WeakPartialOn (ball c R) i f (fun x => Z x i)) →
    IntegrableOn (fun x => |f x|^p) (closedBall c R) →
    IntegrableOn (fun x => ‖Z x‖^p) (closedBall c R) →
    (∫ x in closedBall c R, |f x|^p) ≤ C * R^p * ∫ x in closedBall c R, ‖Z x‖^p

def localTruncationConstant (p C : ℝ) : ℝ := C * 3^p * ((4*p)^p * 4)

/-- The truncation in the proof of Lemma 4.18. Its entire Sobolev argument
uses only the ball and the active part of its interior. -/
theorem local_wavevector_truncation {p C : ℝ} (hp : 3 < p) (hC : 0 ≤ C)
    (rules : BallTruncationRules p C) {D : Density} {φ : Phase} {G : MatrixGradient}
    {c z : Position} {R ℓ ε : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (radius : R ≤ 3*ℓ)
    (he : 0 < ε) (data : LocalWavevectorData D φ G p c R) (hz : z ∈ closedBall c R)
    (minz : IsMinOn (fun x => ‖φ.grad x‖) (closedBall c R) z) :
    let K := closedBall c R
    let g := fun x => D.charge x^(1/p) * truncatedSpeed p (ε^2) ‖φ.grad x - φ.grad z‖
    IntegrableOn (fun x => g x^p) K ∧ (∫ x in K, g x^p) ≤
      localTruncationConstant p C * ℓ^p * ((∫ x in K, weightedRoot φ G p x) +
        (ε^2 : ℝ)^(1-p/2) * ∫ x in K, D.charge x * φ.hessianNorm x^p) := by
  intro K g
  let δ := ε^2
  let s := fun x => ‖φ.grad x - φ.grad z‖
  let v := fun x => truncatedSpeed p δ (s x)
  let u := fun x => D.charge x^(1/p)
  let b : ℝ := truncationSlope p δ
  let V := ball c R ∩ φ.active
  let scale := δ^(1-p/2)
  let A := (4*p)^p * 4
  let curv := fun x => D.charge x * φ.hessianNorm x^p
  let major := fun x => A * (weightedRoot φ G p x + scale * curv x)
  have hp₀ : 0 < p := by linarith
  have hp₁ : 1 ≤ p := by linarith
  have hδ : 0 < δ := sq_pos_of_pos he
  have hu (x) : 0 ≤ u x := Real.rpow_nonneg (D.charge_nonneg x) _
  have hv (x) : 0 ≤ v x := le_max_left ..
  have hg (x) : 0 ≤ g x := mul_nonneg (hu x) (hv x)
  have hb : 0 ≤ b := NNReal.coe_nonneg _
  have hscale : 0 ≤ scale := Real.rpow_nonneg hδ.le _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlip := truncatedSpeed_lipschitz (by linarith : 2 ≤ p) hδ
  have sc : ContinuousOn s K := (data.continuous_grad.sub continuousOn_const).norm
  have vc : ContinuousOn v K := hlip.continuousOn.comp sc (fun x _ => norm_nonneg _)
  have iu (x) : (u x)^p = D.charge x := by
    dsimp [u]
    rw [← Real.rpow_mul (D.charge_nonneg x), div_mul_cancel₀ _ hp₀.ne', Real.rpow_one]
  have ig : IntegrableOn (fun x => g x^p) K := by
    have ident : (fun x => g x^p) = fun x => D.charge x * (v x)^p := by
      funext x
      change (u x * v x)^p = _
      rw [Real.mul_rpow (hu x) (hv x), iu]
    rw [ident]
    exact data.charge.mul_continuousOn (vc.rpow_const fun _ _ => Or.inr hp₀.le)
      (isCompact_closedBall c R)
  have zeroNear {x : Position} (hx : x ∈ K) (hs : s x = 0) :
      ∀ᶠ y in 𝓝[K] x, v y = 0 := by
    filter_upwards [(sc x hx).eventually_lt_const (by simpa [hs] using he)] with y hy
    apply max_eq_left
    apply sub_nonpos.mpr
    have threshold : ε^(2/p) = δ^(1/p) := by
      dsimp [δ]
      rw [← Real.rpow_natCast, ← Real.rpow_mul he.le]
      congr 1
      push_cast
      ring
    rw [← threshold]
    exact Real.rpow_le_rpow (norm_nonneg _) hy.le (by positivity)
  have sz : s z = 0 := by simp [s]
  have cap {x : Position} (hx : x ∈ K) : s x ≤ 2 * ‖φ.grad x‖ := by
    have h := norm_sub_le (φ.grad x) (φ.grad z)
    change ‖φ.grad x - φ.grad z‖ ≤ _
    linarith only [h, isMinOn_iff.mp minz x hx]
  obtain ⟨Z, hZm, weak, deriv⟩ := rules.product_chain (V := V) (u := u) (v := v) hp hR
    inter_subset_left (by positivity : 0 ≤ 2*p) hb data.root_regular data.grad_Lp data.hessian_Lp
    data.weak_hessian (fun x _ y _ => chargeRoot_lipschitz D hp₁ x y) (fun x _ y _ => by
      have h := hlip.dist_le_mul _ (show s x ∈ Ici (0:ℝ) from norm_nonneg _)
        _ (show s y ∈ Ici (0:ℝ) from norm_nonneg _)
      rw [Real.dist_eq, Real.dist_eq] at h
      apply h.trans (mul_le_mul_of_nonneg_left _ hb)
      exact (abs_norm_sub_norm_le _ _).trans_eq (by rw [sub_sub_sub_cancel_right]))
    (fun x hx out => by
      have hK : x ∈ K := ball_subset_closedBall hx
      have hg₀ : φ.grad x = 0 := Classical.byContradiction fun h => out ⟨hx, h⟩
      apply zeroNear hK
      exact le_antisymm ((cap hK).trans_eq (by rw [hg₀, norm_zero, mul_zero])) (norm_nonneg _))
  have curv₀ (x) : 0 ≤ curv x :=
    mul_nonneg (D.charge_nonneg x) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have majorable : IntegrableOn major K := (data.weighted.add (data.curvature.const_mul scale)).const_mul A
  have bound : ∀ᵐ x ∂volume.restrict K, ‖Z x‖^p ≤ major x := by
    filter_upwards [deriv, ae_restrict_mem (μ := volume) measurableSet_closedBall] with x d hx
    have hG : 0 ≤ matrixGradNorm G x := Real.sqrt_nonneg _
    have hH : 0 ≤ φ.hessianNorm x := Real.sqrt_nonneg _
    have base : 1 ≤ (2*p)^p := Real.one_le_rpow (by linarith) hp₀.le
    have vpow : (v x)^p ≤ 4 * ‖φ.grad x‖^2 := by
      apply (truncation_bounds hp₀ hδ.le (norm_nonneg _)).1.trans
      have h := pow_le_pow_left₀ (norm_nonneg _) (cap hx) 2
      simpa only [mul_pow, show (2 : ℝ)^2 = 4 by norm_num] using h
    change ‖Z x‖^p ≤ (2:ℝ)^p * (((2*p) * |v x| * matrixGradNorm G x)^p +
      (|u x| * b * φ.hessianNorm x)^p) at d
    rw [abs_of_nonneg (hu x), abs_of_nonneg (hv x), Real.mul_rpow (mul_nonneg (by positivity : 0 ≤ 2*p) (hv x)) hG,
      Real.mul_rpow (by positivity : 0 ≤ 2*p) (hv x), Real.mul_rpow (mul_nonneg (hu x) hb) hH,
      Real.mul_rpow (hu x) hb, iu, show b^p = scale from truncationSlope_rpow hp₀ hδ] at d
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left vpow (zero_le_one.trans base)) (Real.rpow_nonneg hG p)
    have h2 := mul_le_mul_of_nonneg_right (show 1 ≤ (2*p)^p*4 by linarith) (mul_nonneg hscale (curv₀ x))
    have hs : (2:ℝ)^p*(2*p)^p = (4*p)^p := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ 2*p), show 2*(2*p)=4*p by ring]
    change _ ≤ (4*p)^p*4*(‖φ.grad x‖^2*(matrixGradNorm G x)^p+scale*curv x)
    rw [← hs]
    apply d.trans
    rw [show D.charge x * scale * φ.hessianNorm x^p = scale * curv x by dsimp [curv]; ring]
    calc
      _ ≤ (2:ℝ)^p * (((2*p)^p*(4*‖φ.grad x‖^2)*(matrixGradNorm G x)^p) +
        (2*p)^p*4*(scale*curv x)) := by
        apply mul_le_mul_of_nonneg_left (add_le_add h1 (by simpa only [one_mul] using h2)) (by positivity)
      _ = _ := by ring
  have iZ : IntegrableOn (fun x => ‖Z x‖^p) K :=
    majorable.mono' (hZm.norm.aemeasurable.pow_const _).aestronglyMeasurable
      (bound.mono fun x h => by simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)] using h)
  have zi := integral_mono_ae iZ majorable bound
  change _ ≤ ∫ x in K, A * (weightedRoot φ G p x + scale * curv x) at zi
  rw [integral_const_mul, integral_add data.weighted (data.curvature.const_mul scale), integral_const_mul] at zi
  have zm := rules.anchored_morrey (f := g) hp hR hz
    ((zeroNear hz sz).mono fun y hy => show u y * v y = 0 by rw [hy, mul_zero]) weak
    (by simpa only [abs_of_nonneg (hg _)] using ig) iZ
  simp only [abs_of_nonneg (hg _)] at zm
  refine ⟨ig, zm.trans ?_⟩
  calc
    _ ≤ C*(3*ℓ)^p*(A*((∫ x in K, weightedRoot φ G p x) + scale*∫ x in K, curv x)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le radius hp₀.le) hC) zi
        (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hℓ.le]; dsimp [localTruncationConstant, A, curv, scale, δ]; ring

end TSGA.ManyBody
