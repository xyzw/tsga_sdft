import TSGA.BallTruncatedGradient
import TSGA.BallDensityRepresentative
import TSGA.LocalWavevectorTruncation

/-! # Freezing the wavevector at a minimum on a ball (Lemma 4.18) -/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Metric Set TSGA.Localization PhaseLocalization

/-- Half the residual speed, extended off the ball so it vanishes at zero
velocity and remains 1-Lipschitz. -/
private def residualSpeed (q v : Position) : ℝ := min (dist v q / 2) ‖v‖

private theorem residualSpeed_lipschitz (q : Position) : LipschitzWith 1 (residualSpeed q) := by
  have half : LipschitzWith 1 (fun v : Position => dist v q / 2) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := dist_dist_dist_le_left x y q
    rw [Real.dist_eq] at h
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    simpa only [NNReal.coe_one, one_mul] using (show |dist x q - dist y q| / 2 ≤ dist x y by
      linarith [dist_nonneg (x := x) (y := y)])
  unfold residualSpeed
  simpa only [sup_idem] using half.min (lipschitzWith_one_norm (E := Position))

private theorem residualSpeed_eq {v q : Position} (h : ‖q‖ ≤ ‖v‖) :
    residualSpeed q v = ‖v-q‖ / 2 := by
  rw [residualSpeed, dist_eq_norm, min_eq_left]
  linarith [norm_sub_le v q]

/-- Volume-normalized Morrey at an arbitrary radius at most three tile lengths. -/
private theorem morrey_volume_bound {R ℓ p C d J : ℝ} {c : Position}
    (hR : 0 < R) (hℓ : 0 < ℓ) (radius : R ≤ 3*ℓ) (hp : 0 < p)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (bound : d ≤ C * R^(p-3) * J) :
    volume.real (closedBall c R) * d ≤
      (volume.real (ball (0 : Position) 1) * C * (3:ℝ)^p) * ℓ^p * J := by
  have hvol := mul_le_mul_of_nonneg_left bound (show 0 ≤ volume.real (closedBall c R) from ENNReal.toReal_nonneg)
  apply hvol.trans
  rw [Measure.addHaar_real_closedBall volume c hR.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  have hs : R^(3 : ℕ) * R^(p-3) = R^p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  calc
    _ = (volume.real (ball (0 : Position) 1) * C) * (R^(3 : ℕ) * R^(p-3)) * J := by ring
    _ ≤ (volume.real (ball (0 : Position) 1) * C) * ((3*ℓ)^p) * J := by
      rw [hs]
      gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hℓ.le]; ring

/-- Integrate the scalar truncation inequality against a taper, then divide by ε.
Only the mass term retains the taper. -/
private theorem freezing_from_truncation {p ε ℓ B U H : ℝ} {K : Set Position}
    {D : Density} {ξ s d : Position → ℝ} (hp₀ : 0 < p) (he : 0 < ε) (hℓ : 0 < ℓ)
    (hB : 0 ≤ B) (hU : 0 ≤ U) (hH : 0 ≤ H) (hK : MeasurableSet K)
    (range : ∀ x ∈ K, ξ x ∈ Icc 0 1) (hmass : IntegrableOn (fun x => D.charge x * ξ x) K)
    (hs : ∀ x ∈ K, 0 ≤ s x) (hd : ∀ x ∈ K, 0 ≤ d x) (cap : ∀ x ∈ K, d x ≤ 2*s x)
    (ig : IntegrableOn (fun x => (D.charge x^(1/p) * truncatedSpeed p (ε^2) (s x))^p) K)
    (hpeak : (∫ x in K, (D.charge x^(1/p) * truncatedSpeed p (ε^2) (s x))^p) ≤
      B * ℓ^p * (U + (ε^2)^(1-p/2)*H)) :
    (∫ x in K, (D.charge x * ξ x) * (d x)^2) / ε ≤
      (4*(2:ℝ)^p)*(1+B) * (ε * (∫ x in K, D.charge x * ξ x) + ℓ^p/ε*U + ℓ^p/ε^(p-1)*H) := by
  let A := 4 * (2 : ℝ)^p
  have hA : 0 < A := by dsimp [A]; positivity
  let δ := ε^2
  have hδ : 0 < δ := sq_pos_of_pos he
  let g := fun x => D.charge x^(1/p) * truncatedSpeed p δ (s x)
  have hg (x) : 0 ≤ g x := mul_nonneg (Real.rpow_nonneg (D.charge_nonneg x) _) (le_max_left ..)
  let m := ∫ x in K, D.charge x * ξ x
  have hm : 0 ≤ m := setIntegral_nonneg hK fun x hx =>
    mul_nonneg (D.charge_nonneg x) (range x hx).1
  have point (x : Position) (hx : x ∈ K) :
      (D.charge x * ξ x) * (d x)^2 ≤ A * (δ * (D.charge x * ξ x) + g x^p) := by
    have ht := (truncation_bounds hp₀ hδ.le (hs x hx)).2
    have heq : (d x)^2 ≤ 4 * (s x)^2 := by
      have := pow_le_pow_left₀ (hd x hx) (cap x hx) 2
      linarith only [this]
    have hpwr : g x^p = D.charge x * truncatedSpeed p δ (s x)^p := by
      dsimp only [g]
      rw [Real.mul_rpow (Real.rpow_nonneg (D.charge_nonneg x) _)
          (show 0 ≤ truncatedSpeed p δ (s x) from le_max_left ..),
        ← Real.rpow_mul (D.charge_nonneg x), div_mul_cancel₀ _ hp₀.ne', Real.rpow_one]
    have capped : g x^p * ξ x ≤ g x^p :=
      mul_le_of_le_one_right (Real.rpow_nonneg (hg x) _) (range x hx).2
    calc
      _ ≤ (D.charge x * ξ x) * (4*((2:ℝ)^p*(δ + truncatedSpeed p δ (s x)^p))) :=
        mul_le_mul_of_nonneg_left
          (heq.trans (mul_le_mul_of_nonneg_left ht (by norm_num)))
          (mul_nonneg (D.charge_nonneg x) (range x hx).1)
      _ = A * (δ*(D.charge x*ξ x) + g x^p*ξ x) := by rw [hpwr]; dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl capped) hA.le
  have i := integral_mono_of_nonneg (μ := volume.restrict K)
    ((ae_restrict_mem hK).mono (fun x hx =>
      mul_nonneg (mul_nonneg (D.charge_nonneg x) (range x hx).1) (sq_nonneg _)))
    (((hmass.const_mul δ).add ig).const_mul A)
    ((ae_restrict_mem hK).mono point)
  change (∫ x in K, (D.charge x * ξ x) * (d x)^2) ≤
    ∫ x in K, A * (δ * (D.charge x * ξ x) + g x^p) at i
  rw [integral_const_mul, integral_add (hmass.const_mul δ) ig, integral_const_mul] at i
  have comb := i.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (δ*m)) hpeak) hA.le)
  change _ ≤ A*(δ*m + B*ℓ^p*(U+δ^(1-p/2)*H)) at comb
  have power : δ^(1-p/2) = ε / ε^(p-1) := by
    dsimp [δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul he.le,
      show ε / ε^(p-1) = ε^(1:ℝ) / ε^(p-1) by rw [Real.rpow_one], ← Real.rpow_sub he]
    congr 1
    push_cast
    ring
  rw [power] at comb
  apply (div_le_iff₀ he).2
  apply comb.trans
  change A * (ε^2*m + B * ℓ^p * (U + ε/ε^(p-1)*H)) ≤
    A*(1+B)*(ε*m + ℓ^p/ε*U + ℓ^p/ε^(p-1)*H)*ε
  have hd : 0 < ε^(p-1) := Real.rpow_pos_of_pos he _
  field_simp
  linarith only [mul_nonneg (mul_nonneg (mul_nonneg hB (sq_nonneg ε)) hm) hd.le,
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hℓ.le p) hU) hd.le,
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hℓ.le p) hH) he.le]

/-- One minimum-speed wavevector for every taper on a fixed ball.
The weighted root integrand vanishes off the active set. -/
def WeightedWavevectorBound (D : Density) (φ : Phase) (G : MatrixGradient)
    (p C : ℝ) (c : Position) (R ℓ : ℝ) : Prop :=
  ∃ z ∈ closedBall c R, IsMinOn (fun x => ‖φ.grad x‖) (closedBall c R) z ∧
    ∀ (ξ : Position → ℝ), AEMeasurable ξ (volume.restrict (closedBall c R)) →
      (∀ x ∈ closedBall c R, ξ x ∈ Icc 0 1) → ∀ ε > 0, ε ≤ 1 →
      (∫ x in closedBall c R, (D.charge x * ξ x) * ‖φ.grad x - φ.grad z‖^2) / ε ≤
        C * (ε * (∫ x in closedBall c R, D.charge x * ξ x) +
          ℓ^p / ε * (∫ x in closedBall c R, weightedRoot φ G p x) +
          ℓ^p / ε^(p-1) * ∫ x in closedBall c R, D.charge x * φ.hessianNorm x^p)

/-- Lemma 4.18 on the finite-error domain, with Sobolev hypotheses local
to the given ball. The coefficient depends only on p and its Morrey constant. -/
theorem weighted_wavevector_on_ball {p Cₘ : ℝ} (hp : 3 < p) (hC : 0 ≤ Cₘ)
    (rules : BallTruncationRules p Cₘ) :
    ∃ C > 0, ∀ {D : Density} {φ : Phase} {G : MatrixGradient} {c : Position} {R ℓ : ℝ},
      0 ≤ R → 0 < ℓ → R ≤ 3*ℓ → LocalWavevectorData D φ G p c R →
      WeightedWavevectorBound D φ G p C c R ℓ := by
  let B := localTruncationConstant p Cₘ
  have hp₀ : 0 < p := by linarith
  have hB : 0 ≤ B := by dsimp [B, localTruncationConstant]; positivity
  refine ⟨4*(2:ℝ)^p*(1+B), by positivity, ?_⟩
  intro D φ G c R ℓ hR₀ hℓ radius data
  let K := closedBall c R
  obtain ⟨z,hz,minz⟩ := (isCompact_closedBall c R).exists_isMinOn
    ⟨c, mem_closedBall_self hR₀⟩ data.continuous_grad.norm
  refine ⟨z,hz,minz,?_⟩
  intro ξ hξ range ε he _
  rcases hR₀.eq_or_lt with hR | hR
  · subst R
    simp
  obtain ⟨ig, bound⟩ := local_wavevector_truncation hp hC rules hR hℓ radius he data hz minz
  have mass : IntegrableOn (fun x => D.charge x * ξ x) K := by
    apply data.charge.mono' (data.charge.aestronglyMeasurable.mul hξ.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (μ := volume) (s := K) measurableSet_closedBall] with x hx
    change ‖D.charge x * ξ x‖ ≤ D.charge x
    rw [Real.norm_of_nonneg (mul_nonneg (D.charge_nonneg x) (range x hx).1)]
    exact mul_le_of_le_one_right (D.charge_nonneg x) (range x hx).2
  apply freezing_from_truncation (s := fun x => ‖φ.grad x - φ.grad z‖) hp₀ he hℓ hB
    (integral_nonneg (weightedRoot_nonneg φ G p)) (integral_nonneg fun x =>
      mul_nonneg (D.charge_nonneg x) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
    measurableSet_closedBall range mass (fun x _ => norm_nonneg _) (fun x _ => norm_nonneg _)
    (fun x _ => by linarith [norm_nonneg (φ.grad x - φ.grad z)]) ig bound

/-- The tapered freezing error on the continuous density representative used
in the TSGA proof. A single minimizing point works for every taper and ε. -/
theorem weighted_wavevector_of_global_fields {p Cₘ : ℝ} (hp : 3 < p) (hC : 0 ≤ Cₘ)
    (morrey : MatrixSobolevMorrey p Cₘ) (calculus : TruncationSobolevCalculus) :
    ∃ C > 0, ∀ {D : Density} {φ : Phase} {G : MatrixGradient},
      PhaseAdmissible D p φ G → Continuous D.charge →
      ∀ (c : Position) {R ℓ : ℝ}, 0 ≤ R → 0 < ℓ → R ≤ 3*ℓ →
      WeightedWavevectorBound D φ G p C c R ℓ := by
  let A := 4 * (2 : ℝ)^p
  let B := volume.real (ball (0 : Position) 1) * Cₘ * (3:ℝ)^p * (4*p)^p
  have hp₀ : 0 < p := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A*(1+B), mul_pos hA (by linarith), ?_⟩
  intro D φ G phase hc c R ℓ hR₀ hℓ radius
  let K := closedBall c R
  have comp : IsCompact K := isCompact_closedBall c R
  obtain ⟨z, hz, minz⟩ := comp.exists_isMinOn ⟨c, mem_closedBall_self hR₀⟩
    phase.regular.continuous_grad.norm.continuousOn
  refine ⟨z, hz, minz, ?_⟩
  intro ξ hξ range ε he _
  rcases hR₀.eq_or_lt with hR | hR
  · subst R
    simp
  let q := φ.grad z
  let s := residualSpeed q
  have hs (v : Position) : s v ∈ Icc 0 ‖v‖ :=
    ⟨le_min (div_nonneg dist_nonneg (by norm_num)) (norm_nonneg _), min_le_right ..⟩
  let δ := ε^2
  have hδ : 0 < δ := sq_pos_of_pos he
  let g := fun x => D.charge x^(1/p) * truncatedSpeed p δ (s (φ.grad x))
  have hg (x) : 0 ≤ g x := mul_nonneg (Real.rpow_nonneg (D.charge_nonneg x) _) (le_max_left ..)
  have gs : Continuous g := (hc.rpow_const (fun _ => Or.inr (by positivity))).mul
    ((truncatedSpeed_lipschitz (by linarith : 2 ≤ p) hδ).continuousOn.comp_continuous
      ((residualSpeed_lipschitz q).continuous.comp phase.regular.continuous_grad)
      (fun x => (hs _).1))
  have gz : g z = 0 := by
    simp [g, s, q, residualSpeed, truncatedSpeed,
      Real.zero_rpow (by positivity : 2/p ≠ 0), max_eq_left (neg_nonpos.mpr (Real.rpow_nonneg hδ.le _))]
  obtain ⟨y, hy, peak⟩ := comp.exists_isMaxOn ⟨z,hz⟩ gs.continuousOn
  obtain ⟨Z, weak, lp, cost⟩ := truncatedSpeedProduct_gradient calculus hp hδ phase hc s
    (residualSpeed_lipschitz q) hs
  have osc := morrey.scalar_pair hp g Z gs c R hR (weak _ isOpen_ball) (lp.restrict _) y hy z hz
  rw [gz, sub_zero, abs_of_nonneg (hg y)] at osc
  let H := ∫ x in K, D.charge x * φ.hessianNorm x^p
  let U := ∫ x in K, weightedRoot φ G p x
  have hH : 0 ≤ H := integral_nonneg fun x => mul_nonneg (D.charge_nonneg x)
    (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hU : 0 ≤ U := integral_nonneg (weightedRoot_nonneg φ G p)
  have hpeak : volume.real K * g y^p ≤ B * ℓ^p * (U + δ^(1-p/2)*H) := by
    have h := morrey_volume_bound (c := c) hR hℓ radius hp₀ hC
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg (Z x)) p) osc
    apply h.trans
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (cost K) (by positivity)
      _ = _ := by dsimp [B,H,U,K]; ring
  have hmass : IntegrableOn (fun x => D.charge x * ξ x) K := by
    apply (hc.continuousOn.integrableOn_compact comp).mono' (hc.aestronglyMeasurable.mul hξ.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (μ := volume) comp.measurableSet] with x hx
    change ‖D.charge x * ξ x‖ ≤ D.charge x
    rw [Real.norm_of_nonneg (mul_nonneg (D.charge_nonneg x) (range x hx).1)]
    exact mul_le_of_le_one_right (D.charge_nonneg x) (range x hx).2
  have hconst : IntegrableOn (fun _ : Position => g y^p) K := integrableOn_const comp.measure_lt_top.ne
  have ig := (gs.rpow_const (fun _ => Or.inr hp₀.le)).continuousOn.integrableOn_compact (μ := volume) comp
  have total : (∫ x in K, g x^p) ≤ B * ℓ^p * (U + δ^(1-p/2)*H) := by
    have hi := setIntegral_mono_on ig hconst comp.measurableSet
      (fun x hx => Real.rpow_le_rpow (hg x) (peak hx) hp₀.le)
    rw [setIntegral_const, smul_eq_mul] at hi
    exact hi.trans hpeak
  exact freezing_from_truncation hp₀ he hℓ hB hU hH comp.measurableSet range hmass
    (s := fun x => s (φ.grad x)) (fun x _ => (hs _).1) (fun x _ => norm_nonneg _)
    (fun x hx => by rw [show s (φ.grad x) = _ from residualSpeed_eq (minz hx)]; linarith)
    ig total

end TSGA.ManyBody
