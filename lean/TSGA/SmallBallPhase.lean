import TSGA.PhaseOscillation
import TSGA.PhaseTile
import TSGA.BallActiveMorrey
import TSGA.BallDensityRepresentative

/-! # Phase freezing on a small-oscillation comparison ball

The wavevector is the phase gradient at the center. Its oscillation costs
a Hessian integral weighted by the charge. The minimum squared speed on the
ball multiplies the root-gradient integral, including when that minimum is zero.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory Set Metric TSGA.Localization PhaseLocalization

/-- The phase terms from the two local rotations and the gas modulus. -/
def smallBallPhaseCost (r d ε v : ℝ) (q : Position) : ℝ :=
  r*‖q‖^2*(ε+d+d^2/ε) + r*v^2/ε + (r+r^(4/3:ℝ))*v

private theorem scaled_holder {a B Z L u t : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hub : u ≤ L*B) (htz : t ≤ L*Z) :
    u^(1-a)*t^a ≤ L*(B^(1-a)*Z^a) := by
  have hb := sub_nonneg.mpr ha'
  calc
    _ ≤ (L*B)^(1-a)*(L*Z)^a := mul_le_mul (Real.rpow_le_rpow hu hub hb)
      (Real.rpow_le_rpow ht htz ha) (Real.rpow_nonneg ht _) (Real.rpow_nonneg (mul_nonneg hL hB) _)
    _ = (L^(1-a)*L^a)*(B^(1-a)*Z^a) := by
      rw [Real.mul_rpow hL hB, Real.mul_rpow hL hZ]
      ring
    _ = _ := by rw [← Real.rpow_add_of_nonneg hL hb ha, sub_add_cancel, Real.rpow_one]

private theorem factor_power {w t : ℝ} (hw : 0 ≤ w) (ht : 0 ≤ t) (p a : ℝ) :
    w^(1-a)*(w*t^p)^a = w*t^(p*a) := by
  rw [Real.mul_rpow hw (Real.rpow_nonneg ht _), ← Real.rpow_mul ht, ← mul_assoc,
    ← Real.rpow_add' hw (show 1-a+a ≠ 0 by ring_nf; norm_num), sub_add_cancel, Real.rpow_one]

private theorem fourThirds_factor {r p : ℝ} (hr : 0 ≤ r) (hp : 3 < p) :
    r^(4/3:ℝ) ≤ (r+r^2)^(1-1/p)*r^(1/p) := by
  have hp₀ : 0 < p := by linarith
  have ha : 1/p ≤ 1 := (div_le_one hp₀).2 (by linarith)
  have hsum : 1-1/p+1/p ≠ 0 := by ring_nf; norm_num
  rcases le_total r 1 with h | h
  · calc
      _ ≤ r^(1:ℝ) := Real.rpow_le_rpow_of_exponent_ge' hr h (by norm_num) (by norm_num)
      _ = r^(1-1/p)*r^(1/p) := by rw [← Real.rpow_add' hr hsum, sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hr (le_add_of_nonneg_right (sq_nonneg r)) (sub_nonneg.mpr ha))
        (Real.rpow_nonneg hr _)
  · have hap : 1/p ≤ 1/3 := (div_le_div_iff₀ hp₀ (by norm_num : (0:ℝ)<3)).2 (by linarith)
    calc
      _ ≤ r^(2*(1-1/p)+1/p) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
      _ = (r^2)^(1-1/p)*r^(1/p) := by
        rw [Real.rpow_add (by linarith : 0 < r), Real.rpow_mul hr, Real.rpow_two]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (sq_nonneg r) (le_add_of_nonneg_left hr) (sub_nonneg.mpr ha))
        (Real.rpow_nonneg hr _)

/-- Hölder separates all the phase errors before the two Young inequalities
in `TileInput.bound`. The two derivative inputs are the weighted Morrey
bounds for the speed oscillation and the normalized matrix-root oscillation. -/
private theorem small_phase_products {p ε r m d v L B H : ℝ} {q : Position}
    (hp : 3 < p) (he : 0 < ε) (he' : ε ≤ 1) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hd : 0 ≤ d) (hd' : d ≤ 4) (hv : 0 ≤ v)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (mass : r+r^2 ≤ L*B) (kin : r*m ≤ L*B) (speed : ‖q‖^2 ≤ 2*m+2*v^2)
    (hess : r*v^p ≤ L*(ε^(-p)*H)) (root : (r*m)*d^p ≤ L*(ε^(-p)*H)) :
    smallBallPhaseCost r d ε v q ≤ 50*L*(ε*B+morreyProducts p ε B H) := by
  let Z := ε^(-p)*H
  let U := B^(1-1/p)*Z^(1/p)
  let V := B^(1-2/p)*Z^(2/p)/ε
  have hp₀ : 0 < p := by linarith
  have hZ : 0 ≤ Z := mul_nonneg (Real.rpow_nonneg he.le _) hH
  have hU : 0 ≤ U := mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg hZ _)
  have hV : 0 ≤ V := div_nonneg (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg hZ _)) he.le
  have hb := (le_add_of_nonneg_right (sq_nonneg r)).trans mass
  have one (w t : ℝ) (hw : 0 ≤ w) (ht : 0 ≤ t) (wb : w ≤ L*B) (tz : w*t^p ≤ L*Z) : w*t ≤ L*U := by
    have h := scaled_holder (a := 1/p) (by positivity) ((div_le_one hp₀).2 (by linarith)) hB hZ hL
      hw (mul_nonneg hw (Real.rpow_nonneg ht _)) wb tz
    rwa [factor_power hw ht, mul_div_cancel₀ _ hp₀.ne', Real.rpow_one] at h
  have two (w t : ℝ) (hw : 0 ≤ w) (ht : 0 ≤ t) (wb : w ≤ L*B) (tz : w*t^p ≤ L*Z) : w*t^2/ε ≤ L*V := by
    have h := scaled_holder (a := 2/p) (by positivity) ((div_le_one hp₀).2 (by linarith)) hB hZ hL
      hw (mul_nonneg hw (Real.rpow_nonneg ht _)) wb tz
    rw [factor_power hw ht, mul_div_cancel₀ _ hp₀.ne', Real.rpow_two] at h
    exact (div_le_div_of_nonneg_right h he.le).trans_eq (by dsimp only [V]; ring)
  have t1 := one (r*m) d (mul_nonneg hr hm) hd kin root
  have t2 := two (r*m) d (mul_nonneg hr hm) hd kin root
  have v1 := one r v hr hv hb hess
  have v2 := two r v hr hv hb hess
  have v4 : r^(4/3:ℝ)*v ≤ L*U := by
    have h := scaled_holder (a := 1/p) (by positivity) ((div_le_one hp₀).2 (by linarith)) hB hZ hL
      (add_nonneg hr (sq_nonneg r)) (mul_nonneg hr (Real.rpow_nonneg hv _)) mass hess
    have hpow : (r*v^p)^(1/p) = r^(1/p)*v := by
      rw [Real.mul_rpow hr (Real.rpow_nonneg hv _), ← Real.rpow_mul hv, mul_div_cancel₀ _ hp₀.ne', Real.rpow_one]
    rw [hpow, ← mul_assoc] at h
    exact (mul_le_mul_of_nonneg_right (fourThirds_factor hr hp) hv).trans h
  let W := ε+d+d^2/ε
  have hnW : 0 ≤ W := add_nonneg (add_nonneg he.le hd) (div_nonneg (sq_nonneg d) he.le)
  have cap : W ≤ 21/ε := by
    apply (le_div_iff₀ he).2
    dsimp only [W]
    rw [add_mul, div_mul_cancel₀ _ he.ne', add_mul]
    nlinarith only [mul_le_mul he' he' he.le zero_le_one, mul_le_mul hd' he' he.le (by norm_num : (0:ℝ) ≤ 4),
      pow_le_pow_left₀ hd hd' 2]
  have split := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left speed hr) hnW
  have vcost := mul_le_mul_of_nonneg_left cap (mul_nonneg hr (sq_nonneg v))
  have base := mul_le_mul_of_nonneg_right kin he.le
  change r*‖q‖^2*W + r*v^2/ε + (r+r^(4/3:ℝ))*v ≤ 50*L*(ε*B+(U+V))
  calc
    _ ≤ 2*((r*m)*ε+(r*m)*d+(r*m)*d^2/ε)+2*(r*v^2*(21/ε)) + r*v^2/ε + (r+r^(4/3:ℝ))*v := by
      dsimp only [W] at split vcost ⊢
      ring_nf at split vcost ⊢
      linarith only [split, vcost]
    _ ≤ _ := by
      have b₀ := mul_nonneg (mul_nonneg he.le hB) hL
      have u₀ := mul_nonneg hL hU
      have v₀ := mul_nonneg hL hV
      ring_nf at base t1 t2 v1 v2 v4 b₀ u₀ v₀ ⊢
      linarith only [base,t1,t2,v1,v2,v4,b₀,u₀,v₀]

private theorem const_le_ballAverage {c : Position} {R w : ℝ} (hR : 0 < R)
    {f : Position → ℝ} (hf : Integrable f) (h : ∀ x ∈ ball c R, w ≤ f x) :
    w ≤ ballAverage R f c := by
  have hi : IntegrableOn (fun _ : Position => w) (ball c R) :=
    integrableOn_const (measure_ball_lt_top (μ := volume) (x := c) (r := R)).ne
  have hs := setIntegral_mono_on hi hf.integrableOn measurableSet_ball h
  rw [setIntegral_const, smul_eq_mul, Measure.addHaar_real_ball_center volume c R] at hs
  exact (le_div_iff₀ (ballVolume_pos hR)).2 (by simpa only [ballVolume, ballIntegral, mul_comm w] using hs)

private theorem ballAverage_const_mul (R a : ℝ) (f : Position → ℝ) (c : Position) :
    ballAverage R (fun x => a*f x) c = a * ballAverage R f c := by
  simp only [ballAverage, ballIntegral, integral_const_mul, mul_div_assoc]

private theorem curvature_comparison {D : Density} {φ : Phase} {G : MatrixGradient} {p r R : ℝ}
    (hφ : PhaseAdmissible D p φ G) (hr : 0 ≤ r) (c : Position)
    (comp : ∀ x ∈ closedBall c R, r/2 ≤ D.charge x) :
    r*ballAverage R (fun x => φ.hessianNorm x^p) c ≤ 2*ballAverage R (curvature D φ p) c := by
  rw [← ballAverage_const_mul R r, ← ballAverage_const_mul R 2]
  unfold ballAverage ballIntegral
  apply div_le_div_of_nonneg_right _ (show 0 ≤ ballVolume R from ENNReal.toReal_nonneg)
  apply integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg hr (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
    (hφ.curvature.const_mul 2).integrableOn
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_ball (x := c) (ε := R))] with x hx
  change r*φ.hessianNorm x^p ≤ 2*(D.charge x*φ.hessianNorm x^p)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith only [comp x (ball_subset_closedBall hx)]) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- Uniform coefficient for the two normalized Morrey inequalities. -/
def smallBallPhaseConstant (p Cmat Cvec : ℝ) : ℝ :=
  50 * max 4 (max (ballVolume 1 * (3:ℝ)^p * Cmat) (2*(ballVolume 1 * (3:ℝ)^p * Cvec)))

/-- The phase part of the local error with the actual central wavevector and
the attained matrix-root oscillation. The root-gradient estimate is applied
only if the minimum speed on the closed ball is strictly positive. -/
theorem smallBallPhase_input {p Cmat Cvec ε r d : ℝ}
    (M : MatrixSobolevMorrey p Cmat) (V : VectorMorreyOnBalls p Cvec)
    (hp : 3 < p) (he : 0 < ε) (he' : ε ≤ 1) (_hCmat : 0 ≤ Cmat) (hCvec : 0 ≤ Cvec)
    {N : Density} {φ : Phase} {G : MatrixGradient} (hφ : PhaseAdmissible N p φ G)
    (hroot : Continuous (N.power (1/p)))
    (mass : Integrable (fun x => N.charge x + N.charge x^2 + N.charge x*‖φ.grad x‖^2))
    (c : Position) (hr : 0 ≤ r) (hd : 0 ≤ d) (hd' : d ≤ 4)
    (comp : ∀ x ∈ closedBall c (3*ε⁻¹), r/2 ≤ N.charge x)
    (pair : ∃ x ∈ closedBall c (3*ε⁻¹), ∃ y ∈ closedBall c (3*ε⁻¹),
      r^(1/p)*d = hilbertSchmidt (N.power (1/p) x - N.power (1/p) y)) :
    PhaseLocalization.TileInput N φ G p ε (smallBallPhaseConstant p Cmat Cvec) (3*ε⁻¹) c
      (smallBallPhaseCost r d ε (tilePhaseOscillation φ c ε⁻¹) (φ.grad c)) := by
  let R := 3*ε⁻¹
  let Ω := closedBall c R
  let B := bulkAverage N φ R c
  let v := tilePhaseOscillation φ c ε⁻¹
  let H := ballAverage R (curvature N φ p) c
  let J := ballAverage R (rootPower G p) c
  let C := fun t : ℝ => ballVolume 1*(3:ℝ)^p*t
  let L := max 4 (max (C Cmat) (2*C Cvec))
  have hR : 0 < R := mul_pos (by norm_num) (inv_pos.mpr he)
  have compact : IsCompact Ω := isCompact_closedBall c R
  obtain ⟨z, hz, hmin⟩ := compact.exists_isMinOn ⟨c, mem_closedBall_self hR.le⟩
    (hφ.regular.continuous_grad.norm.pow 2).continuousOn
  let m := ‖φ.grad z‖^2
  have hm : 0 ≤ m := sq_nonneg _
  have minimum (x : Position) (hx : x ∈ Ω) : m ≤ ‖φ.grad x‖^2 := hmin hx
  obtain ⟨a, ha, haeq, cap⟩ := tilePhaseOscillation_attained hφ.regular c (inv_pos.mpr he)
  have hv : 0 ≤ v := haeq.ge.trans' (norm_nonneg _)
  have speed₀ := norm_sub_norm_le (φ.grad c) (φ.grad z)
  rw [norm_sub_rev] at speed₀
  have speed : ‖φ.grad c‖^2 ≤ 2*m+2*v^2 := by
    calc
      _ ≤ (‖φ.grad z‖+v)^2 := pow_le_pow_left₀ (norm_nonneg _) (by linarith only [speed₀, cap z hz]) _
      _ ≤ _ := by dsimp only [m]; nlinarith only [sq_nonneg (‖φ.grad z‖-v)]
  have hp₀ : 0 < p := by linarith
  have active (h : m ≠ 0) : Ω ⊆ φ.active := by
    intro x hx
    change φ.grad x ≠ 0
    intro hx'
    have := minimum x hx
    rw [hx',norm_zero,zero_pow (by decide : 2 ≠ 0)] at this
    exact h (le_antisymm this hm)
  have reg (h : m ≠ 0) := rootPower_integrableOn_compact hp₀ hφ.root_regular compact (active h)
  have hreg : m = 0 ∨ IntegrableOn (rootPower G p) (ball c R) := by
    by_cases h : m = 0
    · exact Or.inl h
    · exact Or.inr ((reg h).mono_set ball_subset_closedBall)
  refine .small m hm (fun x hx => minimum x (ball_subset_closedBall hx)) hreg ?_
  have hH : 0 ≤ H := div_nonneg (integral_nonneg (fun x => mul_nonneg (N.charge_nonneg x)
    (Real.rpow_nonneg (Real.sqrt_nonneg _) _))) ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := div_nonneg (integral_nonneg (rootPower_nonneg G p)) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := div_nonneg (integral_nonneg (fun x => add_nonneg
    (add_nonneg (N.charge_nonneg x) (sq_nonneg _)) (mul_nonneg (N.charge_nonneg x) (sq_nonneg _)))) ENNReal.toReal_nonneg
  have hL4 : 4 ≤ L := le_max_left ..
  have hLM : C Cmat ≤ L := (le_max_left ..).trans (le_max_right ..)
  have hLV : 2*C Cvec ≤ L := (le_max_right ..).trans (le_max_right ..)
  have Cpos {t : ℝ} (ht : 0 ≤ t) : 0 ≤ C t :=
    mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) ht
  have hZ := mul_nonneg (Real.rpow_nonneg he.le (-p)) (add_nonneg hH (mul_nonneg hm hJ))
  have mass4 : r+r^2 ≤ 4*B := by
    rw [show 4*B = ballAverage R (fun x => 4*(N.charge x+N.charge x^2+N.charge x*‖φ.grad x‖^2)) c
      from (ballAverage_const_mul ..).symm]
    apply const_le_ballAverage hR (mass.const_mul 4)
    intro x hx
    have hρ := N.charge_nonneg x
    have compare : r ≤ 2*N.charge x := by linarith only [comp x (ball_subset_closedBall hx)]
    nlinarith only [compare, hρ, pow_le_pow_left₀ hr compare 2, mul_nonneg hρ (sq_nonneg ‖φ.grad x‖)]
  have kin4 : r*m ≤ 4*B := by
    rw [show 4*B = ballAverage R (fun x => 4*(N.charge x+N.charge x^2+N.charge x*‖φ.grad x‖^2)) c
      from (ballAverage_const_mul ..).symm]
    apply const_le_ballAverage hR (mass.const_mul 4)
    intro x hx
    have hρ := N.charge_nonneg x
    have compare : r ≤ 2*N.charge x := by linarith only [comp x (ball_subset_closedBall hx)]
    have hk := mul_le_mul compare (minimum x (ball_subset_closedBall hx)) hm (by positivity)
    nlinarith only [hk, hρ, sq_nonneg (N.charge x), mul_nonneg hρ (sq_nonneg ‖φ.grad x‖)]
  have hvRaw := V hp φ.grad φ.hessian hφ.regular.continuous_grad hφ.regular.grad_Lp hφ.regular.hessian_Lp
    hφ.regular.weak_hessian c R hR a ha c (mem_closedBall_self hR.le)
  rw [← haeq] at hvRaw
  have hvNorm : v^p ≤ ε^(-p)*(C Cvec*ballAverage R (fun x => φ.hessianNorm x^p) c) :=
    tile_ball_morrey_average he c (tile_ball_morrey_scale he c hvRaw)
  have hess : r*v^p ≤ L*(ε^(-p)*(H+m*J)) := by
    calc
      _ ≤ r*(ε^(-p)*(C Cvec*ballAverage R (fun x => φ.hessianNorm x^p) c)) := mul_le_mul_of_nonneg_left hvNorm hr
      _ = (C Cvec*ε^(-p))*(r*ballAverage R (fun x => φ.hessianNorm x^p) c) := by ring
      _ ≤ (C Cvec*ε^(-p))*(2*H) := mul_le_mul_of_nonneg_left (curvature_comparison hφ hr c comp)
        (mul_nonneg (Cpos hCvec) (Real.rpow_nonneg he.le _))
      _ = (2*C Cvec)*(ε^(-p)*H) := by ring
      _ ≤ L*(ε^(-p)*(H+m*J)) := mul_le_mul hLV (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hm hJ)) (Real.rpow_nonneg he.le _))
        (mul_nonneg (Real.rpow_nonneg he.le _) hH) (by linarith only [hL4])
  have root : (r*m)*d^p ≤ L*(ε^(-p)*(H+m*J)) := by
    by_cases hz : m = 0
    · rw [hz, mul_zero, zero_mul]
      exact mul_nonneg (by linarith only [hL4]) (by simpa only [hz] using hZ)
    obtain ⟨x,hx,y,hy,hxy⟩ := pair
    have h := tile_ball_morrey_average he c (tile_ball_morrey_scale he c
      (M.root_pair hp hφ.regular.isOpen_active hφ.root_regular hroot hR (active hz) x hx y hy))
    rw [← hxy, Real.mul_rpow (Real.rpow_nonneg hr _) hd, ← Real.rpow_mul hr,
      div_mul_cancel₀ _ hp₀.ne', Real.rpow_one] at h
    calc
      _ = m*(r*d^p) := by ring
      _ ≤ m*(ε^(-p)*(C Cmat*J)) := mul_le_mul_of_nonneg_left h hm
      _ = (C Cmat)*(ε^(-p)*(m*J)) := by ring
      _ ≤ L*(ε^(-p)*(H+m*J)) := mul_le_mul hLM (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left hH) (Real.rpow_nonneg he.le _)) (mul_nonneg (Real.rpow_nonneg he.le _) (mul_nonneg hm hJ))
        (by linarith only [hL4])
  exact small_phase_products hp he he' hr hm hd hd' hv (by linarith only [hL4]) hB
    (add_nonneg hH (mul_nonneg hm hJ)) (mass4.trans (mul_le_mul_of_nonneg_right hL4 hB))
    (kin4.trans (mul_le_mul_of_nonneg_right hL4 hB)) speed hess root

/-- The wavevector contribution in each physical gas modulus is bounded by
the same phase cost as the finite tile rotation. -/
theorem wavevectorModulus_le_smallBallPhaseCost {r t d ε v : ℝ} {q k : Position}
    (ht : 0 ≤ t) (cap : t ≤ r) (hd : 0 ≤ d) (he : 0 < ε) (he' : ε ≤ 1)
    (osc : ‖k-q‖ ≤ v) :
    (t^(7/6:ℝ)+t^(4/3:ℝ)+t*max ‖q‖ ‖k‖)*‖q-k‖ ≤ 2*smallBallPhaseCost r d ε v q := by
  have hr := ht.trans cap
  have hv := (norm_nonneg _).trans osc
  have hq := norm_nonneg q
  have hp : r^(7/6:ℝ) ≤ r+r^(4/3:ℝ) := by
    rcases le_total r 1 with h|h
    · exact (Real.rpow_le_self_of_le_one hr h (by norm_num)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hr _))
    · exact (Real.rpow_le_rpow_of_exponent_le h (by norm_num : (7/6:ℝ) ≤ 4/3)).trans (le_add_of_nonneg_left hr)
  have hk : max ‖q‖ ‖k‖ ≤ ‖q‖+v :=
    max_le (le_add_of_nonneg_right hv) (by linarith only [norm_sub_norm_le k q, osc])
  have h₁ := (Real.rpow_le_rpow ht cap (by norm_num : (0:ℝ) ≤ 7/6)).trans hp
  have h₂ := Real.rpow_le_rpow ht cap (by norm_num : (0:ℝ) ≤ 4/3)
  have h₃ := mul_le_mul cap hk (le_max_of_le_left hq) hr
  have h₄ := mul_le_mul_of_nonneg_right (add_le_add (add_le_add h₁ h₂) h₃) hv
  rw [norm_sub_rev q k]
  apply (mul_le_mul_of_nonneg_left osc (add_nonneg (add_nonneg (Real.rpow_nonneg ht _) (Real.rpow_nonneg ht _))
    (mul_nonneg ht (le_max_of_le_left hq)))).trans (h₄.trans ?_)
  have young : ‖q‖*v ≤ ε*‖q‖^2+v^2/ε := by
    rw [← sub_le_iff_le_add' , le_div_iff₀ he]
    nlinarith only [sq_nonneg (ε*‖q‖-v),sq_nonneg (ε*‖q‖),sq_nonneg v]
  have sq : v^2 ≤ v^2/ε := (le_div_iff₀ he).2 (mul_le_of_le_one_right (sq_nonneg v) he')
  have inflate := mul_le_mul_of_nonneg_left (show ε ≤ ε+d+d^2/ε by
    linarith only [hd,div_nonneg (sq_nonneg d) he.le]) (mul_nonneg hr (sq_nonneg ‖q‖))
  unfold smallBallPhaseCost
  have hy := mul_le_mul_of_nonneg_left young hr
  have hs := mul_le_mul_of_nonneg_left sq hr
  have hb := mul_nonneg hr hv
  have hq₀ := mul_nonneg (mul_nonneg hr (sq_nonneg ‖q‖)) he.le
  simp only [div_eq_mul_inv] at inflate hy hs ⊢
  linarith only [inflate,hy,hs,hb,hq₀]

end TSGA.ManyBody
