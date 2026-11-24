import TSGA.LocalEstimate
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Phase-weighted relative gradients in the proof of Theorem 3.3

The cutoff in wavevector space is needed on a ball where the density has large
oscillation. It lets the matrix root enter only where the phase gradient is
nonzero. The local analytic inputs below are the product rule, Morrey's
inequality, and the large density oscillation estimate on a ball contained in
the active set.
-/

noncomputable section

namespace TSGA.PhaseLocalization

open MeasureTheory Set

def rootPower (G : MatrixGradient) (p : ℝ) (x : Position) : ℝ := matrixGradNorm G x ^ p

def weightedRoot (φ : Phase) (G : MatrixGradient) (p : ℝ) (x : Position) : ℝ :=
  ‖φ.grad x‖ ^ 2 * rootPower G p x

theorem rootPower_nonneg (G : MatrixGradient) (p : ℝ) (x : Position) : 0 ≤ rootPower G p x :=
  Real.rpow_nonneg (Real.sqrt_nonneg _) _

theorem weightedRoot_nonneg (φ : Phase) (G : MatrixGradient) (p : ℝ) (x : Position) :
    0 ≤ weightedRoot φ G p x := mul_nonneg (sq_nonneg _) (rootPower_nonneg ..)

theorem weightedRoot_off_active (φ : Phase) (G : MatrixGradient) (p : ℝ) {x : Position}
    (hx : x ∉ φ.active) : weightedRoot φ G p x = 0 := by
  classical
  have hz : φ.grad x = 0 := not_not.mp hx
  simp [weightedRoot, hz]

theorem integral_weightedRoot_active (φ : Phase) (G : MatrixGradient) (p : ℝ) :
    (∫ x, weightedRoot φ G p x) = ∫ x in φ.active, ‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero (f := weightedRoot φ G p)
    (fun _ hx => weightedRoot_off_active φ G p hx)).symm

theorem integrable_weightedRoot {D : Density} {φ : Phase} {G : MatrixGradient} {p : ℝ}
    (h : PhaseAdmissible D p φ G) : Integrable (weightedRoot φ G p) := by
  have hi := (integrable_indicator_iff (f := weightedRoot φ G p)
    h.regular.isOpen_active.measurableSet).mpr h.root_weighted
  have heq : φ.active.indicator (weightedRoot φ G p) = weightedRoot φ G p := by
    classical
    funext x
    by_cases hx : x ∈ φ.active
    · simp [hx]
    · simp [hx, weightedRoot_off_active φ G p hx]
  rwa [heq] at hi

/-- Push a lower bound on the squared wavevector into the local Morrey integral. -/
theorem minimum_mul_rootPower_le {D : Density} {φ : Phase} {G : MatrixGradient} {p : ℝ}
    (h : PhaseAdmissible D p φ G) {K : Set Position} (hK : MeasurableSet K) {m : ℝ}
    (hm : ∀ x ∈ K, m ≤ ‖φ.grad x‖ ^ 2) (hG : IntegrableOn (rootPower G p) K) :
    m * (∫ x in K, rootPower G p x) ≤ ∫ x in K, weightedRoot φ G p x := by
  rw [← integral_const_mul]
  exact setIntegral_mono_on (hG.const_mul _) (integrable_weightedRoot h).integrableOn hK
    (fun x hx => mul_le_mul_of_nonneg_right (hm x hx) (rootPower_nonneg ..))

/-- Positive part of the wavevector modulus used in the last large-oscillation argument. -/
def truncatedSpeed (p ε t : ℝ) : ℝ := max 0 (t ^ (2 / p) - ε ^ (1 / p))

private theorem speed_pow {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    (t ^ (2 / p)) ^ p = t ^ (2 : ℕ) := by
  rw [← Real.rpow_mul ht, div_mul_cancel₀ _ hp.ne', Real.rpow_two]

private theorem root_pow {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    (t ^ (1 / p)) ^ p = t := by rw [← Real.rpow_mul ht, div_mul_cancel₀ _ hp.ne', Real.rpow_one]

theorem truncation_bounds {p ε t : ℝ} (hp : 0 < p) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    (truncatedSpeed p ε t) ^ p ≤ t ^ (2 : ℕ) ∧
    t ^ (2 : ℕ) ≤ (2 : ℝ) ^ p * (ε + (truncatedSpeed p ε t) ^ p) := by
  let h := truncatedSpeed p ε t
  let a := ε ^ (1 / p)
  have ha : 0 ≤ a := Real.rpow_nonneg hε _
  have hh : 0 ≤ h := le_max_left ..
  have hh' : t ^ (2 / p) - a ≤ h := le_max_right ..
  have ht' := Real.rpow_nonneg ht (2 / p)
  refine ⟨?_, ?_⟩
  · rw [← speed_pow hp ht]
    exact Real.rpow_le_rpow hh (max_le ht' (by linarith)) hp.le
  · have htwo : t ^ (2 / p) ≤ 2 * max a h := by
      linarith [le_max_left a h, le_max_right a h]
    have hm : 0 ≤ max a h := ha.trans (le_max_left ..)
    have hpow := Real.rpow_le_rpow ht' htwo hp.le
    rw [speed_pow hp ht, Real.mul_rpow (by norm_num) hm] at hpow
    apply hpow.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) p)
    rcases le_total a h with he | he
    · rw [max_eq_right he]
      linarith
    · rw [max_eq_left he, show a ^ p = ε from root_pow hp hε]
      linarith [Real.rpow_nonneg hh p]

def truncatedDensity (D : Density) (φ : Phase) (p ε : ℝ) (x : Position) : ℝ :=
  D.charge x ^ (1 / p) * truncatedSpeed p ε ‖φ.grad x‖

theorem truncatedDensity_nonneg (D : Density) (φ : Phase) (p ε : ℝ) (x : Position) :
    0 ≤ truncatedDensity D φ p ε x :=
  mul_nonneg (Real.rpow_nonneg (D.charge_nonneg _) _) (le_max_left ..)

theorem truncatedDensity_pow (D : Density) (φ : Phase) {p : ℝ} (hp : 0 < p) (ε : ℝ)
    (x : Position) :
    truncatedDensity D φ p ε x ^ p = D.charge x * truncatedSpeed p ε ‖φ.grad x‖ ^ p := by
  have hh : 0 ≤ truncatedSpeed p ε ‖φ.grad x‖ := le_max_left ..
  rw [truncatedDensity, Real.mul_rpow (Real.rpow_nonneg (D.charge_nonneg _) _) hh,
    root_pow hp (D.charge_nonneg _)]

private theorem truncatedDensity_off_active (D : Density) (φ : Phase) {p ε : ℝ}
    (hp : 0 < p) (hε : 0 ≤ ε) {x : Position} (hx : x ∉ φ.active) :
    truncatedDensity D φ p ε x = 0 := by
  have hz : φ.grad x = 0 := not_not.mp hx
  have ht : 0 < (2 : ℝ) / p := div_pos (by norm_num) hp
  rw [truncatedDensity, truncatedSpeed, hz, norm_zero, Real.zero_rpow ht.ne', zero_sub,
    max_eq_left (neg_nonpos.mpr (Real.rpow_nonneg hε _)), mul_zero]

/-- Powers of the localization length and of the Lipschitz constant of the
truncation are absorbed by the exponent `2p−1`. -/
theorem phaseScale_bounds {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hε' : ε ≤ 1) :
    ε ^ (-p) ≤ 1 / ε ^ (2 * p - 1) ∧
    ε ^ (-p) * ε ^ (1 - p / 2) ≤ 1 / ε ^ (2 * p - 1) := by
  rw [one_div, ← Real.rpow_neg hε.le, ← Real.rpow_add hε]
  constructor <;> apply Real.rpow_le_rpow_of_exponent_ge hε hε' <;> linarith

/-- Results of local Sobolev estimates on a ball of large density oscillation.
The last estimate needs access to the matrix root only when the whole ball is
in the active set. The product-rule input is the estimate for `∫|∇g|ᵖ` with
`g = truncatedDensity D φ p ε`. -/
structure LargeOscillationData (K : Set Position) (D : Density) (φ : Phase)
    (G : MatrixGradient) (p ε C : ℝ) where
  radiusDensity : ℝ
  charge_le : ∀ x ∈ K, D.charge x ≤ radiusDensity
  peakAt : Position
  peak_mem : peakAt ∈ K
  peak_max : ∀ x ∈ K, truncatedDensity D φ p ε x ≤ truncatedDensity D φ p ε peakAt
  gradient : Position → Position
  weak_gradient : ∀ i, WeakPartialOn (interior K) i (truncatedDensity D φ p ε)
    (fun x => gradient x i)
  morrey : ∀ x ∈ K, ∀ y ∈ K, volume.real K *
    |truncatedDensity D φ p ε x - truncatedDensity D φ p ε y| ^ p ≤
      C * ε ^ (-p) * (∫ x in K, ‖gradient x‖ ^ p)
  product_rule : (∫ x in K, ‖gradient x‖ ^ p) ≤ C * ((∫ x in K, weightedRoot φ G p x) +
    ε ^ (1 - p / 2) * ∫ x in K, D.charge x * φ.hessianNorm x ^ p)
  active_morrey : K ⊆ φ.active → IntegrableOn (rootPower G p) K ∧
    volume.real K * radiusDensity ≤ C * ε ^ (-p) * ∫ x in K, rootPower G p x


private theorem power_of_half_le {p P y : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P)
    (hy : 0 ≤ y) (h : P / 2 ≤ y) : P ^ p ≤ (2 : ℝ) ^ p * y ^ p := by
  rw [← Real.mul_rpow (by norm_num) hy]
  exact Real.rpow_le_rpow hP (by linarith) hp

private theorem largeOscillation_peak {K : Set Position} (hK : IsCompact K)
    {D : Density} {φ : Phase} {G : MatrixGradient} {p ε C : ℝ}
    (hp : 1 ≤ p) (hε : 0 < ε) (hε' : ε ≤ 1) (hC : 1 ≤ C)
    (hφ : PhaseAdmissible D p φ G) (L : LargeOscillationData K D φ G p ε C) :
    volume.real K * truncatedDensity D φ p ε L.peakAt ^ p ≤
      (2 : ℝ) ^ p * C ^ 2 / ε ^ (2*p-1) *
        ((∫ x in K, weightedRoot φ G p x) + ∫ x in K, D.charge x * φ.hessianNorm x ^ p) := by
  let P := truncatedDensity D φ p ε L.peakAt
  let V := volume.real K
  let A := ∫ x in K, weightedRoot φ G p x
  let B := ∫ x in K, D.charge x * φ.hessianNorm x ^ p
  let W := 1 / ε ^ (2*p-1)
  let R := ε ^ (-p)
  let S := ε ^ (1-p/2)
  let T := (2 : ℝ) ^ p
  have hp' : 0 < p := by linarith
  have hC₀ : 0 ≤ C := by linarith
  have hT : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hR : 0 ≤ R := Real.rpow_nonneg hε.le _
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hP : 0 ≤ P := truncatedDensity_nonneg ..
  have hA : 0 ≤ A := integral_nonneg (weightedRoot_nonneg φ G p)
  have hB : 0 ≤ B := integral_nonneg fun x =>
    mul_nonneg (D.charge_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hW : 0 ≤ W := one_div_nonneg.mpr (Real.rpow_nonneg hε.le _)
  have hscale : R ≤ W ∧ R*S ≤ W := phaseScale_bounds hp hε hε'
  change V * P ^ p ≤ T * C ^ 2 / ε ^ (2 * p - 1) * (A+B)
  have heq : T * C ^ 2 / ε ^ (2*p-1) * (A+B) = T * (C ^ 2 * (W*(A+B))) := by
    dsimp [W]
    ring
  rw [heq]
  by_cases ho : ∃ x ∈ K, truncatedDensity D φ p ε x < P / 2
  · obtain ⟨x, hx, hxsmall⟩ := ho
    have hh : P / 2 ≤ |P - truncatedDensity D φ p ε x| :=
      le_trans (by linarith) (le_abs_self _)
    have hpower := power_of_half_le hp'.le hP (abs_nonneg _) hh
    have hmor := L.morrey L.peakAt L.peak_mem x hx
    have hprod : (∫ x in K, ‖L.gradient x‖ ^ p) ≤ C * (A + S * B) := L.product_rule
    have hAB : R * (A + S*B) ≤ W*(A+B) := by
      rw [mul_add, mul_add, ← mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_right hscale.1 hA)
        (mul_le_mul_of_nonneg_right hscale.2 hB)
    calc
      _ ≤ T * (V * |P-truncatedDensity D φ p ε x| ^ p) := by
        simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hpower hV
      _ ≤ T * (C * R * (∫ x in K, ‖L.gradient x‖ ^ p)) := mul_le_mul_of_nonneg_left hmor hT
      _ ≤ T * (C * R * (C * (A + S*B))) := by gcongr
      _ = T * (C ^ 2 * (R*(A+S*B))) := by ring
      _ ≤ _ := by gcongr
  · have hsmall (x : Position) (hx : x ∈ K) : P / 2 ≤ truncatedDensity D φ p ε x :=
      le_of_not_gt fun hn => ho ⟨x, hx, hn⟩
    by_cases hz : P = 0
    · rw [hz, Real.zero_rpow hp'.ne', mul_zero]
      positivity
    have hactive : K ⊆ φ.active := by
      intro x hx
      by_contra ha
      have hg := truncatedDensity_off_active D φ hp' hε.le ha
      have := hsmall x hx
      linarith [lt_of_le_of_ne hP (Ne.symm hz)]
    obtain ⟨hG, hcharge⟩ := L.active_morrey hactive
    obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨L.peakAt, L.peak_mem⟩
      (hφ.regular.continuous_grad.norm.pow 2).continuousOn
    let m := ‖φ.grad y‖ ^ 2
    have hm : 0 ≤ m := sq_nonneg _
    have hpush : m * (∫ x in K, rootPower G p x) ≤ A :=
      minimum_mul_rootPower_le hφ hK.measurableSet (fun x hx => hmin hx) hG
    have hyP := power_of_half_le hp'.le hP (truncatedDensity_nonneg D φ p ε y) (hsmall y hy)
    rw [truncatedDensity_pow D φ hp' ε y] at hyP
    have htr := (truncation_bounds hp' hε.le (norm_nonneg (φ.grad y))).1
    have hval : P ^ p ≤ T * (L.radiusDensity * m) := by
      apply hyP.trans
      apply mul_le_mul_of_nonneg_left _ hT
      exact mul_le_mul (L.charge_le y hy) htr (Real.rpow_nonneg (le_max_left ..) _)
        ((D.charge_nonneg y).trans (L.charge_le y hy))
    have hAB : C*R*A ≤ C^2*(W*(A+B)) := by
      have h₁ := mul_le_mul_of_nonneg_right hscale.1 hA
      have h₂ : C ≤ C^2 := by nlinarith [mul_nonneg hC₀ (sub_nonneg.mpr hC)]
      calc
        _ = C*(R*A) := by ring
        _ ≤ C^2*(W*A) := mul_le_mul h₂ h₁ (mul_nonneg hR hA) (sq_nonneg _)
        _ ≤ _ := by gcongr; linarith
    calc
      _ ≤ T*(m*(V*L.radiusDensity)) := by
        calc
          _ ≤ V * (T * (L.radiusDensity * m)) := mul_le_mul_of_nonneg_left hval hV
          _ = _ := by ring
      _ ≤ T*(m*(C*R*(∫ x in K, rootPower G p x))) := by gcongr
      _ = T*(C*R*(m*(∫ x in K, rootPower G p x))) := by ring
      _ ≤ T*(C*R*A) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hAB hT

/-- Kinetic error on a ball of large density oscillation. Neither the conclusion
nor its global application calls for an unweighted root gradient off the active set. -/
theorem largeOscillation_kinetic {K : Set Position} (hK : IsCompact K)
    {D : Density} {φ : Phase} {G : MatrixGradient} {p ε C : ℝ}
    (hp : 1 ≤ p) (hε : 0 < ε) (hε' : ε ≤ 1) (hC : 1 ≤ C)
    (hρ : Integrable D.charge) (hφ : PhaseAdmissible D p φ G)
    (L : LargeOscillationData K D φ G p ε C) :
    (∫ x in K, D.charge x * ‖φ.grad x‖ ^ 2) ≤ (2 : ℝ) ^ p *
      (ε * (∫ x in K, D.charge x) + (2 : ℝ) ^ p * C ^ 2 / ε ^ (2*p-1) *
        ((∫ x in K, weightedRoot φ G p x) + ∫ x in K, D.charge x * φ.hessianNorm x ^ p)) := by
  let P := truncatedDensity D φ p ε L.peakAt
  have hp' : 0 < p := by linarith
  have hT : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
  have hconst : IntegrableOn (fun _ : Position => P ^ p) K := integrableOn_const hK.measure_lt_top.ne
  have hcomb := (hρ.integrableOn.const_mul ε).add hconst
  have hpoint (x : Position) (hx : x ∈ K) : D.charge x * ‖φ.grad x‖ ^ 2 ≤
      (2 : ℝ) ^ p * (ε * D.charge x + P ^ p) := by
    have h := mul_le_mul_of_nonneg_left (truncation_bounds hp' hε.le (norm_nonneg (φ.grad x))).2
      (D.charge_nonneg x)
    have hg := Real.rpow_le_rpow (truncatedDensity_nonneg D φ p ε x) (L.peak_max x hx) hp'.le
    rw [truncatedDensity_pow D φ hp' ε x] at hg
    calc
      _ ≤ _ := h
      _ = (2 : ℝ) ^ p * (ε * D.charge x + D.charge x * truncatedSpeed p ε ‖φ.grad x‖ ^ p) := by ring
      _ ≤ _ := by gcongr
  have hint := setIntegral_mono_on hφ.kinetic.integrableOn (hcomb.const_mul ((2 : ℝ) ^ p))
    hK.measurableSet hpoint
  change (∫ x in K, D.charge x * ‖φ.grad x‖ ^ 2) ≤
    ∫ x in K, (2 : ℝ)^p * (ε * D.charge x + P^p) at hint
  rw [integral_const_mul, integral_add (hρ.integrableOn.const_mul ε) hconst,
    integral_const_mul, setIntegral_const, smul_eq_mul] at hint
  exact hint.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
    (largeOscillation_peak hK hp hε hε' hC hφ L)) hT)

end TSGA.PhaseLocalization
