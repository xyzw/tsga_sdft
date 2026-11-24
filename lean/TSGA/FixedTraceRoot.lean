import TSGA.EigenframeAlignment
import TSGA.SpinPopulationSegment

/-! # Root Lipschitz regularity at a fixed trace

The two cases depend on the minority occupancy. At occupancy at least r/4
the uniform minority estimate applies. At smaller occupancy the root has
a spectral gap and an aligning rotation costs at most the root distance.
-/

noncomputable section
namespace TSGA.SSW
open Matrix TSGA.Localization
open scoped ComplexOrder MatrixOrder

def rootGap (p : ℝ) : ℝ := (3/4:ℝ)^(1/p) - (1/4:ℝ)^(1/p)

theorem rootGap_pos {p : ℝ} (hp : 0 < p) : 0 < rootGap p :=
  sub_pos.mpr (Real.rpow_lt_rpow (by norm_num) (by norm_num) (one_div_pos.mpr hp))

private theorem scalar_gap {a b r p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r) (hp : 0 < p)
    (hab : a+b=r) (hmin : min a b ≤ r/4) :
    r^(1/p)*rootGap p ≤ |a^(1/p)-b^(1/p)| := by
  wlog order : b ≤ a generalizing a b
  · rw [abs_sub_comm]
    exact this hb ha (by linarith) (min_comm a b ▸ hmin) (le_of_not_ge order)
  rw [min_eq_right order] at hmin
  have hmajor : r*(3/4) ≤ a := by linarith
  have hminor : b ≤ r*(1/4) := by linarith
  have hu := one_div_pos.mpr hp
  have h1 := Real.rpow_le_rpow (mul_nonneg hr.le (by norm_num)) hmajor hu.le
  have h2 := Real.rpow_le_rpow hb hminor hu.le
  rw [Real.mul_rpow hr.le (by norm_num)] at h1 h2
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hb order hu.le)), rootGap, mul_sub]
  linarith

private theorem eigen_floor {A : SpinMatrix} (hA : A.PosSemidef) {m : ℝ}
    (h : m ≤ min (hA.1.eigenvalues 0) (hA.1.eigenvalues 1)) : m • (1 : SpinMatrix) ≤ A := by
  have he := (inSpinFrame_floor_iff hA.1.eigenvectorUnitary hA.1.eigenvalues m).2 (fun i => by
    fin_cases i
    · exact h.trans (min_le_left _ _)
    · exact h.trans (min_le_right _ _))
  exact he.trans_eq hA.1.spectral_theorem.symm

/-- Explicit equal-trace coefficient. The three given bounds govern the
uniform minority slice, the change along a population segment, and the
unitary spin rotation, respectively. -/
theorem fixedTrace_root_lipschitz {e : SpinMatrix → ℝ} {p r L F G : ℝ}
    (hp : 1 ≤ p) (hr : 0 < r) (hL : 0 ≤ L) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (bulk : ∀ A ∈ fixedCharge r, ∀ B ∈ fixedCharge r,
      (r/4) • (1 : SpinMatrix) ≤ A → (r/4) • (1 : SpinMatrix) ≤ B →
      |e A-e B| ≤ L*(hilbertSchmidt (A-B)/r))
    (frac : ∀ P ∈ fixedCharge r, ∀ Q ∈ fixedCharge r, ∀ s ∈ Set.Icc (0:ℝ) (1/2), ∀ t ∈ Set.Icc (0:ℝ) (1/2),
      |e (AffineMap.lineMap P Q t)-e (AffineMap.lineMap P Q s)| ≤ F*|t^(1/p)-s^(1/p)|)
    (angle : ∀ A ∈ fixedCharge r, ∀ S : unitary SpinMatrix,
      |e (Unitary.conjStarAlgAut ℂ SpinMatrix S A)-e A| ≤ G*hilbertSchmidt ((S : SpinMatrix)-1))
    {A B : SpinMatrix} (hA : A ∈ fixedCharge r) (hB : B ∈ fixedCharge r) :
    |e A-e B| ≤ (L*p + F + 4*G/rootGap p) *
      (hilbertSchmidt (hA.1.1.cfc (fun t => t^(1/p)) - hB.1.1.cfc (fun t => t^(1/p)))/r^(1/p)) := by
  let u := 1/p
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hu : 0 < u := one_div_pos.mpr hp0
  have hu1 : u ≤ 1 := (div_le_iff₀ hp0).2 (by simpa only [one_mul] using hp)
  have hru := Real.rpow_pos_of_pos hr u
  have hg := rootGap_pos hp0
  let Gp := 4*G/rootGap p
  have hGp : 0 ≤ Gp := div_nonneg (mul_nonneg (by norm_num) hG) hg.le
  have hLp := mul_nonneg hL hp0.le
  let d := fun (X Y : SpinMatrix) (hX : X.PosSemidef) (hY : Y.PosSemidef) =>
    hilbertSchmidt (hX.1.cfc (fun t => t^u) - hY.1.cfc (fun t => t^u))
  have hd (X Y : SpinMatrix) (hX : X.PosSemidef) (hY : Y.PosSemidef) : 0 ≤ d X Y hX hY := Real.sqrt_nonneg _
  let m := fun (X : SpinMatrix) (hX : X.PosSemidef) => min (hX.1.eigenvalues 0) (hX.1.eigenvalues 1)
  have near {X Y : SpinMatrix} (hX : X ∈ fixedCharge r) (hY : Y ∈ fixedCharge r) (hm : m X hX.1 ≤ r/4) :
      |e X-e Y| ≤ (L*p+F+Gp)*(d X Y hX.1 hY.1/r^u) := by
    obtain ⟨S, hS, hcost⟩ := eigenframe_alignment hX.1 hY.1 (fun t => t^u)
      (fun _ hx _ _ h => Real.rpow_le_rpow hx h hu.le)
    have hgap := scalar_gap (hX.1.eigenvalues_nonneg 0) (hX.1.eigenvalues_nonneg 1) hr hp0
      ((spin_population_sum hX.1).trans hX.2) hm
    let n := hilbertSchmidt ((S : SpinMatrix)-1)
    let z := d X Y hX.1 hY.1/r^u
    have hz : 0 ≤ z := div_nonneg (hd X Y hX.1 hY.1) hru.le
    have hn : n ≤ 4/rootGap p*z := by
      have hsmall : n*(r^u*rootGap p) ≤ 4*d X Y hX.1 hY.1 :=
        (mul_le_mul_of_nonneg_left hgap (show 0 ≤ n from Real.sqrt_nonneg _)).trans hcost
      have hdiv := (le_div_iff₀ (mul_pos hru hg)).2 hsmall
      exact hdiv.trans_eq (by dsimp only [z]; ring)
    have hpop := fixed_frame_population_change hr hu hF frac hX hY
    have hang := angle Y hY S
    rw [hS] at hang
    have hsum := (abs_sub_le (e X) (e (inSpinFrame hX.1.1.eigenvectorUnitary hY.1.1.eigenvalues)) (e Y)).trans
      (add_le_add hpop hang)
    change _ ≤ F*z+G*n at hsum
    dsimp only [Gp]
    change _ ≤ (L*p+F+4*G/rootGap p)*z
    apply hsum.trans
    calc
      _ ≤ F*z+G*(4/rootGap p*z) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hn hG)
      _ ≤ _ := by
        have he : G*(4/rootGap p*z) = (4*G/rootGap p)*z := by ring
        rw [he]; nlinarith only [mul_nonneg hLp hz]
  change _ ≤ (L*p+F+Gp)*(d A B hA.1 hB.1/r^u)
  by_cases ha : m A hA.1 ≤ r/4
  · exact near hA hB ha
  by_cases hb : m B hB.1 ≤ r/4
  · have h := near hB hA hb
    rw [abs_sub_comm (e B)] at h
    simpa only [d, hs_sub_comm (hB.1.1.cfc _) (hA.1.1.cfc _)] using h
  have ht := bulk A hA B hB (eigen_floor hA.1 (le_of_not_ge ha)) (eigen_floor hB.1 (le_of_not_ge hb))
  have hid {X : SpinMatrix} (hX : X.PosSemidef) : hX.1.cfc (fun t : ℝ => t^(1:ℝ)) = X := by
    simp only [Real.rpow_one]
    change hX.1.cfc id = _
    rw [← hX.1.cfc_eq, cfc_id ℝ X hX.1.isSelfAdjoint]
  have hraw := matrix_power_oscillation hA.1 hB.1 (u := 1) hu hu1 hr.le hA.2.le hB.2.le
  rw [hid hA.1, hid hB.1, Real.rpow_sub hr, Real.rpow_one, show 1/u = p by simp [u]] at hraw
  have hscaled : hilbertSchmidt (A-B)/r ≤ p*(d A B hA.1 hB.1/r^u) := by
    apply (div_le_iff₀ hr).2
    exact hraw.trans_eq (by dsimp [d]; ring)
  apply ht.trans
  have hz := div_nonneg (hd A B hA.1 hB.1) hru.le
  calc
    _ ≤ L*(p*(d A B hA.1 hB.1/r^u)) := mul_le_mul_of_nonneg_left hscaled hL
    _ ≤ _ := by nlinarith only [mul_nonneg (add_nonneg hF hGp) hz]

end TSGA.SSW
