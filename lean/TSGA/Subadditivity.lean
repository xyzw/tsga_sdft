import TSGA.IslandHartree
import TSGA.IslandScales
import TSGA.KineticEnergy

/-! # From random island trials to local subadditivity

The three costs refer to the same mixed-state experiment. The finite-radius
inequality and its bounded-charge specialization use the constrained-search
energy and charge integrals in the manuscript.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization

def islandBackground (B : Density) (S : MatrixGradient) : ℝ :=
  (∫ x, B.charge x + B.charge x ^ 2) + sqrtKinetic S

/-- The last three terms of the finite-radius estimate, prior to using an
essential upper bound on the added charge. -/
def islandAdded (D : Density) (ε r : ℝ) : ℝ :=
  (ε ^ (-(2/3:ℝ))) * chargeMoment D (5/3) +
  r⁻¹^2 * (∫ x, D.charge x) + (r^2/ε) * (∫ x, D.charge x ^ 2)

/-- Combining the outside, inside, and fluctuation estimates after fixing
the smoothing width. The hypotheses concern individual costs of the trial. -/
theorem subadditivity_of_trial {B D : Density} {S G : MatrixGradient}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (t : IslandTrial μ (B.matrix+D.matrix)) {C ε r : ℝ}
    (outside : t.outsideEnergy ≤ energy B.matrix + C*ε*islandBackground B S)
    (inside : t.insideEnergy ≤ C*(ε*islandBackground B S + sqrtKinetic G +
      ε^(-(2/3:ℝ))*chargeMoment D (5/3) + r⁻¹^2*(∫ x, D.charge x)))
    (fluct : t.fluctuation ≤ C*(ε*islandBackground B S + (r^2/ε)*(∫ x, D.charge x^2))) :
    energy (B.matrix+D.matrix) ≤ energy B.matrix +
      C*(3*ε*islandBackground B S + sqrtKinetic G + islandAdded D ε r) := by
  unfold islandAdded
  linarith only [t.energy_le, outside, inside, fluct]

private theorem added_le_of_cap {D : Density} {ε r cap : ℝ} (he : 0 < ε)
    (hl : 0 ≤ cap) (hcap : ∀ᵐ x, D.charge x ≤ cap) (hm : Integrable D.charge)
    (hscale : r⁻¹^2 + (cap/ε)*r^2 ≤ 2*(ε + Real.sqrt (cap/ε) + cap/ε)) :
    islandAdded D ε r ≤ 3*(ε + Real.sqrt (cap/ε) + cap/ε)*(∫ x, D.charge x) := by
  let z := cap/ε
  let m := ∫ x, D.charge x
  have hz : 0 ≤ z := div_nonneg hl he.le
  have hm' : 0 ≤ m := integral_nonneg D.charge_nonneg
  have hq : (∫ x, D.charge x ^ 2) ≤ cap*m := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (hm.const_mul cap)
    exact hcap.mono fun x hx => by simpa only [sq] using mul_le_mul_of_nonneg_right hx (D.charge_nonneg x)
  have hp : chargeMoment D (5/3) ≤ cap^(2/3:ℝ) * m := by
    unfold chargeMoment
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ fun x => Real.rpow_nonneg (D.charge_nonneg x) _) (hm.const_mul _)
    filter_upwards [hcap] with x hx
    have h := Real.rpow_le_rpow (D.charge_nonneg x) hx (by norm_num : 0 ≤ (2/3:ℝ))
    rw [show (5/3:ℝ)=(2/3:ℝ)+1 by norm_num, Real.rpow_add_one' (D.charge_nonneg x) (by norm_num)]
    exact mul_le_mul_of_nonneg_right h (D.charge_nonneg x)
  have hcoeff : ε^(-(2/3:ℝ))*cap^(2/3:ℝ) = z^(2/3:ℝ) := by
    rw [Real.rpow_neg he.le, Real.div_rpow hl he.le]
    ring
  have htf : ε^(-(2/3:ℝ))*chargeMoment D (5/3) ≤ (Real.sqrt z+z)*m :=
    calc
      _ ≤ ε^(-(2/3:ℝ))*(cap^(2/3:ℝ)*m) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg he.le _)
      _ = z^(2/3:ℝ)*m := by rw [← mul_assoc, hcoeff]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Islands.two_thirds_le _ hz) hm'
  have heq : r^2/ε*cap = z*r^2 := by dsimp [z]; ring
  have hq' : (r^2/ε)*(∫ x, D.charge x^2) ≤ z*r^2*m :=
    (mul_le_mul_of_nonneg_left hq (div_nonneg (sq_nonneg _) he.le)).trans_eq (by rw [← mul_assoc, heq])
  change r⁻¹^2 + z*r^2 ≤ 2*(ε + Real.sqrt z + z) at hscale
  change _ + r⁻¹^2*m + _ ≤ 3*(ε + Real.sqrt z + z)*m
  linarith only [htf,hq',mul_le_mul_of_nonneg_right hscale hm',mul_nonneg he.le hm']

/-- The bounded-charge version of Lemma C.1 follows by choosing the
island radius in its finite-radius version. -/
theorem subadditivity_of_bounded_charge {B D : Density} {S G : MatrixGradient}
    {ε cap C : ℝ} (he : 0 < ε) (he' : ε ≤ 1) (hC : 0 ≤ C)
    (hl : 0 ≤ cap) (hcap : ∀ᵐ x, D.charge x ≤ cap) (hm : Integrable D.charge)
    (finite_radius : ∀ r : ℝ, 1 ≤ r → ε*r^2 ≤ 1 →
      energy (B.matrix+D.matrix) ≤ energy B.matrix +
        C*(3*ε*islandBackground B S + sqrtKinetic G + islandAdded D ε r)) :
    energy (B.matrix+D.matrix) ≤ energy B.matrix + C*(3*ε*islandBackground B S + sqrtKinetic G +
      3*(ε + Real.sqrt (cap/ε) + cap/ε)*(∫ x, D.charge x)) := by
  obtain ⟨r,hr,hr',hopt⟩ := Islands.choose_island_radius he he' hl
  exact (finite_radius r hr hr').trans (add_le_add_right
    (mul_le_mul_of_nonneg_left (add_le_add_right (added_le_of_cap he hl hcap hm hopt) _) hC) _)

end TSGA.ManyBody
