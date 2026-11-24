import TSGA.CoulombRotationReplacement
import TSGA.IslandInteriorTrial
import TSGA.BulkLocalization

/-! # Energy terms in the two gauge errors on a small comparison ball -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW Set
open scoped ComplexOrder

/-- The powers entering the Lieb–Oxford and kinetic terms have the same
majorant after tapering a charge bounded by r. -/
theorem small_taper_moment {A : Density} {f : Position → ℝ} {r a : ℝ}
    (hr : 0 ≤ r) (ha : a ∈ Icc (1:ℝ) 2) (hf : ∀ x, f x ∈ Icc (0:ℝ) 1)
    (fi : Integrable f) (hm : AEMeasurable A.charge volume)
    (cap : ∀ x, A.charge x ≤ f x*r) :
    Integrable (fun x => A.charge x^a) ∧ chargeMoment A a ≤ (r+r^2)*(∫ x, f x) := by
  have ha₀ : 0 < a := zero_lt_one.trans_le ha.1
  have mass : r^a ≤ r+r^2 := by
    rcases hr.eq_or_lt with hz | hpos
    · rw [← hz, Real.zero_rpow ha₀.ne']; norm_num
    · exact BulkRegime.density_power_le hpos ha
  have pt (x : Position) : A.charge x^a ≤ f x*(r+r^2) := by
    apply (Real.rpow_le_rpow (A.charge_nonneg _) (cap x) ha₀.le).trans
    rw [Real.mul_rpow (hf x).1 hr]
    exact mul_le_mul (Real.rpow_le_self_of_le_one (hf x).1 (hf x).2 ha.1) mass
      (Real.rpow_nonneg hr _) (hf x).1
  have i := fi.mul_const (r+r^2)
  have ia : Integrable fun x => A.charge x^a :=
    i.mono' (hm.pow_const a).aestronglyMeasurable (ae_of_all _ fun x =>
      (Real.norm_of_nonneg (Real.rpow_nonneg (A.charge_nonneg _) _)).le.trans (pt x))
  exact ⟨ia,(integral_mono ia i pt).trans_eq (by rw [integral_mul_const,mul_comm])⟩

/-- Charge moments are preserved through each of the two local spin rotations. -/
private theorem gauge_charge {A B : Density} {L : ℝ} (g : GaugeComparison A B L) : A.charge = B.charge := by
  funext x
  rw [← conjugated_charge A g.U x]
  exact congrArg (fun M : Position → SpinMatrix => (M x).trace.re) g.target

/-- A single quasi-free trial for the aligned background bounds the energy
terms in both gauges. The costs for changing axes and phase remain separate. -/
theorem small_replacement_error {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Y} [IsProbabilityMeasure ν]
    {K : Set Position} {t : SpiralTaper K} {M : Density} {φ : Phase} {low high : SpinMatrix}
    {ε η C r W P I T : ℝ} (H : FiniteEnergyInputs)
    (D : CoulombTileReplacement μ ν M φ t low high ε η C H.loCoeff)
    (he : 0 < ε) (hle : ε ≤ 1) (hr : 0 ≤ r) (cap : ∀ x ∈ K, M.charge x ≤ r)
    (fi : Integrable t.shape) (σ : ℝ) (sign : σ=1 ∨ σ=-1)
    (island : (if σ=1 then D.lower.cost else D.upper.cost) ≤ I)
    (bg : sqrtKinetic D.upper.gradients.background ≤ T)
    (hW : 0 ≤ W) (hP : 0 ≤ P)
    (g1 : D.gauge.forwardCost ≤ W) (g2 : D.gauge.inverseCost ≤ W)
    (p1 : D.phaseGauge.forwardCost ≤ P) (p2 : D.phaseGauge.inverseCost ≤ P) :
    let mass := (r+r^2)*(∫ x, t.shape x)
    let base := (H.interiorConstant+H.loCoeff)*mass + H.interiorConstant*T
    D.error σ ≤ I + 6*ε*base + (8/ε)*(W+P) := by
  intro mass base
  let A := t.field D.aligned
  let B := t.field M
  let Z := t.phaseField M φ
  let moment := H.loCoeff * chargeMoment A (4/3)
  have eqAB : A.charge = B.charge := gauge_charge D.gauge
  have eqBZ : B.charge = Z.charge := gauge_charge D.phaseGauge
  have momentB : H.loCoeff*chargeMoment B (4/3) = moment := by simp only [moment, chargeMoment, eqAB]
  have momentZ : H.loCoeff*chargeMoment Z (4/3) = moment := by simp only [moment, chargeMoment, eqAB, eqBZ]
  have regular := D.upper.gradients.background_regular
  have localCap (x : Position) : A.charge x ≤ t.shape x*r := by
    rw [eqAB,show B.charge x = t.shape x*M.charge x from t.field_charge M x]
    by_cases hx : x ∈ K
    · exact mul_le_mul_of_nonneg_left (cap x hx) (t.range x).1
    · simp [t.outside x hx]
  have lo := (small_taper_moment (A := A) hr (by constructor <;> norm_num : (4/3:ℝ) ∈ Icc 1 2)
    t.range fi regular.charge.aestronglyMeasurable.aemeasurable localCap).2
  have tf := small_taper_moment (A := A) hr (by constructor <;> norm_num : (5/3:ℝ) ∈ Icc 1 2)
    t.range fi regular.charge.aestronglyMeasurable.aemeasurable localCap
  obtain ⟨Γ,rep,kin,inter⟩ := H.exists_island_state A _ regular tf.1
  have bA : energy A.matrix + moment ≤ base := by
    have search := levyLieb_le rep
    have bkin := kin.trans (mul_le_mul_of_nonneg_left (add_le_add tf.2 bg) H.interiorConstant_nonneg)
    have blo := mul_le_mul_of_nonneg_left lo H.lo_nonneg
    change levyLieb A.matrix - hartree A.charge + H.loCoeff*chargeMoment A (4/3) ≤
      (H.interiorConstant+H.loCoeff)*mass + H.interiorConstant*T
    change _ ≤ H.interiorConstant*(mass+T) at bkin
    change _ ≤ H.loCoeff*mass at blo
    linarith only [search, inter, bkin, blo]
  have b₀ : 0 ≤ base := by
    have m₀ : 0 ≤ mass := mul_nonneg (add_nonneg hr (sq_nonneg _)) (integral_nonneg fun x => (t.range x).1)
    have t₀ : 0 ≤ T := (integral_nonneg (fun x => sq_nonneg (matrixGradNorm D.upper.gradients.background x))).trans bg
    dsimp only [base]
    positivity [H.interiorConstant_nonneg,H.lo_nonneg]
  have ab := (D.gauge.signed (ε := 1) zero_lt_one).1
  have bz := (D.phaseGauge.signed (ε := 1) zero_lt_one).1
  change energy B.matrix ≤ energy A.matrix + (1*(energy A.matrix + moment)+(1+1/1)*D.gauge.forwardCost) at ab
  change energy Z.matrix ≤ energy B.matrix + (1*(energy B.matrix + H.loCoeff*chargeMoment B (4/3))+(1+1/1)*D.phaseGauge.forwardCost) at bz
  rw [momentB] at bz
  have bB : energy B.matrix+moment ≤ 2*base+2*W := by linarith only [ab,bA,g1]
  have bZ : energy Z.matrix+moment ≤ 4*base+4*W+2*P := by linarith only [bz,bB,p1]
  have coeff : 0 ≤ 1+1/ε := by positivity
  have factor : 6*ε + (1+1/ε) ≤ 8/ε := by
    apply (le_div_iff₀ he).2
    have he2 : ε*ε ≤ 1 := (mul_le_mul_of_nonneg_left hle he.le).trans (by simpa using hle)
    field_simp [he.ne']
    nlinarith only [he2, hle, he.le]
  have b : (if σ=1 then energy A.matrix + moment + (energy B.matrix+moment)
      else energy B.matrix+moment+(energy Z.matrix+moment)) ≤ 6*base + 6*(W+P) := by
    split <;> linarith only [bA,bB,bZ,hW,hP,b₀]
  have g : ε*(6*base + 6*(W+P)) + (1+1/ε)*(W+P) ≤ 6*ε*base+(8/ε)*(W+P) := by
    nlinarith only [mul_le_mul_of_nonneg_right factor (add_nonneg hW hP)]
  rcases sign with rfl | rfl
  · simp only [ite_true, CoulombTileReplacement.error, gaugeError] at island ⊢
    simp only [ite_true] at b
    change _+ (ε*(energy A.matrix+moment)+(1+1/ε)*D.gauge.forwardCost) +
      (ε*(energy B.matrix+H.loCoeff*chargeMoment B (4/3))+(1+1/ε)*D.phaseGauge.forwardCost) ≤ _
    rw [momentB]
    linarith only [island, mul_le_mul_of_nonneg_left b he.le,
      mul_le_mul_of_nonneg_left (add_le_add g1 p1) coeff,g]
  · have ne : (-1:ℝ) ≠ 1 := by norm_num
    simp only [CoulombTileReplacement.error, gaugeError, ne, ite_false] at island b ⊢
    change _+ (ε*(energy B.matrix+H.loCoeff*chargeMoment B (4/3))+(1+1/ε)*D.gauge.inverseCost) +
      (ε*(energy Z.matrix+H.loCoeff*chargeMoment Z (4/3))+(1+1/ε)*D.phaseGauge.inverseCost) ≤ _
    rw [momentB,momentZ]
    linarith only [island, mul_le_mul_of_nonneg_left b he.le,
      mul_le_mul_of_nonneg_left (add_le_add g2 p2) coeff,g]

end TSGA.ManyBody
