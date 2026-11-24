import TSGA.CoulombHolder
import TSGA.MinorityFraction

/-! # Fixed-direction minority regularity for the Coulomb spin spiral gas -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization
open scoped ComplexOrder

/-- The fixed-axis part of Proposition E.2(vi). Along a segment of common trace
the estimate holds with both the cube root and the p-th root of the mixing
fraction. Opposite spin-polarized endpoints give the minority fraction. -/
theorem coulomb_ssw_minority_fraction {η : Mollifier} {J K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (removal : SpiralRemovalTrials η J) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3 : ℝ)) ≤ indirectAt D.matrix Γ) :
    ∃ C > 0, ∀ {r : ℝ}, 0 < r → ∀ {P Q : SpinMatrix}, P ∈ fixedCharge r → Q ∈ fixedCharge r →
      ∀ q : Position, ∀ {s t : ℝ}, s ∈ Set.Icc 0 (1/2) → t ∈ Set.Icc 0 (1/2) →
      let a := |sswEnergy energy η (AffineMap.lineMap P Q t) q - sswEnergy energy η (AffineMap.lineMap P Q s) q|
      a ≤ C*holderGrowth r q*|t^(1/3:ℝ)-s^(1/3:ℝ)| ∧
        ∀ p : ℝ, 3 ≤ p → a ≤ C*holderGrowth r q*(p/3)*|t^(1/p)-s^(1/p)| := by
  obtain ⟨L, hL, hmat⟩ := coulomb_ssw_holder loc states rate removal hc lo
  refine ⟨12*L, by positivity, ?_⟩
  intro r hr P Q hP hQ q s t hs ht
  let H := L*holderGrowth r q
  have hH : 0 ≤ H := by dsimp [H, holderGrowth]; positivity
  have h := fixedCharge_segment_cubeRoot (e := fun A => sswEnergy energy η A q) hr hH
    (coulomb_ssw_convex_fixed_charge η loc states hr q) (fun A hA B hB => by
      have hmax : max A.trace.re B.trace.re = r := by rw [hA.2, hB.2, max_self]
      simpa only [hmax] using hmat hA.1 hB.1 q (hmax.symm ▸ hr)) hP hQ hs ht
  change _ ≤ _ ∧ ∀ p : ℝ, _ → _ ≤ _
  have he : 12*H = 12*L*holderGrowth r q := by dsimp [H]; ring
  rw [← he]
  refine ⟨h, fun p hp => ?_⟩
  have hs1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have ht1 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  exact h.trans ((mul_le_mul_of_nonneg_left (cubeRoot_distance_le_root hp hs1 ht1)
    (mul_nonneg (by norm_num) hH)).trans_eq (by ring))

/-- The same constants apply to every spin direction and include the fully polarized endpoint t=0. -/
theorem coulomb_ssw_fixed_axis {η : Mollifier} {J K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (removal : SpiralRemovalTrials η J) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3 : ℝ)) ≤ indirectAt D.matrix Γ) :
    ∃ C > 0, ∀ {r : ℝ}, 0 < r → ∀ {n : Fin 3 → ℝ}, spinDot n n = 1 → ∀ q : Position,
      ∀ {s t : ℝ}, s ∈ Set.Icc 0 (1/2) → t ∈ Set.Icc 0 (1/2) →
      let a := |sswEnergy energy η (minoritySpinMatrix r n t) q - sswEnergy energy η (minoritySpinMatrix r n s) q|
      a ≤ C*holderGrowth r q*|t^(1/3:ℝ)-s^(1/3:ℝ)| ∧
        ∀ p : ℝ, 3 ≤ p → a ≤ C*holderGrowth r q*(p/3)*|t^(1/p)-s^(1/p)| := by
  obtain ⟨C, hC, H⟩ := coulomb_ssw_minority_fraction loc states rate removal hc lo
  refine ⟨C, hC, ?_⟩
  intro r hr n hn q s t hs ht
  have hneg : spinDot (-n) (-n) = 1 := by simpa [spinDot] using hn
  exact H hr (pureSpin_fixedCharge hr.le hn) (pureSpin_fixedCharge hr.le hneg) q hs ht

end TSGA.ManyBody
