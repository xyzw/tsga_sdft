import TSGA.MainTheorem
import TSGA.ErrorDensity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Uniform interpolation in the global-root estimate

The first paragraph of the proof of Theorem 3.3 reduces the sharp alternative
to θ = 2/p. The weak Hilbert–Schmidt functional-calculus chain rule is the
analytic input. Its scalar Lipschitz bound, the integral comparison, and the
uniformity in θ are proved here.
-/

namespace TSGA.Localization

open MeasureTheory PhaseLocalization

private theorem slope_numerator_le {k t : ℝ} (hk : 2 ≤ k) (ht : 0 ≤ t) :
    t ≤ 1 + k * t ^ (k - 1) := by
  have hpow := Real.rpow_nonneg ht (k - 1)
  rcases le_total t 1 with h | h
  · linarith [mul_nonneg (show 0 ≤ k by linarith) hpow]
  · have ht' : t ≤ t ^ (k - 1) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h (show 1 ≤ k - 1 by linarith)
    nlinarith [mul_nonneg (show 0 ≤ k - 1 by linarith) hpow]

theorem power_change_slope {k t : ℝ} (hk : 2 ≤ k) (ht : 0 ≤ t) :
    2 * t / (1 + k * t ^ (k - 1)) ≤ 2 := by
  have hden : 0 < 1 + k * t ^ (k - 1) :=
    by linarith [mul_nonneg (show 0 ≤ k by linarith) (Real.rpow_nonneg ht (k - 1))]
  exact (div_le_iff₀ hden).2 (by linarith [slope_numerator_le hk ht])

/-- Difference-quotient form of the 2-Lipschitz estimate for F(t+tᵏ)=t². -/
theorem power_change_lipschitz {k : ℝ} (hk : 2 ≤ k) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |s ^ 2 - t ^ 2| ≤ 2 * |(s + s ^ k) - (t + t ^ k)| := by
  let f := fun x : ℝ => 2 * (x + x ^ k) - x ^ 2
  have deriv_f (x : ℝ) : HasDerivAt f (2 * (1 + k * x ^ (k - 1)) - 2 * x) x := by
    have h := (((hasDerivAt_id x).add (Real.hasDerivAt_rpow_const (p := k)
      (Or.inr (by linarith)))).const_mul 2).sub ((hasDerivAt_id x).pow 2)
    simpa [f, Pi.sub_def, Pi.pow_def] using h
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (deriv_f x).continuousAt.continuousWithinAt) (fun x _ => (deriv_f x).hasDerivWithinAt)
    intro x hx
    have hx' : 0 ≤ x := interior_subset hx
    linarith [slope_numerator_le hk hx']
  have ordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      b ^ 2 - a ^ 2 ≤ 2 * ((b + b ^ k) - (a + a ^ k)) := by
    have h := hm ha (ha.trans hab) hab
    dsimp [f] at h
    linarith
  rcases le_total s t with h | h
  · have hsq : s ^ 2 ≤ t ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hs ht)]
    have hpow := add_le_add h (Real.rpow_le_rpow hs h (by linarith : 0 ≤ k))
    rw [abs_of_nonpos (sub_nonpos.mpr hsq), abs_of_nonpos (sub_nonpos.mpr hpow)]
    linarith [ordered s t hs h]
  · have hsq : t ^ 2 ≤ s ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hs ht)]
    have hpow := add_le_add h (Real.rpow_le_rpow ht h (by linarith : 0 ≤ k))
    rw [abs_of_nonneg (sub_nonneg.mpr hsq), abs_of_nonneg (sub_nonneg.mpr hpow)]
    exact ordered t s ht h

/-- Sobolev functional calculus for a sum of two positive matrix powers.
The hypothesis on scalars says that tˡ is L-Lipschitz as a function of t+tᵏ.
Here t represents an eigenvalue of Dᵃ. The Hilbert–Schmidt Lipschitz estimate
and weak difference quotients supply the weak gradient on each compact set. -/
def WeakPowerComparison : Prop :=
  ∀ (D : Density) (a k l L : ℝ) (G T : MatrixGradient),
    0 < a → 0 < k → 0 < l → 0 ≤ L →
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |s ^ l - t ^ l| ≤ L * |(s + s ^ k) - (t + t ^ k)|) →
    IsMatrixGradientOn Set.univ (D.power a) G →
    IsMatrixGradientOn Set.univ (D.power (a * k)) T →
    ∃ U : MatrixGradient, IsMatrixGradientOn Set.univ (D.power (a * l)) U ∧
      AEStronglyMeasurable (matrixGradNorm U) volume ∧
      ∀ᵐ x, matrixGradNorm U x ≤ L * (matrixGradNorm G x + matrixGradNorm T x)

private theorem power_sum_bound {u g t p : ℝ} (hp : 0 ≤ p) (hu : 0 ≤ u) (hg : 0 ≤ g) (ht : 0 ≤ t)
    (h : u ≤ 2 * (g + t)) : u ^ p ≤ (4 : ℝ) ^ p * (g ^ p + t ^ p) := by
  have h4 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) p
  have aux (x : ℝ) (hx : 0 ≤ x) (hu' : u ≤ 4 * x) : u ^ p ≤ 4 ^ p * x ^ p := by
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hx] using Real.rpow_le_rpow hu hu' hp
  rcases le_total g t with hgt | htg
  · exact (aux t ht (by linarith)).trans (mul_le_mul_of_nonneg_left
      (by linarith [Real.rpow_nonneg hg p]) h4)
  · exact (aux g hg (by linarith)).trans (mul_le_mul_of_nonneg_left
      (by linarith [Real.rpow_nonneg ht p]) h4)

/-- The endpoint density has an Lᵖ weak gradient and its integral is bounded
uniformly over all exponents with pθ ≥ 2. -/
theorem endpoint_gradient (chain : WeakPowerComparison) {p θ : ℝ} (hp : 0 < p) (hθ : 2 ≤ p * θ)
    {D : Density} {S T G : MatrixGradient} (hD : DensityRegular D p θ S T)
    (hroot : IsMatrixGradientOn Set.univ (D.power (1 / p)) G)
    (hg : MemLp (matrixGradNorm G) (ENNReal.ofReal p)) :
    ∃ U : MatrixGradient, DensityRegular D p (2 / p) S U ∧
      (∫ x, matrixGradNorm U x ^ p) ≤ 4 ^ p * ((∫ x, matrixGradNorm G x ^ p) +
        ∫ x, matrixGradNorm T x ^ p) := by
  have hθ' : 1 / p * (p * θ) = θ := by field_simp
  have hweak : IsMatrixGradientOn Set.univ (D.power (1 / p * (p * θ))) T := by
    rw [hθ']
    exact hD.theta_gradient
  obtain ⟨U, hU, hUm, hb⟩ := chain D (1 / p) (p * θ) 2 2 G T (by positivity)
    (by linarith) (by norm_num) (by norm_num) (fun s t hs ht => by
      simpa only [Real.rpow_two] using power_change_lipschitz hθ hs ht) hroot hweak
  have hUlp : MemLp (matrixGradNorm U) (ENNReal.ofReal p) := by
    apply ((hg.add hD.theta_Lp).const_mul 2).mono' hUm
    filter_upwards [hb] with x hx
    change ‖matrixGradNorm U x‖ ≤ 2 * (matrixGradNorm G x + matrixGradNorm T x)
    rwa [Real.norm_of_nonneg (show 0 ≤ matrixGradNorm U x from Real.sqrt_nonneg _)]
  have hUreg : DensityRegular D p (2 / p) S U := by
    have hpower : 1 / p * 2 = 2 / p := by ring
    rw [hpower] at hU
    exact { hD with theta_gradient := hU, theta_Lp := hUlp }
  refine ⟨U, hUreg, ?_⟩
  have hG := rootPower_integrable hp hg
  have hT := rootPower_integrable hp hD.theta_Lp
  have hi := integral_mono_ae (rootPower_integrable hp hUlp) ((hG.add hT).const_mul ((4:ℝ) ^ p))
    (hb.mono fun x hx => power_sum_bound hp.le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) hx)
  rw [integral_const_mul, integral_add' hG hT] at hi
  exact hi

/-- Transfer the sharp estimate at θ = 2/p to every admissible θ with one
constant. The additive mass term keeps its original coefficient ε. -/
theorem sharp_from_two_div {F : GasEnergies} {p C : ℝ} (hp : 3 < p) (hC : 0 < C)
    (hchain : WeakPowerComparison) (hbase : SharpTSGAEstimate F p (2 / p) C) :
    ∃ C' > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ → SharpTSGAEstimate F p θ C' := by
  let K := (4 : ℝ) ^ p + 1
  have hfour : 0 < (4 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have hK : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨C * K, mul_pos hC (by linarith), ?_⟩
  intro θ _ _ hpθ D S T G hD hroot hg φ hφ ε hε
  obtain ⟨U, hU, hcontrol⟩ := endpoint_gradient hchain (by linarith : 0 < p) hpθ hD hroot hg
  obtain ⟨hlocal, herr⟩ := hbase D S U G hU hroot hg φ hφ ε hε
  refine ⟨hlocal, herr.trans ?_⟩
  let w := ε ^ (2 * p - 1)
  have hw : 0 < w := Real.rpow_pos_of_pos hε _
  let u := ∫ x, matrixGradNorm U x ^ p
  let t := ∫ x, matrixGradNorm T x ^ p
  let g := ∫ x, matrixGradNorm G x ^ p
  let s := ∫ x, matrixGradNorm S x ^ 2
  let v := (∫ x, D.charge x * φ.hessianNorm x ^ p) +
    ∫ x in φ.active, ‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p
  have ht : 0 ≤ t := integral_nonneg fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hs : 0 ≤ s := integral_nonneg fun x => sq_nonneg (matrixGradNorm S x)
  have hv : 0 ≤ v := add_nonneg
    (integral_nonneg fun x => mul_nonneg (D.charge_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
    (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  have hb : u + g ≤ K * (t + g) := by dsimp [K]; change u ≤ _ * (g + t) at hcontrol; linarith
  have hCK : C ≤ C * K := by nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hK)]
  have hkin := mul_le_mul_of_nonneg_right hCK
    (show 0 ≤ (1 + ε) / ε * s by positivity)
  have hphase := mul_le_mul_of_nonneg_right hCK (show 0 ≤ v / w by positivity)
  have hbulk := mul_le_mul_of_nonneg_left hb (div_nonneg hC.le hw.le)
  unfold tsgaError
  change _ + C * (1+ε) / ε * s + C / w * u + C / w * v + C / w * g ≤
    _ + (C*K) * (1+ε) / ε * s + (C*K) / w * t + (C*K) / w * v + (C*K) / w * g
  simp only [div_eq_mul_inv] at hkin hphase hbulk ⊢
  linarith only [hkin, hphase, hbulk]

end TSGA.Localization
