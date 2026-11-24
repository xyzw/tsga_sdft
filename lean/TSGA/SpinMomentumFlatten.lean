import TSGA.SpinMomentumEnsemble
import TSGA.SectorSpectralResolution

/-! # Momentum density of flattened Fock ensembles -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- Flattening a countable mixture preserves its one-body momentum marginal. -/
theorem mixedSpinMomentumProfile_flatten (Γ : MixedState) (states : ℕ → MixedState) (hN hT hV)
    (P : PureState → Position → SpinMatrix) (h : ∀ s, PureSpinMomentumDistribution s (P s)) :
    mixedSpinMomentumProfile (Γ.flatten states hN hT hV) P =ᵐ[volume]
      fun p => ∑' k, Γ.weight k • mixedSpinMomentumProfile (states k) P p := by
  let Λ := Γ.flatten states hN hT hV
  filter_upwards [mixedMomentum_summable_ae Λ P h] with p hp
  let f (n : ℕ × ℕ) :=
    (Γ.weight n.1 * (states n.1).weight n.2) • P ((states n.1).component n.2) p
  have hs : Summable f := Nat.pairEquiv.symm.summable_iff.mp hp
  calc
    _ = ∑' n, f n := Nat.pairEquiv.symm.tsum_eq _
    _ = _ := by rw [hs.tsum_prod]; simp only [f,mul_smul,tsum_const_smul'',mixedSpinMomentumProfile]

/-- A fixed spin contraction commutes with an absolutely summable momentum marginal. -/
theorem mixedSpinMomentumProfile_sandwich (Γ : MixedState) (P : PureState → Position → SpinMatrix)
    (h : ∀ s, PureSpinMomentumDistribution s (P s)) (S : SpinMatrix) :
    (fun p => ∑' k, Γ.weight k • (S * P (Γ.component k) p * star S)) =ᵐ[volume]
      fun p => S * mixedSpinMomentumProfile Γ P p * star S := by
  filter_upwards [mixedMomentum_summable_ae Γ P h] with p hp
  simpa only [mixedSpinMomentumProfile,Matrix.mul_smul, Matrix.smul_mul] using!
    ((hp.hasSum.mul_left S).mul_right (star S)).tsum_eq

/-- Assemble the componentwise geometric localizations before taking moments. -/
theorem mixedSpinMomentumProfile_flatten_localized (Γ : MixedState) (states : ℕ → MixedState)
    (hN hT hV) (P : PureState → Position → SpinMatrix)
    (h : ∀ s, PureSpinMomentumDistribution s (P s)) (S : SpinMatrix)
    (loc : ∀ k, mixedSpinMomentumProfile (states k) P =ᵐ[volume]
      fun p => S * P (Γ.component k) p * star S) :
    mixedSpinMomentumProfile (Γ.flatten states hN hT hV) P =ᵐ[volume]
      fun p => S * mixedSpinMomentumProfile Γ P p * star S := by
  filter_upwards [mixedSpinMomentumProfile_flatten Γ states hN hT hV P h,
    ae_all_iff.mpr loc,mixedSpinMomentumProfile_sandwich Γ P h S] with p h₁ hp h₂
  rw [h₁, ← h₂]
  exact tsum_congr fun k => by rw [hp k]

theorem mixedPosition_flatten_localized (Γ : MixedState) (states : ℕ → MixedState)
    (hN hT hV) (S : SpinMatrix)
    (loc : ∀ k, (states k).matrixDensity =ᵐ[volume]
      fun x => S * (Γ.component k).matrixDensity x * star S) :
    (Γ.flatten states hN hT hV).matrixDensity =ᵐ[volume]
      fun x => S * Γ.matrixDensity x * star S := by
  filter_upwards [Γ.flatten_density states hN hT hV,ae_all_iff.mpr loc,
    Γ.density_summable] with x hflat hloc hx
  have hs : HasSum (fun k => Γ.weight k • (Γ.component k).matrixDensity x)
      (Γ.matrixDensity x) :=
    Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => (hx i j).hasSum
  have hsum := (hs.mul_left S).mul_right (star S)
  ext i j
  rw [hflat i j, ← (Pi.hasSum.mp (Pi.hasSum.mp hsum i) j).tsum_eq]
  apply tsum_congr
  intro k
  simp only [hloc k, Matrix.mul_smul, Matrix.smul_mul,Matrix.smul_apply,Complex.real_smul]

end TSGA.ManyBody
