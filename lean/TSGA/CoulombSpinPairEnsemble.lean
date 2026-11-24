import TSGA.CoulombSpinPair
import TSGA.SectorSpectralResolution

/-! # The Coulomb pair matrix under countable mixtures -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory

theorem MixedState.coulombPairMatrix_flatten (Γ : MixedState) (states : ℕ → MixedState)
    (hN : Summable (fun k => Γ.weight k * (states k).particleMean))
    (hT : Summable (fun k => Γ.weight k * (states k).kinetic))
    (hV : Summable (fun k => Γ.weight k * (states k).interaction)) :
    HasSum (fun k => Γ.weight k • (states k).coulombPairMatrix)
      (Γ.flatten states hN hT hV).coulombPairMatrix := by
  let Λ := Γ.flatten states hN hT hV
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  let F := fun s : PureState => s.coulombPairMatrix i j
  have e (Δ : MixedState) : (∑' k, Δ.weight k • F (Δ.component k)) = Δ.coulombPairMatrix i j :=
    (Pi.hasSum.mp (Pi.hasSum.mp Δ.coulombPairMatrix_hasSum i) j).tsum_eq
  have h := Γ.flatten_summable_of_bound states hN hT hV F 1 (fun s => by
    rw [one_mul]
    exact (s.norm_coulombPairMatrix_entry i j).trans
      (le_add_of_nonneg_left (add_nonneg (Nat.cast_nonneg _) s.kinetic_nonneg)))
  have eqn := Γ.flatten_expect states hN hT hV F h
  change (∑' k, Λ.weight k • F (Λ.component k)) = _ at eqn
  simp only [e] at eqn
  change HasSum (fun k => Γ.weight k • (states k).coulombPairMatrix i j) (Λ.coulombPairMatrix i j)
  rw [eqn]
  apply Summable.hasSum
  apply hV.of_norm_bounded
  intro k
  rw [norm_smul,Real.norm_of_nonneg (Γ.weight_nonneg k)]
  exact mul_le_mul_of_nonneg_left ((states k).norm_coulombPairMatrix_entry i j) (Γ.weight_nonneg k)

end TSGA.ManyBody
