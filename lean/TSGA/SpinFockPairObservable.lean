import TSGA.SectorPairObservable
import TSGA.SpinFockWave

/-! # Pullback of whole-sector pair observables through a spin splitting -/

noncomputable section
namespace TSGA.ManyBody
open Matrix MeasureTheory
open scoped Kronecker

theorem Wave.split_pairObservable {n : ℕ} (ψ : Wave (n+2)) (U : SpinSplitter) (hU : U.Isometry)
    (b : PairSpace → ℂ) (A : PairSpinMatrix) :
    sectorPairObservable (ψ.split U hU).value b (retainedPairTest A) =
      sectorPairObservable ψ.value b (star (U.active ⊗ₖ U.active) * A * (U.active ⊗ₖ U.active)) := by
  unfold sectorPairObservable
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  let z := fun p : PairSpin × Spins n => ψ.value (Fin.cons p.1.1 (Fin.cons p.1.2 p.2)) x
  let D := (U ⊗ₖ U) ⊗ₖ sectorSpinTensor n (fun _ => U)
  have hw : (fun p : (SplitSpin × SplitSpin) × (Fin n → SplitSpin) =>
      (ψ.split U hU).value (Fin.cons p.1.1 (Fin.cons p.1.2 p.2)) x) = D *ᵥ z := by
    funext p
    exact split_vector_cons_cons U (fun t => ψ.value t x) p.1.1 p.1.2 p.2
  simpa only [hw] using congrArg ((b (x 0,x 1)) * ·) (U.first_pair_form hU n A z)

end TSGA.ManyBody
