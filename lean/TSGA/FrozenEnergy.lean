import TSGA.LocalizationAssembly
import TSGA.SSWDomain

/-! # Frozen SSW energy of translated finite tiles -/

noncomputable section

namespace TSGA.Localization

open MeasureTheory

/-- The same tapered finite systems and weights as in `AveragedTiles.energy`,
with a constant spin matrix and the linear phase `q · x`. -/
def AveragedTiles.frozenEnergy (T : AveragedTiles) (F : GasEnergies)
    (B : SpinMatrix) (q c : Position) : ℝ := by
  letI := T.space
  exact ∫ i, T.weight i * F.energy (SSW.cutoffSpiral (fun x => T.shape i (c - x)) B q) ∂T.measure

def AveragedTiles.FrozenIntegrable (T : AveragedTiles) (F : GasEnergies)
    (B : SpinMatrix) (q c : Position) : Prop := by
  letI := T.space
  exact Integrable (fun i => T.weight i *
    F.energy (SSW.cutoffSpiral (fun x => T.shape i (c - x)) B q)) T.measure

end TSGA.Localization
