import TSGA.SectorFourierDensity
import TSGA.SpinFockWave

/-! # The Fourier transform of a doubled-spin wave -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

/-- The Fourier transform of the doubled-spin amplitudes, with the same angular-frequency
convention as the original wave. -/
def SectorFourierTransform.splitAmplitude (F : SectorFourierTransform) {n : ℕ} (ψ : Wave n)
    (U : SpinSplitter) (t : Fin n → SplitSpin) : Space n → ℂ :=
  F.transform n ((ψ.splitValue_L2 U t).toLp (ψ.splitValue U t))

/-- A constant spin tensor commutes with the scalar Fourier transform, including on waves
whose Fourier transform is only defined as an L² equivalence class. -/
theorem SectorFourierTransform.splitAmplitude_eq (F : SectorFourierTransform) {n : ℕ}
    (ψ : Wave n) (U : SpinSplitter) (t : Fin n → SplitSpin) :
    F.splitAmplitude ψ U t =ᵐ[volume] fun p =>
      ∑ s, sectorSpinTensor n (fun _ => U) t s * F.amplitude ψ s p :=
  (ψ.split_transform U (F.transform n).toLinearMap).mono fun _ hp => hp t

end TSGA.ManyBody
