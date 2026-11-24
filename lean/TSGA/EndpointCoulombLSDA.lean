import TSGA.EndpointIntegration
import TSGA.UEGEndpointInterpolation

/-! # LSDA under a fractional endpoint modulus for the uniform gas -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW

/-- The LSDA estimate under a power-law spin-flip bound. -/
theorem CoulombModelInputs.lsda_of_power_endpoint {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}
    (P : CoulombModelInputs μ ι η) {α E : ℝ} (hα : α ∈ Set.Icc (1/3 : ℝ) 1)
    (hE : 0 ≤ E) (endpoint : UEGPowerEndpointBound η α E) {p θ : ℝ}
    (hp : 3 < p) (hlo : 2/p ≤ θ) (hhi : θ < 1) :
    ∃ C > 0, LSDAEstimate (referenceEnergies energy η) (fun _ => True) p θ (endpointBulkExponent p θ α) C := by
  obtain ⟨K,⟨L⟩⟩ := P.gas.2
  have ha : 0 < α := by linarith [hα.1]
  have hp₀ : 0 < p := by linarith
  have hθ : 0 < θ := (div_pos (by norm_num : (0:ℝ)<2) hp₀).trans_le hlo
  have hpθ : 2 ≤ p*θ := by simpa only [mul_comm θ p] using (div_le_iff₀ hp₀).mp hlo
  obtain ⟨J,hJ,bound⟩ := L.ueg_small_ball_of_power_endpoint P.fock.oneBody P.difference endpoint hE ha hα.2 hθ hhi.le
  exact P.lsda_of_endpoint_tile_bound L hp hθ hhi.le ha hpθ hJ.le (@bound)

end TSGA.ManyBody
