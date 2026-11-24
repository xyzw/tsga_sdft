import TSGA.BallDensityRepresentative
import TSGA.LocalErrorTerms

/-! # Changing the density representative in a Coulomb tile estimate -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization

private theorem gradient_congr {U : Set Position} {M N : Position → SpinMatrix}
    {G : MatrixGradient} (h : M =ᵐ[volume] N) (hg : IsMatrixGradientOn U M G) :
    IsMatrixGradientOn U N G := by
  intro i j k
  have he : (fun x => M x j k) =ᵐ[volume.restrict U] (fun x => N x j k) :=
    ae_restrict_of_ae (h.mono fun x hx => congrArg (fun A : SpinMatrix => A j k) hx)
  obtain ⟨hm, hd, hw⟩ := hg i j k
  refine ⟨LocallyIntegrableOn.congr he hm, hd, ?_⟩
  intro ψ hψ hc hs
  exact (integral_congr_ae (he.symm.mono fun x hx => congrArg (_ • ·) hx)).trans (hw ψ hψ hc hs)

theorem densityRegular_of_ae {D N : Density} {p θ : ℝ} {S T : MatrixGradient}
    (e : D.matrix =ᵐ[volume] N.matrix) (h : DensityRegular D p θ S T) :
    DensityRegular N p θ S T :=
  ⟨h.charge_L1.congr (densityCharge_ae_congr e), (memLp_congr_ae (densityCharge_ae_congr e)).mp h.charge_L2,
   gradient_congr (densityPower_ae_congr e _) h.sqrt_gradient, h.sqrt_L2,
   gradient_congr (densityPower_ae_congr e _) h.theta_gradient, h.theta_Lp⟩

theorem phaseAdmissible_of_ae {D N : Density} {φ : Phase} {p : ℝ} {G : MatrixGradient}
    (e : D.matrix =ᵐ[volume] N.matrix) (h : PhaseAdmissible D p φ G) :
    PhaseAdmissible N p φ G := by
  have hc := densityCharge_ae_congr e
  refine ⟨h.regular, ?_, h.kinetic.congr (hc.mul Filter.EventuallyEq.rfl),
    h.curvature.congr (hc.mul Filter.EventuallyEq.rfl), h.root_weighted⟩
  intro x hx
  obtain ⟨r, hr, hsub, hgrad, hentry, hG⟩ := h.root_regular x hx
  have ep := densityPower_ae_congr e (1/p)
  refine ⟨r, hr, hsub, gradient_congr ep hgrad, ?_, hG⟩
  intro j k
  exact (memLp_congr_ae (ae_restrict_of_ae (ep.mono fun y hy =>
    congrArg (fun A : SpinMatrix => A j k) hy))).mp (hentry j k)

theorem regimeHyp_of_ae {D N : Density} {mode : BulkRegime} {ν p : ℝ} {G : MatrixGradient}
    (e : D.matrix =ᵐ[volume] N.matrix) (h : RegimeHyp mode ν D G p) :
    RegimeHyp mode ν N G p := by
  cases mode with
  | general => trivial
  | minority =>
    filter_upwards [h, e, densityCharge_ae_congr e] with x hx hm hc
    simpa only [← hm, ← hc] using hx
  | globalRoot => exact ⟨gradient_congr (densityPower_ae_congr e _) h.1, h.2⟩

end TSGA.ManyBody
