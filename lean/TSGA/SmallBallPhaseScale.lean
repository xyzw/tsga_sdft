import TSGA.SmallBallMatrices
import TSGA.SmallBallPhase
import TSGA.BallDensityTransfer

/-! # Phase error for the representative chosen on a small ball -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization Metric

theorem SmallBallScale.phase_input {D N : Density} {φ : Phase} {G S T : MatrixGradient}
    {p θ ε Cmat Cvec : ℝ} {c : Position} (s : SmallBallScale N (3*ε⁻¹) c)
    (e : N.matrix =ᵐ[volume] D.matrix) (reg : DensityRegular D p θ S T) (phase : PhaseAdmissible D p φ G)
    (M : MatrixSobolevMorrey p Cmat) (V : VectorMorreyOnBalls p Cvec)
    (hp : 3 < p) (he : 0 < ε) (he' : ε ≤ 1) (hCmat : 0 ≤ Cmat) (hCvec : 0 ≤ Cvec)
    (hroot : Continuous (N.power (1/p))) :
    let d := s.omega (1/p)/s.r^(1/p)
    RepresentativeTileInput D φ G p ε (smallBallPhaseConstant p Cmat Cvec) (3*ε⁻¹) c
      (smallBallPhaseCost s.r d ε (tilePhaseOscillation φ c ε⁻¹) (φ.grad c)) := by
  intro d
  have hp₀ : 0 < p := by linarith
  have ha : 0 < 1/p := one_div_pos.mpr hp₀
  have regN := densityRegular_of_ae e.symm reg
  have phaseN := phaseAdmissible_of_ae e.symm phase
  refine ⟨N,e,smallBallPhase_input M V hp he he' hCmat hCvec phaseN hroot
    (massDensity_integrable regN phaseN) c s.r_nonneg
    (div_nonneg (s.omega_nonneg _ ha) (Real.rpow_nonneg s.r_nonneg _))
    (s.root_ratio_le hp₀) s.comparable ?_⟩
  obtain ⟨x,hx,y,hy,hm⟩ := s.omega_max _ ha
  refine ⟨x,hx,y,hy,Eq.trans ?_ hm⟩
  by_cases h : s.r = 0
  · have cap := s.omega_le _ ha
    rw [h,Real.zero_rpow ha.ne',mul_zero] at cap
    rw [h,Real.zero_rpow ha.ne',zero_mul]
    exact (le_antisymm cap (s.omega_nonneg _ ha)).symm
  · exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos (s.r_nonneg.lt_of_ne' h) _).ne'

theorem SmallBallScale.phase_bound {D N : Density} {φ : Phase} {G S T : MatrixGradient}
    {p θ ε Cmat Cvec : ℝ} {c : Position} (s : SmallBallScale N (3*ε⁻¹) c)
    (e : N.matrix =ᵐ[volume] D.matrix) (reg : DensityRegular D p θ S T) (phase : PhaseAdmissible D p φ G)
    (M : MatrixSobolevMorrey p Cmat) (V : VectorMorreyOnBalls p Cvec)
    (hp : 3 < p) (he : 0 < ε) (he' : ε ≤ 1) (hCmat : 0 ≤ Cmat) (hCvec : 0 ≤ Cvec)
    (hroot : Continuous (N.power (1/p))) :
    let d := s.omega (1/p)/s.r^(1/p)
    let R := 3*ε⁻¹
    smallBallPhaseCost s.r d ε (tilePhaseOscillation φ c ε⁻¹) (φ.grad c) ≤
      tileConstant p (smallBallPhaseConstant p Cmat Cvec) *
        (ε*bulkAverage D φ R c + ballAverage R (phaseDensity D φ G p) c / ε^(2*p-1)) := by
  have h := s.phase_input e reg phase M V hp he he' hCmat hCvec hroot
  apply h.bound hp he he' _ (by positivity) reg.charge_L1 (massDensity_integrable reg phase) phase
  unfold smallBallPhaseConstant
  linarith only [le_max_left (4:ℝ) (max (ballVolume 1*3^p*Cmat) (2*(ballVolume 1*3^p*Cvec)))]

end TSGA.ManyBody
