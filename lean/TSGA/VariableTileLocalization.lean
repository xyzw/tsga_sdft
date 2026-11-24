import TSGA.CoulombCubicVariance

/-! # Localization of spatially varying spin densities on the physical lattice -/

noncomputable section
namespace TSGA.ManyBody

open SSW MeasureTheory Set

/-- Minimize the state-level Graf–Schenker inequality for the original
density, keeping the full local spin density inside every tile. -/
theorem coulomb_variable_lower_localization {η : Mollifier} {O : TileOrientationLaw} {C : ℝ}
    (graf : SmearedGrafSchenker η O C) (F : Position → SpinMatrix)
    (rep : ∃ Γ, feasible F Γ) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hscale : 2*C*δ ≤ ℓ) :
    let V := regionVolume (tetrahedron ℓ)
    let field := fun u z x => (centeredWindow η ℓ δ (O.frame u) z x : ℂ) • F x
    (∀ᵐ u ∂O.law, Integrable (fun z => energy (field u z) / V)) →
    Integrable (fun u => ∫ z, energy (field u z) / V) O.law →
    (1-C*δ/ℓ)*(∫ u, ∫ z, energy (field u z) / V ∂volume ∂O.law) -
      C/ℓ*((1+δ⁻¹)*(∫ x, (F x).trace.re) + δ^3*(∫ x, (F x).trace.re^2)) ≤ energy F := by
  intro V field hc ho
  apply (le_sub_iff_add_le).2
  apply le_levyLieb rep
  intro Γ hΓ
  obtain ⟨s,hs,hsz,hsu,hbound⟩ := graf F Γ hΓ hℓ hδ hscale
  have center (u : O.Frames) (hu : ∀ᵐ z, feasible (field u z) (s u z))
      (hzu : Integrable (fun z => energy (field u z) / V))
      (hszu : Integrable (fun z => localStateEnergy (s u z) (field u z) / V)) :
      (∫ z, energy (field u z) / V) ≤ ∫ z, localStateEnergy (s u z) (field u z) / V := by
    apply integral_mono_ae hzu hszu
    filter_upwards [hu] with z hz
    exact div_le_div_of_nonneg_right (sub_le_sub_right (levyLieb_le hz) _) (tetrahedron_volume_pos hℓ).le
  have hmean := integral_mono_ae ho hsu (by
    filter_upwards [hs,hc,hsz] with u hu hzu hszu
    exact center u hu hzu hszu)
  have hfactor : 0 ≤ 1-C*δ/ℓ := sub_nonneg.mpr ((div_le_one hℓ).mpr (by linarith))
  have hin := mul_le_mul_of_nonneg_left hmean hfactor
  change _ ≤ localStateEnergy Γ F at hbound
  unfold localStateEnergy at hbound
  change (1-C*δ/ℓ)*(∫ u, ∫ z, localStateEnergy (s u z) (field u z) / V ∂volume ∂O.law) - _ ≤ _ at hbound
  linarith only [hin,hbound]

/-- Fixed-scale upper localization for the uncut density on all of space.
The skeleton is counted once per shift. The fluctuation of the total
charge is the direct energy left by the convex mixture. -/
theorem coulomb_variable_upper_localization (tensor : DisjointFockTensorization)
    (hlsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (O : TileOrientationLaw) (haar : CubeFrameInvariant O)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ Metric.closedBall 0 (1/100))
    {b d : ℝ} (hd : 0 < d) (hscale : d ≤ b/2)
    (F : Position → SpinMatrix)
    (hi : ∀ i j, Integrable (fun x => F x i j))
    (direct : Integrable (directKernel (fun x => (F x).trace.re) (fun x => (F x).trace.re)) pairVolume) :
    let μ := latticeShiftMeasure b
    let J := fun (w : Position → ℝ) => energy (fun x => (w x : ℂ) • F x)
    let sk := fun u τ => energy (latticeBlockDensity b d η (O.frame u) F τ none)
    let fluct := fun u => ∫ τ, hartree (fun x =>
      (latticeTotalWindow b d η (O.frame u x-τ)-1)*(F x).trace.re) ∂μ
    (∀ R : Position ≃ₗᵢ[ℝ] Position, Integrable (fun z => J (centeredWindow η (b-d) d R z))) →
    Integrable (fun u => ∫ z, J (centeredWindow η (b-d) d (O.frame u) z)) O.law →
    (∀ᵐ u ∂O.law, ∀ᵐ τ ∂μ, ∀ p, ∃ Γ, feasible (latticeBlockDensity b d η (O.frame u) F τ p) Γ) →
    (∀ᵐ u ∂O.law, Integrable (sk u) μ) →
    Integrable (fun u => ∫ τ, sk u τ ∂μ) O.law →
    Integrable fluct O.law →
    energy F ≤ (∫ u, ∫ z, J (centeredWindow η (b-d) d (O.frame u) z) /
        regionVolume (tetrahedron b) ∂volume ∂O.law) +
      (∫ u, ∫ τ, sk u τ ∂μ ∂O.law) + ∫ u, fluct u ∂O.law := by
  intro μ J sk fluct hc ho rep skShift skFrame varFrame
  have hb : 0 < b := by linarith
  let cells := fun (u : O.Frames) (τ : Position) =>
    ∑' p : LatticeTile, J (fun x => latticeWindow b d η p (O.frame u x-τ))
  have unfolded := unfold_lattice_window_functional O haar η hb d J hc ho
  have fixed : ∀ᵐ u ∂O.law, energy F ≤
      ((∫ τ, cells u τ ∂μ) + ∫ τ, sk u τ ∂μ) + fluct u := by
    filter_upwards [rep,skShift] with u hrep hsk
    have ⟨summable,shift⟩ := lattice_window_series hb d η J hc (O.frame u)
    have hsum : latticeBlockEnergySum b d η (O.frame u) F = fun τ => sk u τ + cells u τ := rfl
    have h := coulomb_variable_lattice_shifts tensor hlsc hd hscale hs (O.frame u) F hi
      hrep summable (hsum ▸ hsk.add shift) direct
    change energy F ≤ (∫ τ, latticeBlockEnergySum b d η (O.frame u) F τ ∂μ) + fluct u at h
    rwa [hsum,integral_add hsk shift,add_comm (∫ τ, sk u τ ∂μ)] at h
  have cellsFrame : Integrable (fun u => ∫ τ, cells u τ ∂μ) O.law := unfolded.1
  have both : Integrable (fun u => (∫ τ, cells u τ ∂μ)+(∫ τ, sk u τ ∂μ)) O.law :=
    cellsFrame.add skFrame
  have avg := integral_mono_ae (integrable_const (energy F)) (both.add varFrame) fixed
  rw [integral_const,probReal_univ,one_smul] at avg
  calc
    energy F ≤ ∫ u, ((∫ τ, cells u τ ∂μ)+(∫ τ, sk u τ ∂μ))+fluct u ∂O.law := avg
    _ = (∫ u, (∫ τ, cells u τ ∂μ)+(∫ τ, sk u τ ∂μ) ∂O.law) + ∫ u, fluct u ∂O.law :=
      integral_add both varFrame
    _ = _ := by rw [integral_add cellsFrame skFrame]; exact congrArg (fun x => x+_+_) unfolded.2

end TSGA.ManyBody
