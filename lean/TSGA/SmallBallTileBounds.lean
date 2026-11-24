import TSGA.ActualTileAssembly
import TSGA.CoulombFrozenTile

/-! # Bounds uniform in the dilation and frame of a small tile -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Set Metric
open scoped ComplexOrder

def actualSmallTaper (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (side : CutoffSide) {ε : ℝ}
    (he : 0 < ε) (hle : ε < 1) (q c : Position) (i : ℝ × O.Frames) : SpiralTaper (closedBall c (3*ε⁻¹)) :=
  comparisonTaper (actualTiles O frames η side he hle) q c _ (actualTiles_supported O frames η hs side he hle c) i

theorem actualSmallTaper_bounds (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (side : CutoffSide) {ε a : ℝ}
    (he : 0 < ε) (hle : ε < 1) (q c : Position) (i : ℝ × O.Frames)
    (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients) (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) :
    let t := actualSmallTaper O frames η hs side he hle q c i
    let Ω := closedBall c (3*ε⁻¹)
    LocallyLipschitz (fun x => √(t.shape x)) ∧ Continuous t.shape ∧ Integrable t.shape ∧
      (∫ x, t.shape x) ≤ (ε⁻¹)^3 ∧ ∃ g : Position → Position,
        (∀ j, WeakPartialOn univ j (fun x => √(t.shape x)) (fun x => g x j)) ∧
        Integrable (Ω.indicator fun x => ‖g x‖^2) ∧ (∫ x in Ω, ‖g x‖^2) ≤ a*(ε⁻¹)^2 := by
  intro t Ω
  let d := tileDilation i.1
  let L := tileSideLength side ε⁻¹
  let n := smoothedIndicator (tetrahedron (d*L)) η d
  let U := O.frame i.2
  have hd : 0 < d := tileDilation_pos _
  have hL : 0 < L := tileSideLength_pos side he hle
  have he' := inv_pos.mpr he
  have vol := tetrahedron_volume (mul_pos hd hL)
  have shape : t.shape = fun x => n (U (x-c)) := by
    funext x; simp [t, actualSmallTaper, comparisonTaper, actualTiles, actualTileShape, n, U, L, d]
  have rigid : MeasurePreserving (fun x => U (x-c)) volume volume :=
    U.measurePreserving.comp (measurePreserving_sub_right volume c)
  have iso : Isometry (fun x : Position => U (x-c)) := U.isometry.comp (Isometry.of_dist_eq fun x y => by simp [dist_eq_norm, sub_sub_sub_cancel_right])
  obtain ⟨A,_,lip⟩ := smoothedRootLipschitz sob η
  have hlip := (lip _ (tetrahedron_open (d*L)).measurableSet hd).comp iso.lipschitzWith
  have hroot : LocallyLipschitz (fun x => √(t.shape x)) := shape ▸ hlip.locallyLipschitz
  have hc : Continuous t.shape := by
    have eq : t.shape = fun x => (√(t.shape x))^2 := funext fun x => (Real.sq_sqrt (t.range x).1).symm
    rw [eq]; exact hroot.continuous.pow 2
  have mass : (∫ x, t.shape x) = regionVolume (tetrahedron (d*L)) := by
    rw [shape,integral_sub_right_eq_self (fun z => n (U z)) c,
      U.measurePreserving.integral_comp U.toHomeomorph.measurableEmbedding n]
    exact tile_cutoff_mass η (mul_pos hd hL) hd
  have fi : Integrable t.shape := Integrable.of_integral_ne_zero (mass.trans_ne (tetrahedron_volume_pos (mul_pos hd hL)).ne')
  have dmax : d ≤ 3/2 := (tileDilation_mem i.1).2
  have lmax : L ≤ ε⁻¹ := tileSideLength_le side _
  have vbound : (∫ x, t.shape x) ≤ (ε⁻¹)^3 := by
    rw [mass,vol]
    have h := pow_le_pow_left₀ (mul_pos hd hL).le (mul_le_mul dmax lmax hL.le (by norm_num)) 3
    nlinarith only [h, pow_nonneg he'.le 3]
  obtain ⟨h,weak,hLp,fish⟩ := area (d*L) d (mul_pos hd hL) hd
  let g := fun x => U.symm (h (U (x-c)))
  have hg : (fun x => ‖g x‖^2) = fun x => ‖h (U (x-c))‖^2 := by simp [g]
  have hi : Integrable fun x => ‖g x‖^2 := by
    rw [hg]; exact rigid.integrable_comp_of_integrable (hLp.integrable_norm_pow (p := 2) (by decide))
  refine ⟨hroot,hc,fi,vbound,g,?_,hi.indicator measurableSet_closedBall,?_⟩
  · rw [shape]; exact W.rigid weak U c
  · apply (setIntegral_le_integral hi (ae_of_all _ fun _ => sq_nonneg _)).trans
    rw [hg,integral_sub_right_eq_self (fun z => ‖h (U z)‖^2) c,
      U.measurePreserving.integral_comp U.toHomeomorph.measurableEmbedding (fun x => ‖h x‖^2)]
    apply fish.trans
    rw [vol]
    have eq : a*((d*L)^3/24)/((d*L)*d) = (d/24)*(a*L^2) := by field_simp [hd.ne',hL.ne']
    rw [eq]
    apply (mul_le_of_le_one_left (mul_nonneg ha (sq_nonneg _)) (by linarith only [dmax])).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le lmax 2) ha

theorem SpiralTaper.kinetic_le_ball {Ω : Set Position} (t : SpiralTaper Ω) {S : MatrixGradient}
    (hs : MeasurableSet Ω) (hi : Integrable (kineticDensity S)) (fi : Continuous t.shape) :
    (∫ x, t.shape x*kineticDensity S x) ≤ ∫ x in Ω, kineticDensity S x := by
  rw [← integral_indicator hs]
  have kin := window_product_integrable t.range fi.aemeasurable hi
  refine integral_mono kin (hi.indicator hs) fun x => ?_
  by_cases hx : x ∈ Ω
  · rw [indicator_of_mem hx]
    exact mul_le_of_le_one_left (sq_nonneg _) (t.range x).2
  · simp [t.outside x hx,hx]

end TSGA.ManyBody
