import TSGA.CoulombUpperBoundaryEnergy
import TSGA.CoulombTileUnfolding
import TSGA.CoulombShiftIntegrability

/-! # Absolute integrability of energies over tile centers and frames -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW Set Metric TSGA.Localization
open scoped ComplexOrder

/-- Joint Borel measurability of the action of the frame law. -/
def MeasurableFrameAction (O : TileOrientationLaw) : Prop :=
  Measurable (fun p : O.Frames × Position => O.frame p.1 p.2)

private theorem center_window_field (f w : Position → ℝ) (M : SpinMatrix) (q : Position) :
    cutoffSpiral (fun x => f x*w x) M q = fun x => (w x : ℂ) • cutoffSpiral f M q x := by
  funext x
  simp only [cutoffSpiral,smul_smul,Complex.ofReal_mul,mul_comm (f x : ℂ)]

private theorem energy_window_borel {P : Type*} [MeasurableSpace P] (borel : LevyLiebBorel)
    (f : Position → ℝ) (M : SpinMatrix) (q : Position)
    (hm : ∀ i j, Measurable (fun x => cutoffSpiral f M q x i j))
    (hi : ∀ i j, Integrable (fun x => cutoffSpiral f M q x i j))
    (w : P → Position → ℝ) (hw : Measurable (fun z : P × Position => w z.1 z.2))
    (unit : ∀ p x, w p x ∈ Icc 0 1) :
    Measurable (fun p => energy (cutoffSpiral (fun x => f x*w p x) M q)) := by
  simp_rw [center_window_field]
  let D := cutoffSpiral f M q
  have m (i j : Fin 2) : Measurable (fun z : P × Position => ((w z.1 z.2 : ℂ) • D z.2) i j) :=
    (Complex.measurable_ofReal.comp hw).mul ((hm i j).comp measurable_snd)
  apply measurable_coulomb_energy_family borel _ m
  intro p i j
  apply memLp_one_iff_integrable.mpr
  apply (hi i j).norm.mono' ((m i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards with x
  change ‖(w p x : ℂ) * D x i j‖ ≤ ‖D x i j‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (unit p x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (unit p x).2

set_option maxHeartbeats 800000 in
/-- On a fixed pair of scales all center energies have a single integrable
majorant. The outer charge and inner window have bounded supports, and the
direct energy of the parent charge supplies the uniform lower bound. -/
theorem coulomb_center_integrals (H : FiniteEnergyInputs) (W : WindowSobolevRules)
    (sob : SobolevDifferenceQuotients) (borel : LevyLiebBorel)
    (O : TileOrientationLaw) (hmO : MeasurableFrameAction O) (haar : CubeFrameInvariant O)
    {Ω : Set Position} (hop : IsOpen Ω) (hbd : Bornology.IsBounded Ω) (χ : Mollifier)
    {d₀ : ℝ} (hd₀ : 0 < d₀) (η : Mollifier) {b d : ℝ} (hd : 0 < d) (hdb : d < b)
    {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    let f := smoothedIndicator Ω χ d₀
    let E := fun R z => energy (cutoffSpiral (fun x => f x*centeredWindow η (b-d) d R z x) M q)
    (∀ R, Integrable (E R)) ∧ Integrable (fun u => ∫ z, E (O.frame u) z) O.law ∧
      Integrable (fun v => ∫ τ, ∑' p : LatticeTile, energy (cutoffSpiral
        (fun x => f x*latticeWindow b d η p (O.frame v x-τ)) M q) ∂latticeShiftMeasure b) O.law := by
  classical
  intro f E
  let w := smoothedIndicator (tetrahedron (b-d)) η d
  let ξ := centeredWindow η (b-d) d
  let D := cutoffSpiral f M q
  have source := cutoffSpiral_source_data hop.measurableSet hbd χ hd₀ M q
  obtain ⟨hm,hi,_,hdir⟩ := source
  obtain ⟨g,dg,gf⟩ := smoothedIndicator_sqrt_sobolev sob hop.measurableSet hbd.measure_lt_top.ne χ hd₀
  have hχ : Integrable (Ω.indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff hop.measurableSet).2 (integrableOn_const hbd.measure_lt_top.ne)
  have fi : Integrable f := hχ.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (χ.scaled_integrable hd₀)
  have hscale := sub_pos.mpr hdb
  have wm : Measurable w := measurable_smoothedTetrahedron η _ hd
  have unit (R : Position ≃ₗᵢ[ℝ] Position) (z x : Position) : ξ R z x ∈ Icc 0 1 :=
    smoothedIndicator_bounds _ η hd _
  obtain ⟨L,lower⟩ := windowed_field_energy_floor D hdir
  obtain ⟨U,upper⟩ := H.centered_window_bounded_above W sob η hscale hd
    (smoothedIndicator_bounds Ω χ hd₀) fi g gf dg hM q
  obtain ⟨A,hA⟩ := compact_smoothedRegion hbd χ hd₀
  obtain ⟨B,hB⟩ := compact_smoothedRegion (isBounded_closedBall.subset (tetrahedron_subset hscale)) η hd
  let T := closedBall (0:Position) (A+B)
  let bound := T.indicator (fun _ => |L|+|U|)
  have Tm : MeasurableSet T := measurableSet_closedBall
  have bI : Integrable bound := (integrable_indicator_iff Tm).2
    (integrableOn_const isBounded_closedBall.measure_lt_top.ne)
  have normbound (R : Position ≃ₗᵢ[ℝ] Position) (z : Position) : ‖E R z‖ ≤ bound z := by
    by_cases hz : z ∈ T
    · rw [show bound z = |L|+|U| from indicator_of_mem hz _,Real.norm_eq_abs,abs_le]
      have hlow := lower (ξ R z) (wm.comp (R.continuous.measurable.comp (measurable_id.sub_const z)))
        (fun x => ⟨(unit R z x).1,(unit R z x).2.trans (by norm_num)⟩)
      change -L ≤ energy (fun x => (ξ R z x : ℂ) • cutoffSpiral f M q x) at hlow
      rw [← center_window_field] at hlow
      have hu : E R z ≤ U := upper R z
      exact ⟨by linarith only [hlow,le_abs_self L,abs_nonneg U],by linarith only [hu,le_abs_self U,abs_nonneg L]⟩
    · have zero (x : Position) : f x*ξ R z x = 0 := by
        by_contra hn
        have hx := hA x (left_ne_zero_of_mul hn)
        have hy := hB (R (x-z)) (right_ne_zero_of_mul hn)
        rw [R.norm_map] at hy
        apply hz
        apply mem_closedBall_zero_iff.mpr
        calc
          ‖z‖ = ‖x-(x-z)‖ := by simp
          _ ≤ ‖x‖+‖x-z‖ := norm_sub_le _ _
          _ ≤ A+B := add_le_add hx hy
      have vacuum : cutoffSpiral (fun x => f x*ξ R z x) M q = 0 := by
        funext x
        simp only [cutoffSpiral,zero,Complex.ofReal_zero,zero_smul,Pi.zero_apply]
      change ‖energy (cutoffSpiral (fun x => f x*ξ R z x) M q)‖ ≤ _
      rw [vacuum,energy_vacuum,norm_zero,show bound z = 0 from indicator_of_notMem hz _]
  have fixed (R : Position ≃ₗᵢ[ℝ] Position) : Integrable (E R) := by
    apply bI.mono' _ (ae_of_all _ (normbound R))
    exact (energy_window_borel borel f M q hm hi (ξ R)
      (wm.comp (R.continuous.measurable.comp (measurable_snd.sub measurable_fst))) (unit R)).aestronglyMeasurable
  have joint : Measurable (fun y : O.Frames × Position => E (O.frame y.1) y.2) :=
    energy_window_borel borel f M q hm hi (fun y : O.Frames × Position => ξ (O.frame y.1) y.2)
      (wm.comp (hmO.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.sub (measurable_snd.comp measurable_fst))))) (fun y => unit _ _)
  have angular : Integrable (fun u => ∫ z, E (O.frame u) z) O.law := by
    have meas : AEStronglyMeasurable (fun u => ∫ z, E (O.frame u) z) O.law :=
      joint.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    have cI : Integrable (fun _ : O.Frames => ∫ z, bound z) O.law := integrable_const _
    apply cI.mono' meas
    exact ae_of_all _ fun u => norm_integral_le_of_norm_le (f := E (O.frame u)) bI
      (ae_of_all _ (normbound (O.frame u)))
  refine ⟨fixed,angular,?_⟩
  exact (coulomb_unfold_lattice_tiles_integrable O haar η (hd.trans hdb) d f M q fixed angular).1

end TSGA.ManyBody
