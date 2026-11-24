import TSGA.CoulombModelInputs
import TSGA.VariableTileLocalization
import TSGA.RepresentableTileDensity

/-! # Lower localization for all admissible lengths and widths

The full-size tetrahedra fill each lattice cell. Unfolding their centers
restores the sum over all 24 labels and lattice translations in Theorem 4.12.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW Set Metric TSGA.Localization

/-- The lower cutoff smooths the full tetrahedron at width `δ`. -/
def lowerLatticeWindow (ℓ δ : ℝ) (η : Mollifier) (p : LatticeTile) (x : Position) : ℝ :=
  smoothedIndicator (tetrahedron ℓ) η δ (latticeChart ℓ p x)

theorem lowerLatticeWindow_centered (η : Mollifier) (b d : ℝ) (R : Position ≃ₗᵢ[ℝ] Position)
    (τ : Position) (p : LatticeTile) (x : Position) :
    lowerLatticeWindow b d η p (R x-τ) =
      centeredWindow η b d (R.trans (cubeFrame b p.2))
        (R.symm (latticeShift b p.1+τ+cubeLabelCenter b p.2)) x := by
  unfold lowerLatticeWindow centeredWindow
  congr 1
  rw [latticeChart_center]
  change cubeFrame b p.2 (R x-τ-latticeShift b p.1-cubeLabelCenter b p.2) = cubeFrame b p.2
    (R (x-R.symm (latticeShift b p.1+τ+cubeLabelCenter b p.2)))
  rw [map_sub R,R.apply_symm_apply]
  congr 1
  abel

theorem unfold_lower_lattice_windows (O : TileOrientationLaw) (haar : CubeFrameInvariant O)
    (η : Mollifier) {b : ℝ} (hb : 0 < b) (d : ℝ) (J : (Position → ℝ) → ℝ)
    (hc : ∀ R : Position ≃ₗᵢ[ℝ] Position, Integrable (fun z => J (centeredWindow η b d R z)))
    (ho : Integrable (fun v => ∫ z, J (centeredWindow η b d (O.frame v) z)) O.law) :
    Integrable (fun v => ∫ τ, ∑' p : LatticeTile, J (fun x => lowerLatticeWindow b d η p (O.frame v x-τ))
      ∂latticeShiftMeasure b) O.law ∧
    (∫ v, ∫ τ, ∑' p : LatticeTile, J (fun x => lowerLatticeWindow b d η p (O.frame v x-τ))
      ∂latticeShiftMeasure b ∂O.law) =
    ∫ v, ∫ z, J (centeredWindow η b d (O.frame v) z) /
      regionVolume (tetrahedron b) ∂volume ∂O.law := by
  let E := fun (R : Position ≃ₗᵢ[ℝ] Position) (z : Position) => J (centeredWindow η b d R z)
  let G := fun (v : O.Frames) (o : CubeOrientation) => ∫ z, E ((O.frame v).trans (cubeFrame b o)) z
  have fixed (v : O.Frames) :
      (∫ τ, (∑' p : LatticeTile, J (fun x => lowerLatticeWindow b d η p (O.frame v x-τ)))
        ∂latticeShiftMeasure b) = (b^3)⁻¹*(∑ o, G v o) := by
    let R := O.frame v
    let g := fun (o : CubeOrientation) (z : Position) => E (R.trans (cubeFrame b o)) (R.symm (z+cubeLabelCenter b o))
    have hg (o) : Integrable (g o) :=
      ((R.symm.measurePreserving.integrable_comp_emb R.symm.toHomeomorph.measurableEmbedding).2
        (hc (R.trans (cubeFrame b o)))).comp_add_right _
    have hInt (o) : (∫ z, g o z) = G v o := by
      calc
        _ = ∫ z, E (R.trans (cubeFrame b o)) (R.symm z) :=
          integral_add_right_eq_self (fun z => E (R.trans (cubeFrame b o)) (R.symm z)) _
        _ = G v o := R.symm.measurePreserving.integral_comp R.symm.toHomeomorph.measurableEmbedding _
    rw [latticeShiftMeasure,integral_smul_measure]
    simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (pow_nonneg hb.le 3),smul_eq_mul]
    congr 1
    calc
      _ = ∫ τ in latticeCube b 0, ∑' p : LatticeTile, g p.2 (latticeShift b p.1+τ) := by
        simp_rw [lowerLatticeWindow_centered]
        rfl
      _ = ∑ o, ∫ z, g o z := lattice_integral_unfold hb g hg
      _ = _ := Finset.sum_congr rfl fun o _ => hInt o
  have hG (o) : Integrable (fun v => G v o) O.law ∧ (∫ v, G v o ∂O.law) = ∫ v, ∫ z, E (O.frame v) z ∂volume ∂O.law := by
    obtain ⟨k,hk,act⟩ := haar b o
    have he (v) : G v o = ∫ z, E (O.frame (k v)) z := by rw [act]
    simp_rw [he]
    exact ⟨(hk.integrable_comp_emb k.measurableEmbedding).2 ho,hk.integral_comp k.measurableEmbedding
      (fun v => ∫ z, E (O.frame v) z)⟩
  constructor
  · simp_rw [fixed]
    exact (integrable_finsetSum _ fun o _ => (hG o).1).const_mul _
  simp_rw [fixed]
  rw [integral_const_mul,integral_finsetSum _ (fun o _ => (hG o).1)]
  simp only [fun o => (hG o).2,integral_div,Finset.sum_const,Finset.card_univ,card_cubeOrientation,nsmul_eq_mul,Nat.cast_ofNat,tetrahedron_volume hb]
  dsimp only [E]
  ring

private theorem centered_energy_floor (H : FiniteEnergyInputs) {D : Density} {S : MatrixGradient}
    (hD : TileDensityDomain D S) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (η : Mollifier)
    (R : Position ≃ₗᵢ[ℝ] Position)
    (rep : ∀ᵐ z, ∃ Γ, feasible (fun x => (centeredWindow η ℓ δ R z x : ℂ) • D.matrix x) Γ)
    (hi : Integrable fun z => energy (fun x => (centeredWindow η ℓ δ R z x : ℂ) • D.matrix x)) :
    -H.loCoeff*chargeMoment D (4/3) ≤ ∫ z, energy (fun x =>
      (centeredWindow η ℓ δ R z x : ℂ) • D.matrix x) / regionVolume (tetrahedron ℓ) := by
  let w := centeredWindow η ℓ δ R
  let V := regionVolume (tetrahedron ℓ)
  have hv : 0 < V := tetrahedron_volume_pos hℓ
  have unit z x : w z x ∈ Icc 0 1 := smoothedIndicator_bounds _ η hδ _
  have wm : Measurable (fun p : Position × Position => w p.1 p.2) :=
    (measurable_smoothedTetrahedron η ℓ hδ).comp (R.continuous.measurable.comp (measurable_snd.sub measurable_fst))
  have wn := tile_cutoff_mass η hℓ hδ
  have wi := Integrable.of_integral_ne_zero (wn.trans_ne hv.ne')
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  have avg := weighted_profile_average hD.lo (fun x => Real.rpow_nonneg (D.charge_nonneg x) _)
    wm.aestronglyMeasurable (fun z x => (unit z x).1) hv.le (ae_of_all _ fun x => by
      refine ⟨(volume.measurePreserving_sub_left x).integrable_comp_of_integrable
        (R.measurePreserving.integrable_comp_of_integrable wi), ?_⟩
      exact ((integral_sub_left_eq_self (fun z => smoothedIndicator (tetrahedron ℓ) η δ (R z)) volume x).trans
        ((R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding _).trans wn)).le)
  let m := fun z => ∫ x, D.charge x ^ (4/3:ℝ) * w z x
  have pt : ∀ᵐ z, -H.loCoeff*m z ≤ energy (fun x => (w z x : ℂ) • D.matrix x) := by
    filter_upwards [rep] with z hr
    let N := windowDensity D (w z) (fun x => (unit z x).1)
    have id : N.matrix = (fun x => (w z x : ℂ) • D.matrix x) := by ext x j k; exact Complex.real_smul
    rw [← id] at hr ⊢
    have low := le_levyLieb hr (a := hartree N.charge-H.loCoeff*chargeMoment N (4/3)) fun Γ hz =>
      (H.liebOxford N Γ hz).trans (le_add_of_nonneg_left Γ.kinetic_nonneg)
    have mN := (window_charge_moment (D := D) (unit z)
      (wm.comp (measurable_const.prodMk measurable_id)).aemeasurable hD.lo (by norm_num)).2
    simp only [Real.one_rpow, one_mul] at mN
    simp_rw [mul_comm (w z _)] at mN
    change chargeMoment N (4/3) ≤ m z at mN
    change -H.loCoeff*m z ≤ levyLieb N.matrix - hartree N.charge
    linarith only [low,mul_le_mul_of_nonneg_left mN H.lo_nonneg]
  have av := integral_mono_ae (avg.1.integral_prod_left.const_mul (-H.loCoeff)) hi pt
  rw [integral_const_mul] at av
  rw [integral_div,le_div_iff₀ hv]
  have h := mul_le_mul_of_nonpos_left avg.2 (neg_nonpos.mpr H.lo_nonneg)
  change -H.loCoeff*(V*chargeMoment D (4/3)) ≤ _ at h
  linarith only [av,h]

private theorem lo_moment_width {D : Density} {S : MatrixGradient} (hD : TileDensityDomain D S)
    {a δ : ℝ} (ha : a ≤ 1.64) (hδ : 0 < δ) :
    δ*a*chargeMoment D (4/3) ≤ (1+δ⁻¹)*(∫ x, D.charge x) + δ^3*(∫ x, D.charge x^2) := by
  have pt (x : Position) : δ*a*(D.charge x^(4/3:ℝ)) ≤ D.charge x + δ^3*D.charge x^2 := by
    let r := D.charge x
    let t := δ*r^(1/3:ℝ)
    have hr : 0 ≤ r := D.charge_nonneg _
    have ht : 0 ≤ t := mul_nonneg hδ.le (Real.rpow_nonneg hr _)
    have cube : t^3 = δ^3*r := by
      rw [show t^3 = δ^3*(r^(1/3:ℝ))^3 by dsimp only [t]; ring]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
      norm_num
    have fourth : r^(4/3:ℝ) = r*r^(1/3:ℝ) := by
      rw [show (4/3:ℝ) = 1/3+1 by norm_num, Real.rpow_add_one' hr (by norm_num), mul_comm]
    have ht' : a*t ≤ 1+t^3 := by
      nlinarith only [mul_le_mul_of_nonneg_right ha ht,ht,
        mul_nonneg (sq_nonneg (t-3/4)) (show 0 ≤ t+3/2 by linarith)]
    have bound := mul_le_mul_of_nonneg_left ht' hr
    rw [cube] at bound
    change δ*a*r^(4/3:ℝ) ≤ r + δ^3*r^2
    rw [fourth]
    dsimp only [t] at bound
    linarith only [bound]
  have av := integral_mono (hD.lo.const_mul (δ*a)) (hD.regular.charge.add (hD.square.const_mul (δ^3))) pt
  simp only [Pi.add_apply] at av
  rw [integral_add hD.regular.charge (hD.square.const_mul _),integral_const_mul,integral_const_mul] at av
  have hm : 0 ≤ ∫ x, D.charge x := integral_nonneg D.charge_nonneg
  have hc : 1 ≤ 1+δ⁻¹ := by linarith [inv_pos.mpr hδ]
  exact av.trans (add_le_add (le_mul_of_one_le_left hm hc) le_rfl)

/-- Theorem 4.12 in the translation-cell normalization, including both
Coulomb moments and the loss in front of the local energies. -/
private theorem lower_localization_data {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}
    (P : CoulombModelInputs μ ι η) {D : Density} {S : MatrixGradient} (hD : TileDensityDomain D S)
    {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (scale : 2*P.grafConstant*δ ≤ ℓ) :
    let O := P.orientations
    let F := fun u τ (p : LatticeTile) x =>
      (lowerLatticeWindow ℓ δ η p (O.frame u x-τ) : ℂ) • D.matrix x
    (-P.fock.oneBody.loCoeff*chargeMoment D (4/3) ≤ (∫ u, ∫ τ, ∑' p, energy (F u τ p) ∂latticeShiftMeasure ℓ ∂O.law)) ∧
    (1-P.grafConstant*δ/ℓ)*(∫ u, ∫ τ, ∑' p, energy (F u τ p)
      ∂latticeShiftMeasure ℓ ∂O.law) - P.grafConstant/ℓ*
        ((1+δ⁻¹)*(∫ x, D.charge x) + δ^3*(∫ x, D.charge x^2)) ≤ energy D.matrix := by
  intro O F
  let J := fun (w : Position → ℝ) => energy (fun x => (w x : ℂ) • D.matrix x)
  let E := fun u z => J (centeredWindow η ℓ δ (O.frame u) z)
  let H := P.fock.oneBody
  obtain ⟨A,ha,area⟩ := tileCutoffAreaBound_of_sobolev P.difference P.directional.toDifferenceBounds η
  have borel := levyLiebBorel_of_lowerSemicontinuous P.lowerSemicontinuity
  have centers := fun R => H.variable_centers P.product P.window borel hD.regular hD.entries hD.tf hD.lo ha area hℓ hδ R
  let w := fun (p : O.Frames × Position) (x : Position) => centeredWindow η ℓ δ (O.frame p.1) p.2 x
  have wm : Measurable (fun z : (O.Frames × Position) × Position => w z.1 z.2) :=
    (measurable_smoothedTetrahedron η ℓ hδ).comp (P.frames.comp
      ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.sub (measurable_snd.comp measurable_fst))))
  have em : Measurable (Function.uncurry E) := measurable_variableWindowEnergy (F := D.matrix) (B := 1)
    borel hD.entries w wm (fun p x => let b := smoothedIndicator_bounds (tetrahedron ℓ) η hδ (O.frame p.1 (x-p.2))
                                      (abs_of_nonneg b.1).trans_le b.2)
  have ho : Integrable (fun u => ∫ z, E u z) O.law :=
    (integrable_const _).mono' em.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (ae_of_all _ fun u => (norm_integral_le_integral_norm _).trans (centers (O.frame u)).2.2)
  have unfoldE := unfold_lower_lattice_windows O P.haar η hℓ δ J (fun R => (centers R).2.1) ho
  have mean := coulomb_variable_lower_localization P.graf D.matrix (H.representable hD.regular) hℓ hδ scale
    (ae_of_all _ fun u => (centers (O.frame u)).2.1.div_const _) (by simp_rw [integral_div]; exact ho.div_const _)
  rw [show (∫ u, ∫ τ, ∑' p, energy (F u τ p) ∂latticeShiftMeasure ℓ ∂O.law) = _ from unfoldE.2]
  refine ⟨?_, mean⟩
  have hi : Integrable (fun u => ∫ z, E u z / regionVolume (tetrahedron ℓ)) O.law := by
    simp_rw [integral_div]
    exact ho.div_const _
  have pt := fun u => centered_energy_floor H hD hℓ hδ η (O.frame u) (centers (O.frame u)).1 (centers (O.frame u)).2.1
  simpa only [integral_const,probReal_univ,one_smul] using
    (integral_mono_ae (integrable_const (-H.loCoeff*chargeMoment D (4/3))) hi (ae_of_all _ pt))

/-- Theorem 4.12 with the same universal constant in the scale condition,
the prefactor and the error. The Lieb–Oxford floor controls negative tile energies. -/
theorem CoulombModelInputs.lower_localization {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}
    (P : CoulombModelInputs μ ι η) (embed : MatrixSobolevEmbeddingFour)
    (lo : P.fock.oneBody.loCoeff ≤ 1.64) :
    ∃ C > 0, ∀ {D : Density} {S : MatrixGradient}, SqrtRegular D S →
      ∀ {ℓ δ : ℝ}, 0 < ℓ → 0 < δ → δ/ℓ < 1/C →
      let O := P.orientations
      let F := fun u τ (p : LatticeTile) x =>
        (lowerLatticeWindow ℓ δ η p (O.frame u x-τ) : ℂ) • D.matrix x
      (1-C*δ/ℓ)*(∫ u, ∫ τ, ∑' p, energy (F u τ p) ∂latticeShiftMeasure ℓ ∂O.law) -
        C/ℓ*((1+δ⁻¹)*(∫ x, D.charge x) + δ^3*(∫ x, D.charge x^2)) ≤ energy D.matrix := by
  let c := P.grafConstant
  let C := 2*c+1
  have hC : 0 < C := by dsimp only [C,c]; linarith [P.graf_nonneg]
  refine ⟨C,hC,?_⟩
  intro D S hreg ℓ δ hℓ hδ small O F
  have hD := tileDensityDomain_of_representable embed hreg
  have hs : C*δ < ℓ := by
    have h := (div_lt_div_iff₀ hℓ hC).1 small
    linarith only [h]
  have sc : 2*c*δ ≤ ℓ := by dsimp only [C] at hs; nlinarith only [hs,hδ]
  let e := ∫ u, ∫ τ, ∑' p, energy (F u τ p) ∂latticeShiftMeasure ℓ ∂O.law
  let m := (1+δ⁻¹)*(∫ x, D.charge x) + δ^3*(∫ x, D.charge x^2)
  obtain ⟨floor,lower⟩ := lower_localization_data P hD hℓ hδ sc
  change -P.fock.oneBody.loCoeff*chargeMoment D (4/3) ≤ e at floor
  change (1-c*δ/ℓ)*e-c/ℓ*m ≤ _ at lower
  have mass := lo_moment_width hD lo hδ
  change δ*P.fock.oneBody.loCoeff*chargeMoment D (4/3) ≤ m at mass
  have pos : 0 ≤ m+δ*e := by linarith only [mass,mul_le_mul_of_nonneg_left floor hδ.le]
  have hc : c ≤ C := by dsimp only [C,c]; linarith [P.graf_nonneg]
  change (1-C*δ/ℓ)*e-C/ℓ*m ≤ _
  calc
    _ = (1-c*δ/ℓ)*e-c/ℓ*m-((C-c)/ℓ)*(m+δ*e) := by ring
    _ ≤ _ := (sub_le_self _ (mul_nonneg (div_nonneg (sub_nonneg.mpr hc) hℓ.le) pos)).trans lower

end TSGA.ManyBody
