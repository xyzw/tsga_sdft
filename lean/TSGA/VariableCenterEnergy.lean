import TSGA.VariableWindowAverage

/-! # Integration over all centers of a rotated tetrahedron -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set SSW TSGA.Localization Metric

/-- The absolute energy is integrable in the center for every frame. Its
bound depends only on the volume and the Fisher area of the tetrahedron. -/
theorem FiniteEnergyInputs.variable_centers (H : FiniteEnergyInputs)
    (product : WeakScalarMatrixProduct) (W : WindowSobolevRules) (borel : LevyLiebBorel)
    {D : Density} {S : MatrixGradient} (reg : SqrtRegular D S)
    (entries : ∀ i j, Integrable (fun x => D.matrix x i j))
    (p₅ : Integrable fun x => D.charge x^(5/3:ℝ)) (p₄ : Integrable fun x => D.charge x^(4/3:ℝ))
    {η : Mollifier} {C : ℝ} (c₀ : 0 ≤ C) (area : TileCutoffAreaBound η C)
    {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (R : Position ≃ₗᵢ[ℝ] Position) :
    let F := fun z x => (centeredWindow η a d R z x : ℂ) • D.matrix x
    let V := regionVolume (tetrahedron a)
    (∀ᵐ z, ∃ Γ, feasible (F z) Γ) ∧ Integrable (fun z => energy (F z)) ∧
      (∫ z, |energy (F z)|) ≤ variableWindowCost H D S 1 V (C*V/(a*d)) := by
  intro F V
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  obtain ⟨h,dh,lh,fh⟩ := area a d ha hd
  let n := smoothedIndicator (tetrahedron a) η d
  let w := centeredWindow η a d R
  let g := fun z x => R.symm (h (R (x-z)))
  have Vpos := tetrahedron_volume_pos ha
  have wn := tile_cutoff_mass η ha hd
  have ni : Integrable n := Integrable.of_integral_ne_zero (wn.trans_ne Vpos.ne')
  have wm : Measurable (fun p : Position × Position => w p.1 p.2) :=
    (measurable_smoothedTetrahedron η a hd).comp (R.continuous.measurable.comp (measurable_snd.sub measurable_fst))
  have unit (z x) : w z x ∈ Icc 0 1 := smoothedIndicator_bounds _ η hd _
  have q := (MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant
    (volume : Measure Position) (volume : Measure Position)).comp (Measure.measurePreserving_swap (μ := (volume : Measure Position)) (ν := volume)).quasiMeasurePreserving
  have gm : AEStronglyMeasurable (fun p : Position × Position => g p.1 p.2) (volume.prod volume) :=
    R.symm.continuous.comp_aestronglyMeasurable (lh.aestronglyMeasurable.comp_quasiMeasurePreserving
      (R.measurePreserving.quasiMeasurePreserving.comp q))
  have means {v : Position → ℝ} (vi : Integrable v) (x : Position) :
      Integrable (fun z => v (R (x-z))) ∧ (∫ z, v (R (x-z))) = ∫ z, v z := by
    refine ⟨(volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (R.measurePreserving.integrable_comp_of_integrable vi),?_⟩
    exact (integral_sub_left_eq_self (fun z => v (R z)) volume x).trans
      (R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding v)
  apply H.variable_windows_average product reg p₅ p₄ w g zero_le_one unit wm.aestronglyMeasurable gm
    (ae_of_all _ fun z => W.rigid dh R z) Vpos.le (div_nonneg (mul_nonneg c₀ Vpos.le) (mul_pos ha hd).le)
  · exact ae_of_all _ fun x => ⟨(means ni x).1,((means ni x).2.trans wn).le⟩
  · apply ae_of_all
    intro x
    simp only [g,R.symm.norm_map]
    have hh := means (lh.integrable_norm_pow (p := 2) (by decide)) x
    exact ⟨hh.1,hh.2.trans_le fh⟩
  · exact (measurable_variableWindowEnergy borel entries w wm fun z x =>
      (abs_of_nonneg (unit z x).1).trans_le (unit z x).2).aestronglyMeasurable

end TSGA.ManyBody
