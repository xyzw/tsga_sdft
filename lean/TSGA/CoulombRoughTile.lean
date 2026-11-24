import TSGA.FiniteCoulombSpirals
import TSGA.CutoffRepresentability

/-! # Rough Coulomb energy bounds for a smoothed tetrahedron

The scalar cutoff supplies a surface estimate for its square-root gradient.
The density-matrix trial, the Lieb–Oxford inequality and the finite spiral
rotation then bound the energy uniformly over all directions.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization
open scoped ComplexOrder InnerProductSpace

/-- The geometrical surface estimate for the square root of the smoothed
indicator. The normalization retains the exact volume of the tetrahedron. -/
def TileCutoffAreaBound (η : Mollifier) (C : ℝ) : Prop :=
  ∀ ℓ δ : ℝ, 0 < ℓ → 0 < δ →
    let f := smoothedIndicator (tetrahedron ℓ) η δ
    ∃ g : Position → Position, (∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i)) ∧
      MemLp g 2 ∧ (∫ x, ‖g x‖^2) ≤ C * regionVolume (tetrahedron ℓ) / (ℓ*δ)

private theorem cutoff_planar_upper {f : Position → ℝ} {A : SpinMatrix} (hA : A.PosSemidef)
    (rep : ∃ Γ, feasible (fun x => (f x : ℂ) • A) Γ) (q : Position) :
    let F := fun x => (f x : ℂ) • A
    energy (axialSpiral F q) ≤ energy F + ‖q‖^2/4 * ∫ x, (F x).trace.re := by
  let F := fun x => (f x : ℂ) • A
  change energy (axialSpiral F q) ≤ energy F + ‖q‖^2/4*(∫ x, (F x).trace.re)
  by_cases h0 : F =ᵐ[volume] 0
  · have he : axialSpiral F q =ᵐ[volume] F := h0.mono fun x hx => by
      change F x = 0 at hx
      simp [axialSpiral,hx,rotate]
    rw [energy_congr he]
    have ht : (∫ x, (F x).trace.re) = 0 := by
      have ht : (fun x => (F x).trace.re) =ᵐ[volume] 0 := h0.mono fun x hx => by
        change F x = 0 at hx
        simp [hx]
      rw [integral_congr_ae ht]
      simp
    rw [ht,mul_zero,add_zero]
  · apply (finiteCoulombSpiral_planar_le rep h0 (planar_cutoff f hA.isHermitian) q).trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg (sq_nonneg _)
      (total_charge_pos_of_nonzero rep h0).le)) (div_nonneg (sq_nonneg ‖q‖) (by norm_num : (0 : ℝ) ≤ 4)))

private theorem cutoff_trace_moment {f : Position → ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 1)
    (hi : Integrable f) {A : SpinMatrix} (hA : A.PosSemidef) :
    let D : Density := ⟨fun x => f x • A, fun x => hA.smul (hf x).1⟩
    traceMoment D (5/3) ≤ A.trace.re^(5/3:ℝ)*(∫ x, f x) := by
  let D : Density := ⟨fun x => f x • A, fun x => hA.smul (hf x).1⟩
  have hr : 0 ≤ A.trace.re := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have h := integral_mono_of_nonneg (ae_of_all _ fun x => tracePower_nonneg D x (5/3))
    (hi.mul_const (A.trace.re^(5/3:ℝ))) (ae_of_all _ fun x => by
      apply (tracePower_le_charge D x (by norm_num : (1 : ℝ) ≤ 5/3)).trans
      change ((f x • A).trace.re)^(5/3:ℝ) ≤ _
      rw [Matrix.trace_smul,Complex.real_smul,Complex.re_ofReal_mul,Real.mul_rpow (hf x).1 hr]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_le_one (hf x).1 (hf x).2 (by norm_num))
        (Real.rpow_nonneg hr _))
  exact h.trans_eq (by rw [integral_mul_const,mul_comm])

/-- A scalar window of arbitrary shape can be used for a boundary or
skeleton trial. Its only kinetic cost beyond the bulk and spin spiral terms
is the Fisher integral of the actual window. -/
theorem FiniteEnergyInputs.spiral_window_upper (H : FiniteEnergyInputs)
    {f : Position → ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 1) (hi : Integrable f)
    (g : Position → Position)
    (hw : ∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i))
    (hg : MemLp g 2) {A : SpinMatrix} (hA : A.PosSemidef) (q : Position) :
    let r := A.trace.re
    energy (cutoffSpiral f A q) ≤
      (H.cTF*(1+H.κ₁)*r^(5/3:ℝ) + ‖q‖^2/4*r)*(∫ x, f x) +
        8*(1+H.κ₂)*r*(∫ x, ‖g x‖^2) := by
  let D : Density := ⟨fun x => f x • A, fun x => hA.smul (hf x).1⟩
  obtain ⟨S,hS,hgrad⟩ := sqrtRegular_cutoff (fun x => (hf x).1) hi g hw hg hA
  have hD : D.matrix = fun x => (f x : ℂ) • A := by funext x i j; rfl
  have rep : ∃ Γ, feasible D.matrix Γ := H.representable hS
  have hank := cutoff_planar_upper hA (hD ▸ rep) q
  have spin : axialSpiral D.matrix q = cutoffSpiral f A q := by
    rw [hD]
    exact funext fun x => rotate_smul _ _ _
  dsimp only at hank
  rw [← hD,spin] at hank
  have hcharge : (∫ x, (D.matrix x).trace.re) = (∫ x, f x) * A.trace.re := by
    simp only [D, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul, integral_mul_const]
  change energy (cutoffSpiral f A q) ≤ energy D.matrix + ‖q‖^2/4*(∫ x, (D.matrix x).trace.re) at hank
  rw [hcharge] at hank
  have hu := kinetic_and_energy_upper H.cTF_nonneg H.trials H.quasiFree hS (ε := 1) zero_lt_one
  have he := hu.1.trans hu.2
  norm_num only [Real.sqrt_one,mul_one,div_one] at he
  rw [hgrad] at he
  have hT := mul_le_mul_of_nonneg_left (cutoff_trace_moment hf hi hA)
    (mul_nonneg H.cTF_nonneg (add_nonneg zero_le_one H.κ₁_nonneg))
  change H.cTF*(1+H.κ₁)*traceMoment D (5/3) ≤ _ at hT
  linarith only [hank,he,hT]

private theorem sphere_integrable {T : Position → ℝ} (hc : Continuous T) (r : ℝ) :
    Integrable (fun ω : Metric.sphere (0 : Position) 1 => T (r • (ω : Position)))
      (volume : Measure Position).toSphere := by
  let W := Metric.sphere (0 : Position) 1
  have hs : Continuous (fun ω : W => r • (ω : Position)) := by fun_prop
  have ht : Continuous (fun ω : W => T (r • (ω : Position))) :=
    hc.comp hs
  exact integrableOn_univ.mp (ht.continuousOn.integrableOn_compact (μ := (volume : Measure Position).toSphere)
    (isCompact_univ : IsCompact (Set.univ : Set W)))

set_option maxHeartbeats 500000 in
/-- The finite Coulomb constrained search satisfies the rough bounds of
the quantitative tiling theorem, including vacuum and all smoothing widths. -/
theorem FiniteEnergyInputs.rough_tile (H : FiniteEnergyInputs) {η : Mollifier} {C K : ℝ}
    (geom : TileCutoffAreaBound η C) (one : 1 ≤ K) (lo : H.loCoeff ≤ K)
    (tf : H.cTF*(1+H.κ₁) ≤ K) (area : 8*(1+H.κ₂)*C ≤ K) :
    ∀ A : SpinMatrix, A.PosSemidef → ∀ (q : Position) (ℓ δ : ℝ), 0 < ℓ → 0 < δ →
      let r := A.trace.re
      (-K*(r*r^(1/3:ℝ)) ≤ averagedTile energy η A q ℓ δ) ∧
        averagedTile energy η A q ℓ δ + K*(r*r^(1/3:ℝ)) ≤ K*(r*rateGrowth r q + r/(ℓ*δ)) := by
  intro A hA q ℓ δ he hd
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  let V := regionVolume (tetrahedron ℓ)
  let r := A.trace.re
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have hV : 0 < V := tetrahedron_volume_pos he
  have ht : 0 < ℓ*δ := mul_pos he hd
  have hf : ∀ x, f x ∈ Set.Icc 0 1 := smoothedIndicator_bounds _ _ hd
  have hm : (∫ x, f x) = V := tile_cutoff_mass η he hd
  have hi : Integrable f := Integrable.of_integral_ne_zero (hm.trans_ne hV.ne')
  let D : Density := ⟨fun x => f x • A, fun x => hA.smul (hf x).1⟩
  obtain ⟨g,hw,hg,harea⟩ := geom ℓ δ he hd
  obtain ⟨S,hS,hgrad⟩ := sqrtRegular_cutoff (fun x => (hf x).1) hi g hw hg hA
  have rep : ∃ Γ, feasible D.matrix Γ := H.representable hS
  have hD : D.matrix = fun x => (f x : ℂ) • A := by funext x i j; rfl
  have repC : ∃ Γ, feasible (fun x => (f x : ℂ) • A) Γ := by rwa [← hD]
  have spin (k : Position) : axialSpiral D.matrix k = cutoffSpiral f A k := by
    rw [hD]
    exact funext fun x => rotate_smul (⟪k,x⟫_ℝ) (f x : ℂ) A
  have mass : (∫ x, (D.matrix x).trace.re) = r*V := by
    simp only [D,Matrix.trace_smul,Complex.real_smul,Complex.re_ofReal_mul,integral_mul_const,hm,mul_comm V,r]
  have hp43 : r^(4/3:ℝ) = r*r^(1/3:ℝ) := by
    rw [show (4/3:ℝ) = 1+(1/3:ℝ) by norm_num,Real.rpow_add_of_nonneg hr (by norm_num) (by norm_num),Real.rpow_one]
  have hp53 : r^(5/3:ℝ) = r*r^(2/3:ℝ) := by
    rw [show (5/3:ℝ) = 1+(2/3:ℝ) by norm_num,Real.rpow_add_of_nonneg hr (by norm_num) (by norm_num),Real.rpow_one]
  have hflat : energy D.matrix ≤ K*(r*r^(2/3:ℝ))*V + K*(r/(ℓ*δ))*V := by
    have hu := kinetic_and_energy_upper H.cTF_nonneg H.trials H.quasiFree hS (ε := 1) zero_lt_one
    have h := hu.1.trans hu.2
    norm_num only [Real.sqrt_one,mul_one,div_one] at h
    have htr : traceMoment D (5/3) ≤ r^(5/3:ℝ)*V := (cutoff_trace_moment hf hi hA).trans_eq (by rw [hm])
    have h₁ := (mul_le_mul_of_nonneg_left htr (mul_nonneg H.cTF_nonneg (by linarith [H.κ₁_nonneg] : 0 ≤ 1+H.κ₁))).trans
      (mul_le_mul_of_nonneg_right tf (mul_nonneg (Real.rpow_nonneg hr _) hV.le))
    change (∫ x, ‖g x‖^2) ≤ C*V/(ℓ*δ) at harea
    change sqrtKinetic S = r*(∫ x, ‖g x‖^2) at hgrad
    have hJ : 0 ≤ 8*(1+H.κ₂) := mul_nonneg (by norm_num) (add_nonneg zero_le_one H.κ₂_nonneg)
    have surface : 8*(1+H.κ₂)*(r*∫ x, ‖g x‖^2) ≤ K*(r/(ℓ*δ))*V := calc
      _ ≤ 8*(1+H.κ₂)*(r*(C*V/(ℓ*δ))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left harea hr) hJ
      _ = (8*(1+H.κ₂)*C)*(r/(ℓ*δ)*V) := by ring
      _ ≤ K*(r/(ℓ*δ)*V) := mul_le_mul_of_nonneg_right area (mul_nonneg (div_nonneg hr ht.le) hV.le)
      _ = _ := by ring
    have heq : energy D.matrix ≤ H.cTF*(1+H.κ₁)*traceMoment D (5/3) + 8*(1+H.κ₂)*(r*∫ x, ‖g x‖^2) := by
      apply h.trans_eq
      rw [hgrad]
      ring
    rw [← hp53]
    exact heq.trans ((add_le_add h₁ surface).trans_eq (by ring))
  have low (k : Position) : -K*(r*r^(1/3:ℝ)) ≤ tileEnergy energy η A ℓ δ k := by
    let R : Density := ⟨cutoffSpiral f A k, fun x => (rotate_posSemidef _ hA).smul (Complex.zero_le_real.mpr (hf x).1)⟩
    obtain ⟨Γ,hΓ⟩ := repC
    let s := cutoffRotation f A k ⟨Γ,hΓ⟩
    have hb : hartree R.charge - H.loCoeff * chargeMoment R (4/3) ≤ levyLieb R.matrix :=
      le_levyLieb ⟨s.val,s.property⟩ fun Λ hΛ => (H.liebOxford R Λ hΛ).trans (le_add_of_nonneg_left Λ.kinetic_nonneg)
    have hp : chargeMoment R (4/3) ≤ r^(4/3:ℝ)*V := tile_charge_moment η he hd hA k
    have h₁ := (mul_le_mul_of_nonneg_left hp H.lo_nonneg).trans
      (mul_le_mul_of_nonneg_right lo (mul_nonneg (Real.rpow_nonneg hr _) hV.le))
    change -K*(r*r^(1/3:ℝ)) ≤ (levyLieb R.matrix-hartree R.charge)/V
    rw [← hp43]
    apply (le_div_iff₀ hV).2
    linarith only [hb,h₁]
  have up (k : Position) : tileEnergy energy η A ℓ δ k ≤
      K*(r*r^(2/3:ℝ) + r*‖k‖^2 + r/(ℓ*δ)) := by
    have hu := cutoff_planar_upper (f := f) hA repC k
    dsimp only at hu
    rw [← hD] at hu
    change energy (axialSpiral D.matrix k) ≤ energy D.matrix + ‖k‖^2/4*(∫ x, (D.matrix x).trace.re) at hu
    rw [mass,spin] at hu
    have hq := mul_le_mul_of_nonneg_right (show 1/4 ≤ K by linarith) (mul_nonneg (mul_nonneg hr (sq_nonneg ‖k‖)) hV.le)
    apply (div_le_iff₀ hV).2
    change energy (cutoffSpiral f A k) ≤ _
    linarith only [hu,hflat,hq]
  let T := tileEnergy energy η A ℓ δ
  have hc : Continuous T := by
    change Continuous (fun k => energy (cutoffSpiral f A k)/V)
    have h := (finiteCoulombSpiral_continuous rep).div_const V
    simpa only [spin] using h
  have hT := sphere_integrable hc ‖q‖
  let L := -K*(r*r^(1/3:ℝ))
  let U := K*(r*r^(2/3:ℝ)+r*‖q‖^2+r/(ℓ*δ))
  have hl := direction_mono_add (f := fun _ => L) (g := T) (d := 0) (integrable_const L) hT
    (fun ω => by rw [add_zero]; exact low (‖q‖ • (ω : Position)))
  have hu := direction_mono_add (f := T) (g := fun _ => U) (d := 0) hT (integrable_const U)
    (fun ω => by
      have hh : ‖(ω : Position)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
      simpa only [norm_smul,Real.norm_eq_abs,abs_norm,mul_one,hh,add_zero,T,U] using up (‖q‖ • (ω : Position)))
  simp only [directionAverage_const,add_zero] at hl hu
  refine ⟨hl,?_⟩
  change directionAverage T ‖q‖ + K*(r*r^(1/3:ℝ)) ≤ K*(r*rateGrowth r q+r/(ℓ*δ))
  exact (add_le_add hu (le_refl (K*(r*r^(1/3:ℝ))))).trans_eq (by dsimp only [U,rateGrowth]; ring)

end TSGA.ManyBody
