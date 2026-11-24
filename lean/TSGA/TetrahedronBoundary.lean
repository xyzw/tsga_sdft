import TSGA.TetrahedronVolume

/-! # Boundary layers of the reference tetrahedron

A displacement of size w changes each defining face inequality by at
most 2w. Expanding and shrinking the length by 16w therefore encloses the
boundary layer between two concentric tetrahedra.
-/

noncomputable section
namespace TSGA.SSW
open MeasureTheory Set Metric

theorem tetrahedron_mono {a b : ℝ} (h : a ≤ b) : tetrahedron a ⊆ tetrahedron b := by
  intro x hx
  obtain ⟨h₁,h₂,h₃⟩ := hx
  exact ⟨by linarith,by linarith,by linarith⟩

theorem tetrahedron_empty_of_nonpos {a : ℝ} (ha : a ≤ 0) : tetrahedron a = ∅ := by
  ext x
  change (_ ∧ _ ∧ _) ↔ False
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    linarith [abs_nonneg (x 2)]
  · simp

theorem tetrahedron_enlarge {ℓ w : ℝ} {x y : Position}
    (hx : x ∈ tetrahedron ℓ) (hxy : dist x y < w) : y ∈ tetrahedron (ℓ+16*w) := by
  have hd (j : Fin 3) : |x j-y j| < w := (PiLp.dist_apply_le x y j).trans_lt hxy
  have h₀ := abs_lt.mp (hd 0)
  have h₁ := abs_lt.mp (hd 1)
  have h₂ := abs_lt.mp (hd 2)
  obtain ⟨ha,hb,hc⟩ := hx
  have ha' := abs_lt.mp ha
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩, by linarith, by linarith⟩

theorem tetrahedron_boundary_subset (ℓ w : ℝ) :
    thickening w (frontier (tetrahedron ℓ)) ⊆ tetrahedron (ℓ+16*w) \ tetrahedron (ℓ-16*w) := by
  rintro x hx
  obtain ⟨z,hz,hxz⟩ := mem_thickening_iff.mp hx
  rw [frontier_eq_closure_inter_closure] at hz
  have hzball : z ∈ ball x w := by simpa only [mem_ball,dist_comm z x] using hxz
  obtain ⟨u,hu,hU⟩ := _root_.mem_closure_iff.mp hz.1 (ball x w) isOpen_ball hzball
  obtain ⟨v,hv,hV⟩ := _root_.mem_closure_iff.mp hz.2 (ball x w) isOpen_ball hzball
  refine ⟨tetrahedron_enlarge hU hu,fun hx' => hV ?_⟩
  have hle := tetrahedron_enlarge hx' (show dist x v < w by simpa only [mem_ball,dist_comm v x] using hv)
  simpa only [sub_add_cancel] using hle

theorem tetrahedron_boundary_volume {ℓ w : ℝ} (hw : 0 < w) (hle : w ≤ ℓ) :
    regionVolume (thickening w (frontier (tetrahedron ℓ))) ≤ 1156*ℓ^2*w := by
  let b := ℓ + 16*w
  let a := max 0 (ℓ-16*w)
  have he : 0 < ℓ := hw.trans_le hle
  have hb : 0 < b := by dsimp [b]; positivity
  have ha : 0 ≤ a := le_max_left _ _
  have hab : a ≤ b := max_le hb.le (by dsimp [b]; linarith)
  have hd : b-a ≤ 32*w := by have := le_max_right 0 (ℓ-16*w); dsimp [a,b]; linarith
  have hu : b ≤ 17*ℓ := by dsimp [b]; linarith
  have hi : tetrahedron a = tetrahedron (ℓ-16*w) := by
    rcases le_total 0 (ℓ-16*w) with h | h
    · rw [show a = ℓ-16*w from max_eq_right h]
    · rw [show a = 0 from max_eq_left h,tetrahedron_empty_of_nonpos le_rfl,tetrahedron_empty_of_nonpos h]
  have hs : thickening w (frontier (tetrahedron ℓ)) ⊆ tetrahedron b \ tetrahedron a := by
    rw [hi]; exact tetrahedron_boundary_subset _ _
  have hfin : volume (tetrahedron b) ≠ ⊤ := (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos hb)).2.ne
  have hvol (t : ℝ) (ht : 0 ≤ t) : volume.real (tetrahedron t) = t^3/24 := by
    rcases ht.eq_or_lt with rfl | h
    · simp [tetrahedron_empty_of_nonpos (le_refl 0)]
    · exact tetrahedron_volume h
  have hdiff := measureReal_sdiff (μ := volume) (tetrahedron_mono hab) (tetrahedron_open a).measurableSet hfin
  have hmono := measureReal_mono (μ := volume) hs (measure_ne_top_of_subset sdiff_subset hfin)
  change regionVolume _ ≤ _ at hmono
  rw [regionVolume,hdiff,hvol a ha,hvol b hb.le] at hmono
  apply hmono.trans
  have hs₁ := mul_le_mul_of_nonneg_right hab ha
  have hs₂ := mul_le_mul_of_nonneg_left hab hb.le
  have hsq := pow_le_pow_left₀ hb.le hu 2
  have hg : b*b + b*a + a*a ≤ 3*(17*ℓ)^2 := by nlinarith only [hs₁,hs₂,hsq]
  have hp := mul_le_mul hd hg (by positivity : 0 ≤ b*b+b*a+a*a) (by positivity : 0 ≤ 32*w)
  nlinarith only [hp]

end TSGA.SSW
