import TSGA.CoulombLatticeMixture
import TSGA.CoulombLowerTiling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Unfolding the translated and rotated lattice

The centers of the tiles of each label run once through all of space as
the lattice translation runs through one cube. Each orientation label
contributes the same integral against Haar measure.
-/

noncomputable section
namespace TSGA.SSW

open MeasureTheory Set

private abbrev LatticeIndex := Fin 3 → ℤ

private def indexEquiv {ℓ : ℝ} (hℓ : 0 < ℓ) : LatticeIndex ≃ (latticeShift ℓ).range :=
  Equiv.ofBijective (fun m => ⟨latticeShift ℓ m,⟨m,rfl⟩⟩) ⟨by
    intro m n h
    funext i
    have e := congrArg (fun (x : (latticeShift ℓ).range) => (x.val i)) h
    change ℓ * (m i : ℝ) = ℓ * (n i : ℝ) at e
    exact_mod_cast (mul_left_cancel₀ hℓ.ne' e), by
    rintro ⟨_,m,rfl⟩
    exact ⟨m,rfl⟩⟩

private theorem lattice_norm_sum_finite {ℓ : ℝ} (hℓ : 0 < ℓ) (g : CubeOrientation → Position → ℝ)
    (hg : ∀ o, Integrable (g o)) :
    (∑' p : CubeOrientation × LatticeIndex,
      ∫⁻ z in latticeCube ℓ 0, ‖g p.1 (latticeShift ℓ p.2+z)‖ₑ) ≠ ⊤ := by
  classical
  let C := latticeCube ℓ 0
  let e := indexEquiv hℓ
  let f := fun (p : CubeOrientation × LatticeIndex) (τ : Position) => g p.1 (latticeShift ℓ p.2+τ)
  have : Countable (latticeShift ℓ).range := Set.Countable.to_subtype
    (s := Set.range (latticeShift ℓ)) (Set.countable_range _)
  have fund := latticeCube_fundamental hℓ
  have hi (p) : IntegrableOn (f p) C := ((hg p.1).comp_add_left _).integrableOn
  have norm_sum (o) :
      (∑' m : LatticeIndex, ∫⁻ z in C, ‖f (o,m) z‖ₑ) = ∫⁻ z, ‖g o z‖ₑ := by
    rw [fund.lintegral_eq_tsum'' (fun z => ‖g o z‖ₑ)]
    exact e.tsum_eq (fun u => ∫⁻ z in C, ‖g o (u +ᵥ z)‖ₑ)
  have hfin : (∑' p, ∫⁻ z in C, ‖f p z‖ₑ) ≠ ⊤ := by
    rw [ENNReal.tsum_prod',tsum_fintype]
    simp_rw [norm_sum]
    exact ENNReal.sum_ne_top.mpr fun o _ => (hg o).hasFiniteIntegral.ne
  exact hfin

/-- Absolute summability for almost every shift and integrability of the
lattice sum follow by unfolding the absolute values on the cube. -/
theorem lattice_shift_series {ℓ : ℝ} (hℓ : 0 < ℓ) (g : CubeOrientation → Position → ℝ)
    (hg : ∀ o, Integrable (g o)) :
    (∀ᵐ τ ∂latticeShiftMeasure ℓ, Summable (fun p : LatticeTile => g p.2 (latticeShift ℓ p.1+τ))) ∧
    Integrable (fun τ => ∑' p : LatticeTile, g p.2 (latticeShift ℓ p.1+τ)) (latticeShiftMeasure ℓ) := by
  let f := fun (p : LatticeTile) (τ : Position) => g p.2 (latticeShift ℓ p.1+τ)
  let ν := volume.restrict (latticeCube ℓ 0)
  have fi (p) : Integrable (f p) ν := ((hg p.2).comp_add_left _).integrableOn
  have hn : (∑' p, ∫⁻ z, ‖f p z‖ₑ ∂ν) ≠ ⊤ := by
    exact ((Equiv.prodComm LatticeIndex CubeOrientation).tsum_eq
      (fun p => ∫⁻ z, ‖g p.1 (latticeShift ℓ p.2+z)‖ₑ ∂ν)).trans_ne (lattice_norm_sum_finite hℓ g hg)
  have hm (p) : AEMeasurable (fun z => ‖f p z‖ₑ) ν := (fi p).1.enorm
  have hi : (∫⁻ z, ∑' p, ‖f p z‖ₑ ∂ν) ≠ ⊤ := by rwa [lintegral_tsum hm]
  constructor
  · apply Measure.smul_absolutelyContinuous.ae_le
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hi] with z hz
    exact (tsum_enorm_ne_top_iff_summable_norm.mp hz.ne).of_norm
  · apply Integrable.smul_measure (c := (ENNReal.ofReal (ℓ^3))⁻¹) _ (by simp [hℓ])
    exact ⟨AEStronglyMeasurable.tsum (fun p => (fi p).1),
      (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)).trans_lt hi.lt_top⟩

/-- Unfold any integrable family indexed by the 24 labels. Tonelli applied
to the norms justifies the signed energy sum on the translation cube. -/
theorem lattice_integral_unfold {ℓ : ℝ} (hℓ : 0 < ℓ) (g : CubeOrientation → Position → ℝ)
    (hg : ∀ o, Integrable (g o)) :
    (∫ τ in latticeCube ℓ 0, ∑' p : LatticeTile, g p.2 (latticeShift ℓ p.1 + τ)) =
      ∑ o, ∫ z, g o z := by
  classical
  let C := latticeCube ℓ 0
  let e := indexEquiv hℓ
  let f := fun (p : CubeOrientation × LatticeIndex) (τ : Position) => g p.1 (latticeShift ℓ p.2+τ)
  have : Countable (latticeShift ℓ).range := Set.Countable.to_subtype
    (s := Set.range (latticeShift ℓ)) (Set.countable_range _)
  have fund := latticeCube_fundamental hℓ
  have hi (p) : IntegrableOn (f p) C := ((hg p.1).comp_add_left _).integrableOn
  have hfin := lattice_norm_sum_finite hℓ g hg
  change (∑' p, ∫⁻ z in C, ‖f p z‖ₑ) ≠ ⊤ at hfin
  have hsn : Summable fun p => ∫ z in C, ‖f p z‖ := by
    simp_rw [integral_norm_eq_lintegral_enorm (hi _).aestronglyMeasurable]
    exact ENNReal.summable_toReal hfin
  have hsum := (hasSum_integral_of_summable_integral_norm hi hsn).summable
  have swap (τ : Position) :
      (∑' p : LatticeTile, g p.2 (latticeShift ℓ p.1+τ)) = ∑' p, f p τ :=
    (Equiv.prodComm LatticeIndex CubeOrientation).tsum_eq (fun p => f p τ)
  simp_rw [swap]
  rw [integral_tsum (fun p => (hi p).aestronglyMeasurable) hfin,hsum.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro o _
  rw [fund.integral_eq_tsum'' (g o) (hg o)]
  exact e.tsum_eq (fun u => ∫ z in C, g o (u +ᵥ z))

/-- The linear part of the chart of a cube label. -/
def cubeFrame (ℓ : ℝ) (o : CubeOrientation) : Position ≃ₗᵢ[ℝ] Position :=
  (latticeChartEquiv ℓ (0,o)).toRealLinearIsometryEquiv

/-- Displacement of the barycenter of a labeled tile from its cube center. -/
def cubeLabelCenter (ℓ : ℝ) (o : CubeOrientation) : Position :=
  -(cubeFrame ℓ o).symm (latticeChart ℓ (0,o) 0)

theorem latticeChart_center (ℓ : ℝ) (m : LatticeIndex) (o : CubeOrientation) (x : Position) :
    latticeChart ℓ (m,o) x = cubeFrame ℓ o (x-latticeShift ℓ m-cubeLabelCenter ℓ o) := by
  have base : latticeChart ℓ (m,o) x = latticeChart ℓ (0,o) (x-latticeShift ℓ m) := by
    simp [latticeChart,latticeShift]
  let a := latticeChartEquiv ℓ (0,o)
  change _ = a.toRealLinearIsometryEquiv (x-latticeShift ℓ m - cubeLabelCenter ℓ o)
  rw [base,map_sub]
  simp only [cubeLabelCenter,map_neg,sub_neg_eq_add,show cubeFrame ℓ o = a.toRealLinearIsometryEquiv from rfl,
    LinearIsometryEquiv.apply_symm_apply,IsometryEquiv.toRealLinearIsometryEquiv_apply]
  change latticeChart ℓ (0,o) (x-latticeShift ℓ m) =
    (latticeChart ℓ (0,o) (x-latticeShift ℓ m)-latticeChart ℓ (0,o) 0)+latticeChart ℓ (0,o) 0
  simp

end TSGA.SSW

namespace TSGA.ManyBody

open SSW MeasureTheory Set

/-- Left translation in an orthogonal Haar frame law. In a realization on
the orthogonal group the measurable equivalence is group multiplication.
The signed cube charts can have determinant −1. -/
def CubeFrameInvariant (O : TileOrientationLaw) : Prop :=
  ∀ (b : ℝ) (o : CubeOrientation), ∃ k : O.Frames ≃ᵐ O.Frames,
    MeasurePreserving k O.law O.law ∧ ∀ v, O.frame (k v) = (O.frame v).trans (cubeFrame b o)

/-- A frame parametrization on a group with left-invariant measure
satisfies the cube relabeling property as soon as its image contains the
signed cube frames. This applies to normalized Haar measure on O(3). -/
theorem cubeFrameInvariant_of_haar (O : TileOrientationLaw) [Group O.Frames]
    [MeasurableMul O.Frames] [O.law.IsMulLeftInvariant]
    (mul_frame : ∀ u v : O.Frames, O.frame (u*v) = (O.frame v).trans (O.frame u))
    (labels : ∀ (b : ℝ) (o : CubeOrientation), ∃ u, O.frame u = cubeFrame b o) :
    CubeFrameInvariant O := by
  intro b o
  obtain ⟨u,hu⟩ := labels b o
  refine ⟨MeasurableEquiv.mulLeft u,measurePreserving_mul_left O.law u,?_⟩
  intro v
  exact (mul_frame u v).trans (by rw [hu])

/-- The rigid chart at a lattice point becomes the centered window after
combining the spatial rotation, the lattice translation and the barycenter. -/
theorem latticeWindow_centered (η : Mollifier) (b d : ℝ) (R : Position ≃ₗᵢ[ℝ] Position)
    (τ : Position) (p : LatticeTile) (x : Position) :
    latticeWindow b d η p (R x-τ) =
      centeredWindow η (b-d) d (R.trans (cubeFrame b p.2))
        (R.symm (latticeShift b p.1+τ+cubeLabelCenter b p.2)) x := by
  unfold latticeWindow centeredWindow
  congr 1
  rw [latticeChart_center]
  change cubeFrame b p.2 (R x-τ-latticeShift b p.1-cubeLabelCenter b p.2) = cubeFrame b p.2
    (R (x-R.symm (latticeShift b p.1+τ+cubeLabelCenter b p.2)))
  rw [map_sub R,R.apply_symm_apply]
  congr 1
  abel

/-- Absolute convergence over the lattice for a variable window functional,
for each fixed frame, and integrability over shifts. -/
theorem lattice_window_series {b : ℝ} (hb : 0 < b) (d : ℝ) (η : Mollifier)
    (J : (Position → ℝ) → ℝ)
    (hc : ∀ R : Position ≃ₗᵢ[ℝ] Position, Integrable (fun z => J (centeredWindow η (b-d) d R z)))
    (R : Position ≃ₗᵢ[ℝ] Position) :
    (∀ᵐ τ ∂latticeShiftMeasure b, Summable (fun p : LatticeTile =>
      J (fun x => latticeWindow b d η p (R x-τ)))) ∧
    Integrable (fun τ => ∑' p : LatticeTile, J (fun x => latticeWindow b d η p (R x-τ)))
      (latticeShiftMeasure b) := by
  let g := fun (o : CubeOrientation) (z : Position) =>
    J (centeredWindow η (b-d) d (R.trans (cubeFrame b o)) (R.symm (z+cubeLabelCenter b o)))
  have hg (o) : Integrable (g o) :=
    ((R.symm.measurePreserving.integrable_comp_emb R.symm.toHomeomorph.measurableEmbedding).2
      (hc (R.trans (cubeFrame b o)))).comp_add_right _
  simp_rw [latticeWindow_centered]
  exact lattice_shift_series hb g hg

/-- Translate the sum of all lattice blocks into a center integral for any
functional of the scalar window. In particular the field multiplied by the
window can have arbitrary spatially varying spin and charge. -/
theorem unfold_lattice_window_functional (O : TileOrientationLaw) (haar : CubeFrameInvariant O)
    (η : Mollifier) {b : ℝ} (hb : 0 < b) (d : ℝ) (J : (Position → ℝ) → ℝ)
    (hc : ∀ R : Position ≃ₗᵢ[ℝ] Position, Integrable (fun z => J (centeredWindow η (b-d) d R z)))
    (ho : Integrable (fun v => ∫ z, J (centeredWindow η (b-d) d (O.frame v) z)) O.law) :
    Integrable (fun v => ∫ τ, ∑' p : LatticeTile, J (fun x => latticeWindow b d η p (O.frame v x-τ))
      ∂latticeShiftMeasure b) O.law ∧
    (∫ v, ∫ τ, ∑' p : LatticeTile, J (fun x => latticeWindow b d η p (O.frame v x-τ))
      ∂latticeShiftMeasure b ∂O.law) =
    ∫ v, ∫ z, J (centeredWindow η (b-d) d (O.frame v) z) /
      regionVolume (tetrahedron b) ∂volume ∂O.law := by
  let E := fun (R : Position ≃ₗᵢ[ℝ] Position) (z : Position) => J (centeredWindow η (b-d) d R z)
  let G := fun (v : O.Frames) (o : CubeOrientation) => ∫ z, E ((O.frame v).trans (cubeFrame b o)) z
  have fixed (v : O.Frames) :
      (∫ τ, (∑' p : LatticeTile, J (fun x => latticeWindow b d η p (O.frame v x-τ)))
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
        simp_rw [latticeWindow_centered]
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

/-- Unfold the energy of all smaller tetrahedra, with the reciprocal
volume of the full tetrahedron as the center density. -/
theorem coulomb_unfold_lattice_tiles_integrable (O : TileOrientationLaw) (haar : CubeFrameInvariant O)
    (η : Mollifier) {b : ℝ} (hb : 0 < b) (d : ℝ) (f : Position → ℝ) (M : SpinMatrix) (q : Position)
    (hc : ∀ R : Position ≃ₗᵢ[ℝ] Position, Integrable (fun z => energy
      (cutoffSpiral (fun x => f x * centeredWindow η (b-d) d R z x) M q)))
    (ho : Integrable (fun v => ∫ z, energy (cutoffSpiral
      (fun x => f x * centeredWindow η (b-d) d (O.frame v) z x) M q)) O.law) :
    Integrable (fun v => ∫ τ, (∑' p : LatticeTile, energy (cutoffSpiral
      (fun x => f x*latticeWindow b d η p (O.frame v x-τ)) M q))
      ∂latticeShiftMeasure b) O.law ∧
    (∫ v, ∫ τ, (∑' p : LatticeTile, energy (cutoffSpiral
      (fun x => f x*latticeWindow b d η p (O.frame v x-τ)) M q))
      ∂latticeShiftMeasure b ∂O.law) =
    ∫ v, ∫ z, energy (cutoffSpiral (fun x => f x*centeredWindow η (b-d) d (O.frame v) z x) M q) /
      regionVolume (tetrahedron b) ∂volume ∂O.law :=
  unfold_lattice_window_functional O haar η hb d
    (fun w => energy (cutoffSpiral (fun x => f x*w x) M q)) hc ho

theorem coulomb_unfold_lattice_tiles (O : TileOrientationLaw) (haar : CubeFrameInvariant O)
    (η : Mollifier) {b : ℝ} (hb : 0 < b) (d : ℝ) (f : Position → ℝ) (M : SpinMatrix) (q : Position)
    (hc : ∀ R : Position ≃ₗᵢ[ℝ] Position, Integrable (fun z => energy
      (cutoffSpiral (fun x => f x * centeredWindow η (b-d) d R z x) M q)))
    (ho : Integrable (fun v => ∫ z, energy (cutoffSpiral
      (fun x => f x * centeredWindow η (b-d) d (O.frame v) z x) M q)) O.law) :
    (∫ v, ∫ τ, (∑' p : LatticeTile, energy (cutoffSpiral
      (fun x => f x*latticeWindow b d η p (O.frame v x-τ)) M q))
      ∂latticeShiftMeasure b ∂O.law) =
    ∫ v, ∫ z, energy (cutoffSpiral (fun x => f x*centeredWindow η (b-d) d (O.frame v) z x) M q) /
      regionVolume (tetrahedron b) ∂volume ∂O.law :=
  (coulomb_unfold_lattice_tiles_integrable O haar η hb d f M q hc ho).2

end TSGA.ManyBody
