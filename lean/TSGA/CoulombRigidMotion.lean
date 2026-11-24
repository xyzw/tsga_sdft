import TSGA.StateSpinRotation
import TSGA.SpiralCovariance
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Rigid motions of particles in the Coulomb constrained search

All particles undergo the same spatial isometry. The orthogonal part acts on
the three components of each weak gradient. Pair distances and the Jacobian
are preserved, including in the integrations defining the spin marginal.
-/

noncomputable section

namespace TSGA.ManyBody
open MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace

private abbrev SpatialRotation := Position ≃ₗᵢ[ℝ] Position

private def sectorLinear (n : ℕ) (R : SpatialRotation) : Space n ≃L[ℝ] Space n :=
  ContinuousLinearEquiv.piCongrRight fun _ => R.toContinuousLinearEquiv

private def motion (n : ℕ) (R : SpatialRotation) (a : Position) : Space n ≃ₜ Space n :=
  (sectorLinear n R).toHomeomorph.trans (Homeomorph.addRight (fun _ => a))

private theorem motion_apply {n : ℕ} (R : SpatialRotation) (a : Position) (x : Space n)
    (i : Fin n) : motion n R a x i = R (x i) + a := rfl

private theorem motion_preserving (n : ℕ) (R : SpatialRotation) (a : Position) :
    MeasurePreserving (motion n R a) volume volume :=
  measurePreserving_pi _ _ fun _ => (measurePreserving_add_right volume a).comp R.measurePreserving

private theorem motion_integral {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : SpatialRotation) (a : Position) (f : Space n → F) :
    (∫ x, f (motion n R a x)) = ∫ y, f y :=
  (motion_preserving n R a).integral_comp (motion n R a).toMeasurableEquiv.measurableEmbedding f

private def rotatedGradient (R : SpatialRotation) (v : Fin 3 → ℂ) (j : Fin 3) : ℂ :=
  ∑ k, (R (EuclideanSpace.single j 1) k) • v k

private theorem rotatedGradient_norm (R : SpatialRotation) (v : Fin 3 → ℂ) :
    ∑ j, ‖rotatedGradient R v j‖ ^ 2 = ∑ k, ‖v k‖ ^ 2 := by
  have coord (u : Position) (j : Fin 3) :
      ∑ k, R (EuclideanSpace.single j 1) k * u k = R.symm u j := by
    have h := R.inner_map_map (EuclideanSpace.single j 1) (R.symm u)
    rw [R.apply_symm_apply, EuclideanSpace.inner_single_left] at h
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using h
  let re : Position := WithLp.toLp 2 (fun k => (v k).re)
  let im : Position := WithLp.toLp 2 (fun k => (v k).im)
  have hre (j) : (rotatedGradient R v j).re = R.symm re j := by
    simpa [rotatedGradient, re, Complex.real_smul] using coord re j
  have him (j) : (rotatedGradient R v j).im = R.symm im j := by
    simpa [rotatedGradient, im, Complex.real_smul] using coord im j
  have hr := congrArg (fun z : ℝ => z^2) (R.symm.norm_map re)
  have hi := congrArg (fun z : ℝ => z^2) (R.symm.norm_map im)
  simp only [EuclideanSpace.real_norm_sq_eq] at hr hi
  simp only [Complex.sq_norm, Complex.normSq_apply, hre, him, Finset.sum_add_distrib, ← sq]
  exact congrArg₂ (· + ·) hr hi

private theorem direction_expansion {n : ℕ} (R : SpatialRotation) (i : Fin n) (j : Fin 3) :
    sectorLinear n R (particleDirection i j) =
      ∑ k, (R (EuclideanSpace.single j 1) k) • particleDirection i k := by
  ext m l
  by_cases h : m = i
  · subst m
    fin_cases l <;> simp [sectorLinear, particleDirection, Fin.sum_univ_three]
  · simp [sectorLinear, particleDirection, h]

private theorem weak_motion {n : ℕ} (ψ : Wave n) (s : Spins n) (i : Fin n) (j : Fin 3)
    (R : SpatialRotation) (a : Position) (f : Space n → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (∫ x, fderiv ℝ f x (particleDirection i j) • ψ.value s (motion n R a x)) =
    -(∫ x, f x • rotatedGradient R (ψ.gradient s (motion n R a x) i) j) := by
  let e := motion n R a
  let L := sectorLinear n R
  let g := f ∘ e.symm
  have hg : ContDiff ℝ ∞ g :=
    hf.comp (L.symm.contDiff.comp (contDiff_id.sub contDiff_const))
  have hgc : HasCompactSupport g := hc.comp_homeomorph e.symm
  have hd (y : Space n) : HasFDerivAt e.symm (L.symm : Space n →L[ℝ] Space n) y := by
    exact (L.symm.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const (fun _ => a))) |>.congr_fderiv (by ext; simp)
  let v := particleDirection i j
  let c (k : Fin 3) := R (EuclideanSpace.single j 1) k
  have deriv (x : Space n) : fderiv ℝ f x v = ∑ k, c k * fderiv ℝ g (e x) (particleDirection i k) := by
    have hg' := ((hf.differentiable (by simp) (e.symm (e x))).hasFDerivAt.comp (e x) (hd (e x))).fderiv
    have d : fderiv ℝ g (e x) (L v) = fderiv ℝ f x v := by
      rw [show fderiv ℝ g (e x) = _ from hg', ContinuousLinearMap.comp_apply]
      simp
    rw [← d, show L v = _ from direction_expansion R i j, map_sum]
    simp [c]
  have hw : (∫ y, (∑ k, c k * fderiv ℝ g y (particleDirection i k)) • ψ.value s y) =
      -(∫ y, g y • rotatedGradient R (ψ.gradient s y i) j) := by
    have h1 (k : Fin 3) : Integrable (fun y => c k • (fderiv ℝ g y (particleDirection i k) • ψ.value s y)) :=
      ((ψ.square_integrable s).locallyIntegrable (by norm_num) |>.integrable_smul_left_of_hasCompactSupport
        ((hg.continuous_fderiv (by simp)).clm_apply continuous_const) (hgc.fderiv_apply ℝ _)).smul (c k)
    have h2 (k : Fin 3) : Integrable (fun y => c k • (g y • ψ.gradient s y i k)) :=
      ((ψ.gradient_L2 s i k).locallyIntegrable (by norm_num) |>.integrable_smul_left_of_hasCompactSupport
        hg.continuous hgc).smul (c k)
    simp only [Finset.sum_smul, mul_smul, rotatedGradient, Finset.smul_sum, smul_comm (g _) (R (EuclideanSpace.single j 1) _)]
    change (∫ y, ∑ k, c k • (fderiv ℝ g y (particleDirection i k) • ψ.value s y)) =
      -(∫ y, ∑ k, c k • (g y • ψ.gradient s y i k))
    rw [integral_finsetSum _ (fun k _ => h1 k), integral_finsetSum _ (fun k _ => h2 k)]
    simp only [integral_smul, ψ.weak_gradient s i _ g hg hgc, smul_neg, Finset.sum_neg_distrib]
  calc
    _ = ∫ x, (∑ k, c k * fderiv ℝ g (e x) (particleDirection i k)) • ψ.value s (e x) := integral_congr_ae (ae_of_all _ fun x => congrArg (· • ψ.value s (e x)) (deriv x))
    _ = _ := motion_integral R a (fun y => (∑ k, c k * fderiv ℝ g y (particleDirection i k)) • ψ.value s y)
    _ = _ := hw
    _ = _ := by
      rw [← motion_integral R a (fun y => g y • rotatedGradient R (ψ.gradient s y i) j)]
      simp [g, e]

private theorem coulomb_motion {n : ℕ} (R : SpatialRotation) (a : Position) (x : Space n) :
    coulomb (motion n R a x) = coulomb x := by simp [coulomb, motion_apply, ← map_sub]

private def Wave.move {n : ℕ} (ψ : Wave n) (R : SpatialRotation) (a : Position) : Wave n where
  value s x := ψ.value s (motion n R a x)
  gradient s x i j := rotatedGradient R (ψ.gradient s (motion n R a x) i) j
  antisymmetric π s := (motion_preserving n R a).quasiMeasurePreserving.ae (ψ.antisymmetric π s)
  square_integrable s := (ψ.square_integrable s).comp_measurePreserving (motion_preserving n R a)
  normalized := by
    refine Eq.trans (Finset.sum_congr rfl fun s _ => motion_integral R a (fun x => ‖ψ.value s x‖^2)) ψ.normalized
  gradient_L2 s i j := memLp_finsetSum _ fun k _ =>
    ((ψ.gradient_L2 s i k).comp_measurePreserving (motion_preserving n R a)).const_smul (R (EuclideanSpace.single j 1) k)
  weak_gradient s i j f := weak_motion ψ s i j R a f
  interaction_integrable s := by
    have h := ((motion_preserving n R a).integrable_comp_emb (motion n R a).toMeasurableEquiv.measurableEmbedding).2 (ψ.interaction_integrable s)
    simpa only [Function.comp_def, coulomb_motion] using h

private theorem move_kinetic {n : ℕ} (ψ : Wave n) (R : SpatialRotation) (a : Position) :
    (ψ.move R a).kinetic = ψ.kinetic := by
  unfold Wave.kinetic sectorIntegral
  simp only [Wave.move, rotatedGradient_norm]
  exact Finset.sum_congr rfl fun s _ => motion_integral R a (fun x => ∑ i, ∑ j, ‖ψ.gradient s x i j‖^2)

private theorem move_interaction {n : ℕ} (ψ : Wave n) (R : SpatialRotation) (a : Position) :
    (ψ.move R a).interaction = ψ.interaction := by
  unfold Wave.interaction sectorIntegral
  refine Finset.sum_congr rfl fun s _ => ?_
  simpa only [coulomb_motion, Wave.move] using motion_integral R a (fun x => coulomb x * ‖ψ.value s x‖^2)

private theorem move_density {n : ℕ} (ψ : Wave (n+1)) (R : SpatialRotation) (a x : Position) :
    (ψ.move R a).matrixDensity x = ψ.matrixDensity (R x + a) := by
  have h (y : Space n) : motion (n+1) R a (Fin.cons x y) =
      Fin.cons (α := fun _ => Position) (R x + a) (motion n R a y) := by
    funext k
    exact Fin.cases rfl (fun _ => rfl) k
  ext i j
  unfold Wave.matrixDensity
  simp only [Wave.move, h]
  congr 1
  exact Finset.sum_congr rfl fun s _ => motion_integral R a
    (fun y => ψ.value (Fin.cons i s) (Fin.cons (R x + a) y) * conj (ψ.value (Fin.cons j s) (Fin.cons (R x + a) y)))

private def PureState.move (s : PureState) (R : SpatialRotation) (a : Position) : PureState := match s with
  | .vacuum => .vacuum
  | .occupied ψ => .occupied (ψ.move R a)

@[simp] private theorem pure_move_kinetic (s : PureState) (R : SpatialRotation) (a : Position) :
    (s.move R a).kinetic = s.kinetic := by cases s <;> simp [PureState.move, PureState.kinetic, move_kinetic]

@[simp] private theorem pure_move_interaction (s : PureState) (R : SpatialRotation) (a : Position) :
    (s.move R a).interaction = s.interaction := by
  cases s <;> simp [PureState.move, PureState.interaction, move_interaction]

@[simp] private theorem pure_move_particles (s : PureState) (R : SpatialRotation) (a : Position) :
    (s.move R a).particles = s.particles := by cases s <;> rfl

@[simp] private theorem pure_move_density (s : PureState) (R : SpatialRotation) (a x : Position) :
    (s.move R a).matrixDensity x = s.matrixDensity (R x+a) := by
  cases s with
  | vacuum => rfl
  | occupied ψ => exact move_density ψ R a x

private theorem rigid_preserving (R : SpatialRotation) (a : Position) :
    MeasurePreserving (fun x => R x + a) volume volume :=
  (measurePreserving_add_right volume a).comp R.measurePreserving

private def MixedState.move (Γ : MixedState) (R : SpatialRotation) (a : Position) : MixedState where
  component k := (Γ.component k).move R a
  weight := Γ.weight
  weight_nonneg := Γ.weight_nonneg
  normalized := Γ.normalized
  particles_summable := by simpa using Γ.particles_summable
  kinetic_summable := by simpa using Γ.kinetic_summable
  interaction_summable := by simpa using Γ.interaction_summable
  density_summable := by
    simpa only [pure_move_density] using (rigid_preserving R a).quasiMeasurePreserving.ae Γ.density_summable

private theorem feasible_move {Γ : MixedState} {F : Position → SpinMatrix} (hΓ : feasible F Γ)
    (R : SpatialRotation) (a : Position) : feasible (fun x => F (R x+a)) (Γ.move R a) := by
  filter_upwards [(rigid_preserving R a).quasiMeasurePreserving.ae hΓ] with x hx
  change Γ.matrixDensity (R x + a) = F (R x+a) at hx
  rw [← hx]
  ext i j
  simp only [MixedState.matrixDensity, MixedState.move, pure_move_density]

private theorem rigid_integral (R : SpatialRotation) (a : Position) (f : Position → ℝ) :
    (∫ x, f (R x + a)) = ∫ y, f y :=
  (rigid_preserving R a).integral_comp
    ((Homeomorph.addRight a).toMeasurableEquiv.measurableEmbedding.comp
      R.toHomeomorph.toMeasurableEquiv.measurableEmbedding) f

/-- Rigid motions preserve the full constrained search, including its Hartree subtraction. -/
theorem energy_rigidMotion (F : Position → SpinMatrix) (R : Position ≃ₗᵢ[ℝ] Position) (a : Position) :
    energy (fun x => F (R x + a)) = energy F := by
  let values (G : Position → SpinMatrix) := {e | ∃ Γ : MixedState, feasible G Γ ∧ e = Γ.kinetic + Γ.interaction}
  have subset (G : Position → SpinMatrix) (U : SpatialRotation) (b : Position) :
      values G ⊆ values (fun x => G (U x + b)) := by
    rintro e ⟨Γ, hΓ, rfl⟩
    exact ⟨Γ.move U b, feasible_move hΓ U b, by simp [MixedState.kinetic, MixedState.interaction, MixedState.move]⟩
  have hLL : levyLieb (fun x => F (R x+a)) = levyLieb F := by
    apply congrArg sInf
    apply Set.Subset.antisymm _ (subset F R a)
    simpa using subset (fun x => F (R x+a)) R.symm (-(R.symm a))
  have hc (x y : Position) : ‖(R x + a) - (R y + a)‖ = ‖x-y‖ := by simp [← map_sub]
  let ρ (x : Position) := (F x).trace.re
  have hH : hartree (fun x => ρ (R x+a)) = hartree ρ := by
    unfold hartree
    have inner (x : Position) :
        (∫ y, ρ (R x+a) * ρ (R y+a) / ‖x-y‖) =
        ∫ y, ρ (R x+a) * ρ y / ‖R x+a-y‖ := by
      simpa only [hc] using rigid_integral R a (fun y => ρ (R x+a) * ρ y / ‖R x+a-y‖)
    simp_rw [inner]
    rw [rigid_integral R a (fun x => ∫ y, ρ x * ρ y / ‖x-y‖)]
  exact congrArg₂ (· - ·) hLL hH

/-- The actual Coulomb energy of an interior tile depends on its orientation
through the rotated wavevector and is independent of its center. -/
theorem coulomb_spiral_rigidMotion (f : Position → ℝ) (M : SpinMatrix) (q a : Position)
    (R : Position ≃ₗᵢ[ℝ] Position) :
    energy (SSW.cutoffSpiral (fun x => f (R x-a)) M q) =
      energy (SSW.cutoffSpiral f M (R q)) := by
  rw [SSW.spiralEnergy_isometry energy R (fun G => by simpa using energy_rigidMotion G R 0)
    (fun x => f (x-a))]
  exact SSW.spiralEnergy_translate energy
    (fun G τ => by simpa [sub_eq_add_neg] using energy_rigidMotion G (LinearIsometryEquiv.refl ℝ Position) (-τ))
    energy_axial f M (R q) a

end TSGA.ManyBody
