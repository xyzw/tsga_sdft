import TSGA.WaveCurrent
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Current in a one-dimensional spin subspace

The relation between two spin amplitudes propagates to their distributional
derivatives. Applying antisymmetry first makes this argument work in each
particle coordinate.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped ComplexConjugate

private def spinAt {n : ℕ} (a : Fin 2) (t : Spins n) (i : Fin (n+1)) : Spins (n+1) :=
  (Fin.cons a t) ∘ Equiv.swap 0 i

private theorem Wave.swap_row {n : ℕ} (ψ : Wave (n+1)) {c d : ℂ} (t : Spins n)
    (h : ∀ᵐ z, c*ψ.value (Fin.cons 0 t) z = d*ψ.value (Fin.cons 1 t) z) (i : Fin (n+1)) :
    ∀ᵐ z, c*ψ.value (spinAt 0 t i) z = d*ψ.value (spinAt 1 t i) z := by
  let π := Equiv.swap 0 i
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin (n+1) => Position) π.symm
  have he : MeasurePreserving e := volume_measurePreserving_piCongrLeft _ _
  have heq (z : Space (n+1)) : e z = z ∘ π := by
    funext j
    simp [e,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have hspin (a : Fin 2) : spinAt a t i ∘ π = Fin.cons a t := by
    ext k
    simp [spinAt,π,Function.comp_def]
  filter_upwards [he.quasiMeasurePreserving.ae h,ψ.antisymmetric π (spinAt 0 t i),
    ψ.antisymmetric π (spinAt 1 t i)] with z hz h0 h1
  rw [hspin] at h0 h1
  rw [heq,h0,h1] at hz
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hπ | hπ <;> simpa [hπ] using hz

private theorem Wave.gradient_row {n : ℕ} (ψ : Wave n) {c d : ℂ} {s t : Spins n}
    (h : ∀ᵐ z, c*ψ.value s z = d*ψ.value t z) (i : Fin n) (j : Fin 3) :
    ∀ᵐ z, c*ψ.gradient s z i j = d*ψ.gradient t z i j := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (((ψ.gradient_L2 s i j).const_mul c).locallyIntegrable (by norm_num))
    (((ψ.gradient_L2 t i j).const_mul d).locallyIntegrable (by norm_num))
  intro g hg hc
  have eqn := integral_congr_ae (h.mono fun z hz =>
    congrArg (fun w : ℂ => (fderiv ℝ g z (particleDirection i j)) • w) hz)
  simp only [← mul_smul_comm,integral_const_mul,ψ.weak_gradient s i j g hg hc,ψ.weak_gradient t i j g hg hc,
    mul_neg, neg_inj] at eqn
  simpa only [← mul_smul_comm,integral_const_mul] using eqn

private theorem currentPair_mul (c u z : ℂ) : currentPair (c*u) (c*z) = ‖c‖^2 * currentPair u z := by
  unfold currentPair
  rw [map_mul, show conj c*conj u*(c*z)=(c*conj c)*(conj u*z) by ring,
    Complex.mul_conj, Complex.im_ofReal_mul, ← Complex.sq_norm]

private theorem Wave.spinMomentum_at {n : ℕ} (ψ : Wave (n+1)) (a : Fin 2) (j : Fin 3) :
    ψ.spinMomentum a j = ∑ i : Fin (n+1), ∑ t : Spins n,
      ∫ z, currentPair (ψ.value (spinAt a t i) z) (ψ.gradient (spinAt a t i) z i j) := by
  rw [ψ.spinMomentum_apply,spinSum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let e := (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)).trans
    (Equiv.arrowCongr (Equiv.swap 0 i) (Equiv.refl (Fin 2)))
  have ee (p : Fin 2 × Spins n) : e p = spinAt p.1 p.2 i := by
    ext k
    simp [e,spinAt,Function.comp_def]
  let f := fun s : Spins (n+1) => ∫ z, currentPair (ψ.value s z) (ψ.gradient s z i j)
  have eqn := e.sum_comp fun s => if s i = a then f s else 0
  rw [Fintype.sum_prod_type] at eqn
  have spin (b : Fin 2) (t : Spins n) : (spinAt b t i) i = b := by simp [spinAt]
  simpa only [ee,spin,← Finset.ite_sum_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using eqn.symm

/-- If the row cψ₀−dψ₁ is zero, its spin momenta obey the same proportionality
as its populations. The result allows either c or d to vanish. -/
theorem Wave.spinMomentum_of_zero_row {n : ℕ} (ψ : Wave (n+1)) {c d : ℂ}
    (first : ∀ t : Spins n, ∀ᵐ z, c*ψ.value (Fin.cons 0 t) z = d*ψ.value (Fin.cons 1 t) z)
    (j : Fin 3) : ‖c‖^2 * ψ.spinMomentum 0 j = ‖d‖^2 * ψ.spinMomentum 1 j := by
  simp only [ψ.spinMomentum_at,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro t _
  rw [← integral_const_mul,← integral_const_mul]
  have h := ψ.swap_row t (first t) i
  apply integral_congr_ae
  filter_upwards [h,ψ.gradient_row h i j] with z hv hg
  rw [← currentPair_mul,← currentPair_mul,hv,hg]

end TSGA.ManyBody
