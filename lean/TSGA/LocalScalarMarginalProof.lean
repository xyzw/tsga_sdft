import TSGA.LocalRotationMarginal
import TSGA.ParticleNumber
import TSGA.MarginalPositivity

/-! # Scalar one-body tests of concrete Coulomb mixed states -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped ComplexOrder

private def spinSum {n : ℕ} (ψ : Wave n) (x : Space n) := ∑ s, ‖ψ.value s x‖^2

private theorem spinSum_symm {n : ℕ} (ψ : Wave n) (π : Equiv.Perm (Fin n)) :
    ∀ᵐ x, spinSum ψ (x ∘ π) = spinSum ψ x := by
  let e := Equiv.arrowCongr π.symm (Equiv.refl (Fin 2))
  filter_upwards [ae_all_iff.mpr (ψ.antisymmetric π)] with x hx
  unfold spinSum
  rw [← e.sum_comp (fun s => ‖ψ.value s (x ∘ π)‖^2)]
  apply Finset.sum_congr rfl
  intro s _
  change ‖ψ.value (s ∘ π) (x ∘ π)‖^2 = _
  rw [hx s,norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

private theorem trace_slice {n : ℕ} (ψ : Wave (n+1)) :
    ∀ᵐ x, (ψ.matrixDensity x).trace.re = (n+1 : ℕ)*(∫ y : Space n, spinSum ψ (Fin.cons x y)) := by
  filter_upwards [ψ.square_integrable_slices] with x hx
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)
  have h (y : Space n) := e.sum_comp (fun s => ‖ψ.value s (Fin.cons x y)‖^2)
  simp only [Fintype.sum_prod_type] at h
  change ∀ y, (∑ a : Fin 2, ∑ s : Spins n, ‖ψ.value (Fin.cons a s) (Fin.cons x y)‖^2) = spinSum ψ (Fin.cons x y) at h
  have hi (a : Fin 2) (s : Spins n) := (hx a s).integrable_norm_pow (p := 2) (by decide)
  simp only [← h,integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun s _ => hi a s),
    integral_finsetSum _ (fun s _ => hi _ s)]
  simp [Wave.matrixDensity,Matrix.trace,Matrix.diag,Complex.mul_conj,Complex.sq_norm,integral_complex_ofReal,
    Finset.mul_sum,mul_add]

/-- Weighting the first-coordinate marginal and permuting that coordinate
into each slot gives the expectation of the full multiplication operator. -/
private theorem wave_scalar_mass {n : ℕ} (ψ : Wave (n+1)) {w : Position → ℝ} (hm : AEMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (hi : Integrable (fun x => (ψ.matrixDensity x).trace.re * w x)) :
    Integrable (ψ.localMassDensity w) ∧ (∫ x, ψ.localMassDensity w x) = ∫ x, (ψ.matrixDensity x).trace.re*w x := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Position) 0
  have he : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Space (n+1))) := (volume_preserving_piFinSuccAbove _ 0).symm
  have econs (z : Position × Space n) : e.symm z = Fin.cons z.1 z.2 := by
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply]
  let f := fun i (z : Space (n+1)) => w (z i)*spinSum ψ z
  let g := fun p : Position × Space n => spinSum ψ (Fin.cons p.1 p.2)
  have hsp : Integrable (spinSum ψ) := integrable_finsetSum _ fun s _ =>
    (ψ.square_integrable s).integrable_norm_pow (p := 2) (by decide)
  have hG : Integrable g (volume.prod volume) := by
    simpa only [Function.comp_def,g,econs] using (he.integrable_comp_emb e.symm.measurableEmbedding).2 hsp
  have hsub : (fun x : Position => (∫ y, g (x,y))*w x) =ᵐ[volume] (fun x => ((n+1:ℕ):ℝ)⁻¹*((ψ.matrixDensity x).trace.re*w x)) := by
    filter_upwards [trace_slice ψ] with x hx
    rw [hx]
    dsimp only [g]
    field_simp
  have intg := (hi.const_mul ((n+1:ℕ):ℝ)⁻¹).congr hsub.symm
  have hfn (p : Position × Space n) : 0 ≤ w p.1*g p :=
    mul_nonneg (hn p.1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have intprod : Integrable (fun p : Position × Space n => w p.1*g p) (volume.prod volume) := by
    apply (integrable_prod_iff ((hm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).aestronglyMeasurable.mul hG.1)).2
    refine ⟨hG.prod_right_ae.mono (fun x hx => hx.const_mul (w x)),?_⟩
    change Integrable (fun x => ∫ y : Space n, ‖w x*g (x,y)‖)
    have eqn (x : Position) (y : Space n) : ‖w x*g (x,y)‖ = w x*g (x,y) := Real.norm_of_nonneg (hfn (x,y))
    simpa only [eqn,integral_const_mul,mul_comm] using intg
  have fi0 : Integrable (f 0) := by
    apply (he.integrable_comp_emb e.symm.measurableEmbedding).1
    change Integrable (fun p => f 0 (e.symm p)) (volume.prod volume)
    simpa only [f,g,econs,Fin.cons_zero] using intprod
  have F0 : (∫ z, f 0 z) = ∫ x, w x*(∫ y, g (x,y)) := by
    rw [← he.integral_comp' (f 0)]
    change (∫ p : Position × Space n, f 0 (e.symm p) ∂volume.prod volume) = _
    simpa only [f,econs,Fin.cons_zero,g,integral_const_mul] using integral_prod _ intprod
  have perm (i : Fin (n+1)) : Integrable (f i) ∧ (∫ z, f i z) = ∫ z, f 0 z := by
    let π := Equiv.swap 0 i
    let T := MeasurableEquiv.piCongrLeft (fun _ : Fin (n+1) => Position) π.symm
    have hT : MeasurePreserving T := volume_measurePreserving_piCongrLeft _ _
    have coord (z : Space (n+1)) : T z = z ∘ π := by ext k; simp [T,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
    have eqf : (fun z => f 0 (T z)) =ᵐ[volume] f i := by
      filter_upwards [spinSum_symm ψ π] with z hz
      simp only [f,coord,hz,Function.comp_apply,π,Equiv.swap_apply_left]
    exact ⟨((hT.integrable_comp_emb T.measurableEmbedding).2 fi0).congr eqf,
      (integral_congr_ae eqf.symm).trans (hT.integral_comp' _)⟩
  refine ⟨integrable_finsetSum _ (fun i _ => (perm i).1),?_⟩
  change (∫ x, ∑ i, f i x) = _
  rw [integral_finsetSum _ (fun i _ => (perm i).1)]
  simp only [(perm _).2,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,F0]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [trace_slice ψ] with x hx
  rw [hx]
  dsimp only [g]
  ring

private theorem pure_scalar_mass (p : PureState) {w : Position → ℝ} (hm : AEMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (hi : Integrable (fun x => (p.matrixDensity x).trace.re*w x)) :
    p.localMassFinite w ∧ p.localMass w = ∫ x, (p.matrixDensity x).trace.re*w x := by
  cases p with
  | vacuum => simp [PureState.localMass,PureState.localMassFinite,PureState.matrixDensity]
  | occupied ψ => exact wave_scalar_mass ψ hm hn hi

/-- The scalar marginal law for every admissible normal mixed state,
including unbounded nonnegative multiplication operators. -/
theorem localScalarMarginal : LocalScalarMarginal := by
  intro Γ D hΓ w hm hn hi
  let f := fun k x => Γ.weight k * ((Γ.component k).matrixDensity x).trace.re * w x
  have sum : ∀ᵐ x, HasSum (fun k => f k x) (D.charge x*w x) := by
    filter_upwards [Γ.density_summable,hΓ] with x hx he
    have hh : HasSum (fun k => Γ.weight k*((Γ.component k).matrixDensity x).trace.re) ((Γ.matrixDensity x).trace.re) := by
      simpa only [MixedState.matrixDensity,Matrix.trace_fin_two,Complex.add_re,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,mul_add] using
        Complex.hasSum_re ((hx 0 0).hasSum.add (hx 1 1).hasSum)
    rw [he] at hh
    exact hh.mul_right _
  have meas (k) : AEStronglyMeasurable (f k) volume := by
    have H : Integrable (fun x => ((Γ.component k).matrixDensity x).trace.re) := by
      cases Γ.component k with
      | vacuum => simp [PureState.matrixDensity]
      | occupied ψ => exact ψ.particleNumber.1
    exact (aestronglyMeasurable_const.mul H.1).mul hm.aestronglyMeasurable
  have pos : ∀ᵐ x, ∀ k, 0 ≤ f k x := ae_all_iff.mpr fun k => ((Γ.component k).matrixDensity_posSemidef).mono
    fun x hp => mul_nonneg (mul_nonneg (Γ.weight_nonneg k) (RCLike.nonneg_iff.mp hp.trace_nonneg).1) (hn x)
  have ints (k) : Integrable (f k) := hi.mono' (meas k) (by
    filter_upwards [pos,sum] with x hp hs
    rw [Real.norm_of_nonneg (hp k),← hs.tsum_eq]
    exact hs.summable.le_tsum k fun j _ => hp j)
  have each (k) (hk : 0 < Γ.weight k) : (Γ.component k).localMassFinite w ∧
      (Γ.component k).localMass w = ∫ x, ((Γ.component k).matrixDensity x).trace.re*w x := by
    apply pure_scalar_mass _ hm hn
    have I := (ints k).const_mul (Γ.weight k)⁻¹
    simpa only [f,← mul_assoc,inv_mul_cancel₀ hk.ne',one_mul] using I
  refine ⟨fun k hk => (each k hk).1,?_⟩
  have hs := hasSum_integral_of_dominated_convergence (F := f) f meas
    (fun k => pos.mono fun x h => (Real.norm_of_nonneg (h k)).le)
    (sum.mono fun x h => h.summable) (hi.congr (sum.mono fun x h => h.tsum_eq.symm)) sum
  apply hs.congr_fun
  intro k
  by_cases hk : Γ.weight k = 0
  · simp [f,hk]
  · rw [(each k (lt_of_le_of_ne (Γ.weight_nonneg k) (Ne.symm hk))).2,← integral_const_mul]
    apply integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only [f]
    ring

end TSGA.ManyBody
