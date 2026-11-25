import TSGA.SectorFourierSplit
import TSGA.SectorPairObservable

/-! # Retained one-particle observables on a doubled-spin wave -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker MatrixOrder Matrix.Norms.L2Operator

/-- Test the first spin slot and integrate over the spectator variables.
Both exclusion and retention are encoded by the spin matrix of the test. -/
def sectorOneObservable {a : Type*} [Fintype a] [DecidableEq a] {n : ℕ}
    (v : (Fin (n+1) → a) → Space (n+1) → ℂ) (E : Set Position) (A : Matrix a a ℂ) : ℂ :=
  (n+1 : ℕ) * ∫ x in E, ∫ y : Space n,
    let z := fun t : a × (Fin n → a) => v (Fin.cons t.1 t.2) (Fin.cons x y)
    star z ⬝ᵥ ((A ⊗ₖ (1 : Matrix (Fin n → a) (Fin n → a) ℂ)) *ᵥ z)

private theorem front_preserves (n : ℕ) : MeasurePreserving (fun p : Position × Space n => Fin.cons p.1 p.2)
    (volume.prod volume) (volume : Measure (Space (n+1))) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Position) 0
  have he : (fun p : Position × Space n => Fin.cons p.1 p.2) = e.symm := by
    funext p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply]
  rw [he]
  exact (volume_preserving_piFinSuccAbove (fun _ => Position) 0).symm

private def oneMarginal {n : ℕ} (v : Spins (n+1) → Space (n+1) → ℂ) (x : Position) : SpinMatrix :=
  fun i j => (n+1 : ℕ) * ∑ s : Spins n, ∫ y : Space n,
    v (Fin.cons i s) (Fin.cons x y) * conj (v (Fin.cons j s) (Fin.cons x y))

private theorem one_duality {n : ℕ} (v : Spins (n+1) → Space (n+1) → ℂ)
    (hv : ∀ t, MemLp (v t) 2 volume) (E : Set Position) (A : SpinMatrix) :
    (A * positionProbe E (oneMarginal v)).trace = sectorOneObservable v E A := by
  let f (i j : Fin 2) (s : Spins n) (p : Position × Space n) :=
    v (Fin.cons j s) (Fin.cons p.1 p.2) * conj (v (Fin.cons i s) (Fin.cons p.1 p.2))
  have h (i j : Fin 2) (s : Spins n) : Integrable (f i j s) (volume.prod volume) := by
    have hj := (hv (Fin.cons j s)).comp_measurePreserving (front_preserves n)
    have hi := (hv (Fin.cons i s)).comp_measurePreserving (front_preserves n)
    apply hj.integrable_mul (q := 2)
    exact hi.star
  have ha : ∀ᵐ x : Position, ∀ i j s, Integrable (fun y : Space n => f i j s (x,y)) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr fun s => (h i j s).prod_right_ae
  have hi (i j : Fin 2) (s : Spins n) := (h i j s).integral_prod_left
  have hs (i j : Fin 2) (s : Spins n) := (hi i j s).const_mul (A i j)
  have hinner : ∀ᵐ x : Position, (∫ y : Space n, let z := fun t : Fin 2 × Spins n => v (Fin.cons t.1 t.2) (Fin.cons x y)
      star z ⬝ᵥ ((A ⊗ₖ (1 : Matrix (Spins n) (Spins n) ℂ)) *ᵥ z)) =
      ∑ i, ∑ j, ∑ s, A i j * ∫ y : Space n, f i j s (x,y) := by
    filter_upwards [ha] with x hx
    simp only [spinFrontForm_entries]
    change (∫ y : Space n, ∑ i, ∑ j, ∑ s, A i j * f i j s (x,y)) = _
    have H (i j : Fin 2) (s : Spins n) := (hx i j s).const_mul (A i j)
    simp only [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun s _ => H i j s),
      integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun s _ => H _ j s),integral_finsetSum _ (fun s _ => H _ _ s),integral_const_mul]
  rw [sectorOneObservable, integral_congr_ae (ae_restrict_of_ae hinner)]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,positionProbe,oneMarginal,integral_const_mul]
  change (∑ i, ∑ j, A i j * ((n+1 : ℕ) * ∫ x in E, ∑ s, ∫ y, f i j s (x,y))) = _
  simp only [integral_finsetSum _ (fun s _ => (hi _ _ s).integrableOn),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun s _ => (hs i j s).integrableOn),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun s _ => (hs _ j s).integrableOn),
    integral_finsetSum _ (fun s _ => (hs _ _ s).integrableOn),integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem Wave.position_duality {n : ℕ} (ψ : Wave (n+1)) (E : Set Position) (A : SpinMatrix) :
    (A * positionProbe E ψ.matrixDensity).trace = sectorOneObservable ψ.value E A :=
  one_duality _ ψ.square_integrable E A

theorem SectorFourierTransform.momentum_duality (F : SectorFourierTransform) {n : ℕ} (ψ : Wave (n+1))
    (E : Set Position) (A : SpinMatrix) : (A * positionProbe E (F.profile (.occupied ψ))).trace =
      sectorOneObservable (F.amplitude ψ) E A :=
  one_duality (F.amplitude ψ) (fun s => Lp.memLp (F.transform (n+1) ((ψ.square_integrable s).toLp (ψ.value s)))) E A

theorem sectorOneObservable_pullback {n : ℕ} (v : Spins (n+1) → Space (n+1) → ℂ)
    (U : SpinSplitter) (hU : U.Isometry) (E : Set Position) (A : SpinMatrix) :
    sectorOneObservable (fun t x => (sectorSpinTensor (n+1) (fun _ => U) *ᵥ (fun s => v s x)) t) E (retainedSpinTest A) =
    sectorOneObservable v E (U.conjTranspose * retainedSpinTest A * U) := by
  unfold sectorOneObservable
  congr 1
  apply integral_congr_ae (ae_of_all _ fun x => ?_)
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [split_vector_cons,U.compress_one]
  exact U.first_spin_form hU n A _

theorem sectorOneObservable_congr {a : Type*} [Fintype a] [DecidableEq a] {n : ℕ}
    {v w : (Fin (n+1) → a) → Space (n+1) → ℂ} (h : ∀ t, v t =ᵐ[volume] w t)
    (E : Set Position) (A : Matrix a a ℂ) : sectorOneObservable v E A = sectorOneObservable w E A := by
  have ha : ∀ᵐ z : Space (n+1), ∀ t, v t z = w t z := ae_all_iff.mpr h
  have hc : ∀ᵐ p : Position × Space n ∂volume.prod volume,
      ∀ t, v t (Fin.cons p.1 p.2) = w t (Fin.cons p.1 p.2) :=
    (front_preserves n).quasiMeasurePreserving.ae ha
  have hs := Measure.ae_ae_of_ae_prod hc
  unfold sectorOneObservable
  apply congrArg (fun z : ℂ => (n+1 : ℕ) * z)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hs] with x hx
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  exact congrArg (fun z => star z ⬝ᵥ ((A ⊗ₖ (1 : Matrix (Fin n → a) (Fin n → a) ℂ)) *ᵥ z))
    (funext fun t : a × (Fin n → a) => hy (Fin.cons t.1 t.2))

end TSGA.ManyBody
