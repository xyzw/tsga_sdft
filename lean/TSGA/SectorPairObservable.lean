import TSGA.CoulombSpinPair

/-! # Testing the two-particle marginal on a full sector wavefunction

For the multiplier `b(x₁,x₂) A`, symmetry allows one to select the first
two coordinates and multiply by the number of unordered pairs. The
remaining spin indices are summed and all particle positions integrated.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker

private def pairSectorEntry {n : ℕ} (ψ : Wave (n+2)) (b : PairSpace → ℂ)
    (i j : Fin 2 × Fin 2) : ℂ :=
  ((((n+2:ℕ):ℝ) * ((n+1:ℕ):ℝ)/2 : ℝ) : ℂ) * ∑ t : Spins n, ∫ x : Space (n+2),
    b (x 0,x 1) * (ψ.value (Fin.cons i.1 (Fin.cons i.2 t)) x *
      conj (ψ.value (Fin.cons j.1 (Fin.cons j.2 t)) x))

/-- Two selected spins, with the identity on the spectator spin space. -/
def sectorPairObservable {n : ℕ} {a : Type*} [Fintype a] [DecidableEq a]
    (v : (Fin (n+2) → a) → Space (n+2) → ℂ) (b : PairSpace → ℂ)
    (A : Matrix (a × a) (a × a) ℂ) : ℂ :=
  ((((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)/2 : ℝ) : ℂ) * ∫ x : Space (n+2),
    let z := fun p : (a × a) × (Fin n → a) => v (Fin.cons p.1.1 (Fin.cons p.1.2 p.2)) x
    b (x 0,x 1) * (star z ⬝ᵥ ((A ⊗ₖ (1 : Matrix (Fin n → a) (Fin n → a) ℂ)) *ᵥ z))

/-- Spin matrix coefficients of an observable acting trivially on the spectator space. -/
theorem spinFrontForm_entries {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (A : Matrix ι ι ℂ) (z : ι × σ → ℂ) :
    star z ⬝ᵥ ((A ⊗ₖ (1 : Matrix σ σ ℂ)) *ᵥ z) =
      ∑ i, ∑ j, ∑ t, A i j * (z (j,t) * conj (z (i,t))) := by
  have hm (i t) : ((A ⊗ₖ (1 : Matrix σ σ ℂ)) *ᵥ z) (i,t) = ∑ j, A i j * z (j,t) := by
    simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply,mul_ite,ite_mul]
  simp only [dotProduct,Fintype.sum_prod_type,hm,Pi.star_apply,Complex.star_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => by ring

/-- Expectation of a spin-resolved two-body multiplication operator in
the occupied wave. The first exposed spin in the ket carries index j. -/
def PureState.pairObservable : PureState → (PairSpace → ℂ) → PairSpinMatrix → ℂ
  | .vacuum, _, _ => 0
  | .occupied (n:=0) _, _, _ => 0
  | .occupied (n:=_+1) ψ, b, A => sectorPairObservable ψ.value b A

private theorem pairProbe_wave {n : ℕ} (ψ : Wave (n+2)) (b : PairSpace → ℂ) (hb : Measurable b)
    (B : ℝ) (bound : ∀ z, ‖b z‖ ≤ B) (i j : Fin 2 × Fin 2) :
    pairProbe b ψ.pairDensitySpin i j = pairSectorEntry ψ b i j := by
  let g (t : Spins n) (x : Space (n+2)) := ψ.value (Fin.cons i.1 (Fin.cons i.2 t)) x *
    conj (ψ.value (Fin.cons j.1 (Fin.cons j.2 t)) x)
  have hg (t) : Integrable (g t) := by
    have h := ψ.square_integrable (Fin.cons j.1 (Fin.cons j.2 t))
    have hc : MemLp (fun x => conj (ψ.value (Fin.cons j.1 (Fin.cons j.2 t)) x)) 2 volume :=
      h.of_le (Complex.continuous_conj.comp_aestronglyMeasurable h.1) (ae_of_all _ fun x => (Complex.norm_conj _).le)
    exact (ψ.square_integrable (Fin.cons i.1 (Fin.cons i.2 t))).integrable_mul hc
  let G (t : Spins n) (z : PairSpace) := b z * ∫ y : Space n, g t (Fin.cons z.1 (Fin.cons z.2 y))
  have hG (t) : Integrable (G t) pairVolume := by
    have h := ((splitPair_preserving n).integrable_comp_emb (splitPair n).measurableEmbedding).2 (hg t)
    apply Integrable.bdd_mul _ hb.aestronglyMeasurable (ae_of_all _ bound)
    simpa only [Function.comp_def,splitPair_apply] using h.integral_prod_left
  have hslice (t) : (∫ z, G t z ∂pairVolume) = ∫ x : Space (n+2), b (x 0,x 1) * g t x := by
    let F (x : Space (n+2)) := b (x 0,x 1) * g t x
    have hF : Integrable F := (hg t).bdd_mul
      (hb.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))).aestronglyMeasurable
      (ae_of_all _ (fun x => bound (x 0,x 1)))
    have hp := splitPair_preserving n
    have h := (hp.integrable_comp_emb (splitPair n).measurableEmbedding).2 hF
    have he := (integral_prod (F ∘ splitPair n) h).symm.trans (hp.integral_comp' F)
    have h1 (z : PairSpace) (y : Space n) : (Fin.cons z.1 (Fin.cons z.2 y) : Space (n+2)) 1 = z.2 := rfl
    simpa only [F,G,Function.comp_def,splitPair_apply,Fin.cons_zero,h1,integral_const_mul,Prod.mk.eta] using he
  let c := ((n+2:ℕ):ℝ) * ((n+1:ℕ):ℝ)/2
  have he (z : PairSpace) : b z * ψ.pairDensitySpin z i j = (c : ℂ) * ∑ t, G t z := by
    simp only [Wave.pairDensitySpin,Matrix.smul_apply,Matrix.sum_apply,Matrix.of_apply,
      Complex.real_smul, pairAmplitude, G,g,c,← Finset.mul_sum]
    ring
  change (∫ z, b z * ψ.pairDensitySpin z i j ∂pairVolume) = _
  simp only [he,integral_const_mul,integral_finsetSum _ (fun t _ => hG t),hslice]
  rfl

theorem pure_pair_duality (s : PureState) (b : PairSpace → ℂ) (hb : Measurable b)
    (bounded : ∃ C : ℝ, ∀ z, ‖b z‖ ≤ C) (A : PairSpinMatrix) :
    (A * pairProbe b s.pairDensitySpin).trace = s.pairObservable b A := by
  obtain ⟨B,hB⟩ := bounded
  cases s with
  | vacuum => simp [PureState.pairDensitySpin,PureState.pairObservable,pairProbe,Matrix.trace,Matrix.mul_apply]
  | @occupied n ψ => cases n with
    | zero => simp [PureState.pairDensitySpin,PureState.pairObservable,pairProbe,Matrix.trace,Matrix.mul_apply]
    | succ n =>
      let z (x : Space (n+2)) (p : (Fin 2 × Fin 2) × Spins n) :=
        ψ.value (Fin.cons p.1.1 (Fin.cons p.1.2 p.2)) x
      let G (i j : Fin 2 × Fin 2) (t : Spins n) (x : Space (n+2)) :=
        b (x 0,x 1) * (z x (j,t) * conj (z x (i,t)))
      have H (i j : Fin 2 × Fin 2) (t : Spins n) : Integrable (fun x => A i j * G i j t x) := by
        have h := ψ.square_integrable (Fin.cons i.1 (Fin.cons i.2 t))
        have hc : MemLp (fun x => conj (z x (i,t))) 2 volume :=
          h.of_le (Complex.continuous_conj.comp_aestronglyMeasurable h.1) (ae_of_all _ fun _ => (Complex.norm_conj _).le)
        have hj := ψ.square_integrable (Fin.cons j.1 (Fin.cons j.2 t))
        exact ((hj.integrable_mul hc).bdd_mul
          (hb.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))).aestronglyMeasurable
          (ae_of_all _ fun x => hB (x 0,x 1))).const_mul _
      have e (x : Space (n+2)) : b (x 0,x 1) * (star (z x) ⬝ᵥ
          ((A ⊗ₖ (1 : Matrix (Spins n) (Spins n) ℂ)) *ᵥ z x)) =
          ∑ i, ∑ j, ∑ t, A i j * G i j t x := by
        simp only [spinFrontForm_entries,Finset.mul_sum,G]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun t _ => by ring
      change (A * pairProbe b ψ.pairDensitySpin).trace = sectorPairObservable ψ.value b A
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,pairProbe_wave ψ b hb B hB]
      unfold sectorPairObservable
      change _ = _ * ∫ x, b (x 0,x 1) * (star (z x) ⬝ᵥ ((A ⊗ₖ (1 : Matrix (Spins n) (Spins n) ℂ)) *ᵥ z x))
      simp only [e,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        integrable_finsetSum _ fun t _ => H i j t)),integral_finsetSum _ (fun j _ =>
          integrable_finsetSum _ fun t _ => H _ j t),integral_finsetSum _ (fun t _ => H _ _ t),
        integral_const_mul,pairSectorEntry,Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => by
        dsimp [G,z]
        ring

end TSGA.ManyBody
