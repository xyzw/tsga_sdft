import TSGA.LevyLieb
import TSGA.SpinFockIsometry
import Mathlib.MeasureTheory.Function.L2Space

/-! # The finite-sector purification on concrete fermionic wavefunctions

The doubled-spin wave is the tensor power of a constant one-body isometry
applied to the original spin indices. Its derivatives are obtained with
the same tensor power. The discarded spin copy is still present here.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Matrix
open scoped ContDiff ComplexConjugate Matrix Kronecker

def Wave.splitValue {n : ℕ} (ψ : Wave n) (U : SpinSplitter)
    (t : Fin n → SplitSpin) (x : Space n) : ℂ :=
  ∑ s, sectorSpinTensor n (fun _ => U) t s * ψ.value s x

def Wave.splitGradient {n : ℕ} (ψ : Wave n) (U : SpinSplitter)
    (t : Fin n → SplitSpin) (x : Space n) (i : Fin n) (j : Fin 3) : ℂ :=
  ∑ s, sectorSpinTensor n (fun _ => U) t s * ψ.gradient s x i j

theorem Wave.splitValue_antisymmetric {n : ℕ} (ψ : Wave n) (U : SpinSplitter)
    (π : Equiv.Perm (Fin n)) (t : Fin n → SplitSpin) :
    ∀ᵐ x : Space n, ψ.splitValue U (t ∘ π) (x ∘ π) =
      ((Equiv.Perm.sign π : ℤˣ) : ℤ) * ψ.splitValue U t x := by
  have ha : ∀ᵐ x : Space n, ∀ s, ψ.value (s ∘ π) (x ∘ π) =
      ((Equiv.Perm.sign π : ℤˣ) : ℤ) * ψ.value s x := ae_all_iff.mpr (ψ.antisymmetric π)
  let e := Equiv.arrowCongr π.symm (Equiv.refl (Fin 2))
  filter_upwards [ha] with x hx
  rw [splitValue, ← e.sum_comp,splitValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change sectorSpinTensor _ _ (t ∘ π) (s ∘ π) * ψ.value (s ∘ π) (x ∘ π) = _
  rw [U.sector_permute,hx]
  ring

theorem Wave.splitValue_L2 {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (t : Fin n → SplitSpin) :
    MemLp (ψ.splitValue U t) 2 volume :=
  memLp_finsetSum _ fun s _ => (ψ.square_integrable s).const_mul _

/-- Any scalar linear transform on configuration-space L² commutes with
the spin splitter. This applies to the sector Fourier transform and
simultaneously identifies all doubled-spin representatives almost everywhere. -/
theorem Wave.split_transform {n : ℕ} (ψ : Wave n) (U : SpinSplitter)
    (L : Lp ℂ 2 (volume : Measure (Space n)) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Space n))) :
    ∀ᵐ p : Space n, ∀ t, L ((ψ.splitValue_L2 U t).toLp (ψ.splitValue U t)) p =
      (sectorSpinTensor n (fun _ => U) *ᵥ (fun s => L ((ψ.square_integrable s).toLp (ψ.value s)) p)) t := by
  let V (s : Spins n) := (ψ.square_integrable s).toLp (ψ.value s)
  have lc (B : Spins n → ℂ) (f : Spins n → Lp ℂ 2 (volume : Measure (Space n))) :
      ⇑(∑ s, B s • f s) =ᵐ[volume] (fun x => ∑ s, B s * f s x) := by
    apply (Lp.coeFn_fun_finsetSum _ (fun s => B s • f s)).trans
    have h : ∀ᵐ x : Space n, ∀ s, (B s • f s) x = B s * f s x :=
      ae_all_iff.mpr fun s => Lp.coeFn_smul _ _
    exact h.mono fun x hx => Finset.sum_congr rfl (fun s _ => hx s)
  apply ae_all_iff.mpr
  intro t
  let B := sectorSpinTensor n (fun _ => U) t
  have he : (ψ.splitValue_L2 U t).toLp (ψ.splitValue U t) = ∑ s, B s • V s := by
    apply Lp.ext
    apply (ψ.splitValue_L2 U t).coeFn_toLp.trans
    apply Filter.EventuallyEq.trans _ (lc B V).symm
    have hv : ∀ᵐ x : Space n, ∀ s, V s x = ψ.value s x :=
      ae_all_iff.mpr fun s => (ψ.square_integrable s).coeFn_toLp
    filter_upwards [hv] with x hx
    simp only [hx,splitValue,B]
  rw [he,map_sum]
  simp only [map_smul]
  filter_upwards [lc B (fun s => L (V s))] with p hp
  exact hp

theorem Wave.splitGradient_L2 {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (t : Fin n → SplitSpin)
    (i : Fin n) (j : Fin 3) : MemLp (fun x => ψ.splitGradient U t x i j) 2 volume :=
  memLp_finsetSum _ fun s _ => (ψ.gradient_L2 s i j).const_mul _

theorem Wave.split_weak_gradient {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (t : Fin n → SplitSpin)
    (i : Fin n) (j : Fin 3) (g : Space n → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (∫ x, (fderiv ℝ g x (particleDirection i j)) • ψ.splitValue U t x) =
      -(∫ x, g x • ψ.splitGradient U t x i j) := by
  let d := particleDirection i j
  let B := sectorSpinTensor n (fun _ => U) t
  have dl (s) : Integrable (fun x => B s * (fderiv ℝ g x d • ψ.value s x)) :=
    ((ψ.square_integrable s).locallyIntegrable (by norm_num) |>.integrable_smul_left_of_hasCompactSupport
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ d)).const_mul _
  have dr (s) : Integrable (fun x => B s * (g x • ψ.gradient s x i j)) :=
    ((ψ.gradient_L2 s i j).locallyIntegrable (by norm_num) |>.integrable_smul_left_of_hasCompactSupport
      hg.continuous hc).const_mul _
  simp only [splitValue,splitGradient,Finset.smul_sum,← mul_smul_comm]
  rw [integral_finsetSum _ (fun s _ => dl s),integral_finsetSum _ (fun s _ => dr s)]
  simp only [d,integral_const_mul,ψ.weak_gradient _ i j g hg hc,mul_neg,Finset.sum_neg_distrib]

private theorem spin_dot_norm {c : Type*} [Fintype c] (z : c → ℂ) :
    star z ⬝ᵥ z = ((∑ i, ‖z i‖^2 : ℝ) : ℂ) := by
  simp [dotProduct,Complex.conj_mul']

private theorem spin_norm_identity {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (M : Matrix a b ℂ) (h : M.conjTranspose * M = 1) (v : b → ℂ) :
    (∑ u, ‖(M *ᵥ v) u‖^2) = ∑ s, ‖v s‖^2 := by
  apply Complex.ofReal_injective
  rw [← spin_dot_norm (M *ᵥ v),← spin_dot_norm v,Matrix.star_mulVec, Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,h, Matrix.vecMul_one]

/-- Quadratic pullback under an arbitrary finite-dimensional spin map. -/
theorem spin_form_pullback {a b : Type*} [Fintype a] [Fintype b] (D : Matrix a b ℂ)
    (C : Matrix a a ℂ) (v : b → ℂ) :
    star (D *ᵥ v) ⬝ᵥ (C *ᵥ (D *ᵥ v)) =
      star v ⬝ᵥ ((D.conjTranspose * C * D) *ᵥ v) := by
  simp only [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,Matrix.mul_assoc]

/-- A spectator block on which the test is the identity disappears from the
compressed observable. The front test can act jointly on several spins. -/
theorem spin_front_pullback {a b u v : Type*} [Fintype a] [Fintype b] [Fintype u] [Fintype v]
    [DecidableEq u] [DecidableEq v] (D : Matrix a b ℂ) (T : Matrix u v ℂ)
    (hT : T.conjTranspose * T = 1) (C : Matrix a a ℂ) (z : b × v → ℂ) :
    let w := (D ⊗ₖ T) *ᵥ z
    star w ⬝ᵥ ((C ⊗ₖ (1 : Matrix u u ℂ)) *ᵥ w) =
      star z ⬝ᵥ (((D.conjTranspose * C * D) ⊗ₖ (1 : Matrix v v ℂ)) *ᵥ z) := by
  intro w
  rw [spin_form_pullback,Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul,Matrix.mul_one,hT]

/-- The first spin slot is tested, with the remaining n spins as spectators. -/
theorem SpinSplitter.first_spin_form (U : SpinSplitter) (hU : U.Isometry) (n : ℕ) (A : SpinMatrix)
    (z : Fin 2 × Spins n → ℂ) :
    let T := sectorSpinTensor n (fun _ => U)
    let w := (U ⊗ₖ T) *ᵥ z
    star w ⬝ᵥ ((retainedSpinTest A ⊗ₖ (1 : Matrix (Fin n → SplitSpin) (Fin n → SplitSpin) ℂ)) *ᵥ w) =
      star z ⬝ᵥ (((star U.active * A * U.active) ⊗ₖ (1 : Matrix (Spins n) (Spins n) ℂ)) *ᵥ z) := by
  simpa only [U.compress_one] using spin_front_pullback U _ (U.sector_isometry hU n) (retainedSpinTest A) z

/-- An arbitrary observable of the two exposed spins, including entangled
spin tests and all pair matrix units. -/
theorem SpinSplitter.first_pair_form (U : SpinSplitter) (hU : U.Isometry) (n : ℕ)
    (A : Matrix PairSpin PairSpin ℂ) (z : PairSpin × Spins n → ℂ) :
    let T := sectorSpinTensor n (fun _ => U)
    let w := ((U ⊗ₖ U) ⊗ₖ T) *ᵥ z
    star w ⬝ᵥ ((retainedPairTest A ⊗ₖ (1 : Matrix (Fin n → SplitSpin) (Fin n → SplitSpin) ℂ)) *ᵥ w) =
      star z ⬝ᵥ (((star (U.active ⊗ₖ U.active) * A * (U.active ⊗ₖ U.active)) ⊗ₖ
        (1 : Matrix (Spins n) (Spins n) ℂ)) *ᵥ z) := by
  simpa only [U.compress_two] using spin_front_pullback (U ⊗ₖ U) _ (U.sector_isometry hU n) (retainedPairTest A) z

/-- Reindexing the first spin in a sector identifies the tensor-power
wavefunction with the one-front-slot Kronecker representation. -/
theorem split_vector_cons {n : ℕ} (U : SpinSplitter) (v : Spins (n+1) → ℂ)
    (a : SplitSpin) (t : Fin n → SplitSpin) :
    (sectorSpinTensor (n+1) (fun _ => U) *ᵥ v) (Fin.cons a t) =
      ((U ⊗ₖ sectorSpinTensor n (fun _ => U)) *ᵥ
        (fun p : Fin 2 × Spins n => v (Fin.cons p.1 p.2))) (a,t) := by
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)
  rw [Matrix.mulVec,dotProduct,← e.sum_comp]
  apply Finset.sum_congr rfl
  rintro ⟨b,s⟩ _
  change (∏ i, U ((Fin.cons a t : Fin (n+1) → SplitSpin) i) ((Fin.cons b s : Spins (n+1)) i)) * v (Fin.cons b s) = _
  simp [Fin.prod_univ_succ,sectorSpinTensor]

/-- Reindexing both exposed spins identifies the physical two-spin and
spectator-block representation with the (n+2)-spin tensor wavefunction. -/
theorem split_vector_cons_cons {n : ℕ} (U : SpinSplitter) (v : Spins (n+2) → ℂ)
    (a b : SplitSpin) (t : Fin n → SplitSpin) :
    (sectorSpinTensor (n+2) (fun _ => U) *ᵥ v) (Fin.cons a (Fin.cons b t)) =
      (((U ⊗ₖ U) ⊗ₖ sectorSpinTensor n (fun _ => U)) *ᵥ
        (fun p : PairSpin × Spins n => v (Fin.cons p.1.1 (Fin.cons p.1.2 p.2)))) ((a,b),t) := by
  let e := fun k => Fin.consEquiv (fun _ : Fin (k+1) => Fin 2)
  let d := (Equiv.prodAssoc (Fin 2) (Fin 2) (Spins n)).trans
    (((Equiv.refl (Fin 2)).prodCongr (e n)).trans (e (n+1)))
  rw [Matrix.mulVec,dotProduct,← d.sum_comp]
  apply Finset.sum_congr rfl
  rintro ⟨⟨c,f⟩,s⟩ _
  change (∏ i, U ((Fin.cons a (Fin.cons b t) : Fin (n+2) → SplitSpin) i) ((Fin.cons c (Fin.cons f s) : Spins (n+2)) i)) * v (Fin.cons c (Fin.cons f s)) = _
  simp [Fin.prod_univ_succ,sectorSpinTensor,mul_assoc]

/-- The ordered product test on the doubled amplitudes is the product
of compressed spin tests on the original amplitudes, at each position. -/
theorem Wave.split_product_test {n : ℕ} (ψ : Wave n) (U : SpinSplitter)
    (A : Fin n → Matrix SplitSpin SplitSpin ℂ) (x : Space n) :
    let v := fun s => ψ.value s x
    let w := fun t => ψ.splitValue U t x
    star w ⬝ᵥ (sectorSpinTensor n A *ᵥ w) =
      star v ⬝ᵥ (sectorSpinTensor n (fun i => U.conjTranspose * A i * U) *ᵥ v) := by
  intro v w
  let D := sectorSpinTensor n (fun _ => U)
  change star (D *ᵥ v) ⬝ᵥ (sectorSpinTensor n A *ᵥ (D *ᵥ v)) = _
  rw [spin_form_pullback, ← U.sector_compress]

theorem Wave.split_norm {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (hU : U.Isometry) (x : Space n) :
    (∑ t, ‖ψ.splitValue U t x‖^2) = ∑ s, ‖ψ.value s x‖^2 :=
  spin_norm_identity _ (U.sector_isometry hU n) (fun s => ψ.value s x)

theorem Wave.split_gradient_norm {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (hU : U.Isometry)
    (x : Space n) (i : Fin n) (j : Fin 3) :
    (∑ t, ‖ψ.splitGradient U t x i j‖^2) = ∑ s, ‖ψ.gradient s x i j‖^2 :=
  spin_norm_identity _ (U.sector_isometry hU n) (fun s => ψ.gradient s x i j)

theorem Wave.split_normalized {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (hU : U.Isometry) :
    (∑ t, ∫ x, ‖ψ.splitValue U t x‖^2) = 1 := by
  calc
    _ = ∫ x, ∑ t, ‖ψ.splitValue U t x‖^2 :=
      (integral_finsetSum _ fun t _ => (memLp_two_iff_integrable_sq_norm (ψ.splitValue_L2 U t).1).1 (ψ.splitValue_L2 U t)).symm
    _ = _ := by
      simp_rw [ψ.split_norm U hU]
      rw [integral_finsetSum _ fun s _ => (memLp_two_iff_integrable_sq_norm (ψ.square_integrable s).1).1 (ψ.square_integrable s)]
      exact ψ.normalized

/-- On the doubled wave the isometry preserves the full kinetic integrand
before any particle is traced out. -/
theorem Wave.split_kinetic {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (hU : U.Isometry) :
    (∑ t, ∫ x, ∑ i, ∑ j, ‖ψ.splitGradient U t x i j‖^2) = ψ.kinetic := by
  have hi (t : Fin n → SplitSpin) (i : Fin n) (j : Fin 3) :
      Integrable (fun x => ‖ψ.splitGradient U t x i j‖^2) :=
    (ψ.splitGradient_L2 U t i j).integrable_norm_pow (p := 2) (by decide)
  have hj (s : Spins n) (i : Fin n) (j : Fin 3) :
      Integrable (fun x => ‖ψ.gradient s x i j‖^2) :=
    (ψ.gradient_L2 s i j).integrable_norm_pow (p := 2) (by decide)
  rw [← integral_finsetSum _ (fun t _ => integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => hi t i j)]
  unfold Wave.kinetic sectorIntegral
  rw [← integral_finsetSum _ (fun s _ => integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => hj s i j)]
  apply integral_congr_ae (ae_of_all _ fun x => ?_)
  calc
    _ = ∑ i, ∑ j, ∑ t, ‖ψ.splitGradient U t x i j‖^2 := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ s, ‖ψ.gradient s x i j‖^2 := by simp only [ψ.split_gradient_norm U hU]
    _ = _ := by
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Spins n)))]; apply Finset.sum_congr rfl
      intro i _; rw [Finset.sum_comm]

theorem Wave.split_coulomb_integrable {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (hU : U.Isometry)
    (t : Fin n → SplitSpin) : Integrable (fun x => coulomb x * ‖ψ.splitValue U t x‖^2) := by
  have htot : Integrable (fun x => ∑ s, coulomb x * ‖ψ.value s x‖^2) :=
    integrable_finsetSum _ (fun s _ => ψ.interaction_integrable s)
  have hm : Measurable (coulomb : Space n → ℝ) := by unfold coulomb; fun_prop
  apply htot.mono' (hm.aestronglyMeasurable.mul ((ψ.splitValue_L2 U t).1.norm.pow _))
  filter_upwards with x
  change ‖coulomb x * ‖ψ.splitValue U t x‖^2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (coulomb_nonneg x) (sq_nonneg _)),← Finset.mul_sum,← ψ.split_norm U hU]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun a _ => sq_nonneg ‖ψ.splitValue U a x‖) (Finset.mem_univ t)) (coulomb_nonneg x)

theorem Wave.split_interaction {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (hU : U.Isometry) :
    (∑ t, ∫ x, coulomb x * ‖ψ.splitValue U t x‖^2) = ψ.interaction := by
  unfold Wave.interaction sectorIntegral
  rw [← integral_finsetSum _ (fun t _ => ψ.split_coulomb_integrable U hU t),
      ← integral_finsetSum _ (fun s _ => ψ.interaction_integrable s)]
  simp_rw [← Finset.mul_sum,ψ.split_norm U hU]

/-- A normalized fermionic vector on the direct sum of the retained and
discarded one-particle spaces, before taking the Fock partial trace. -/
structure DoubledSpinWave (n : ℕ) where
  value : (Fin n → SplitSpin) → Space n → ℂ
  gradient : (Fin n → SplitSpin) → Space n → Fin n → Fin 3 → ℂ
  antisymmetric : ∀ π : Equiv.Perm (Fin n), ∀ t, ∀ᵐ x : Space n,
    value (t ∘ π) (x ∘ π) = ((Equiv.Perm.sign π : ℤˣ) : ℤ) * value t x
  square_integrable : ∀ t, MemLp (value t) 2 volume
  normalized : (∑ t, ∫ x, ‖value t x‖^2) = 1
  gradient_L2 : ∀ t i j, MemLp (fun x => gradient t x i j) 2 volume
  weak_gradient : ∀ t i j (g : Space n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
    (∫ x, (fderiv ℝ g x (particleDirection i j)) • value t x) = -(∫ x, g x • gradient t x i j)
  interaction_integrable : ∀ t, Integrable (fun x => coulomb x * ‖value t x‖^2)

def Wave.split {n : ℕ} (ψ : Wave n) (U : SpinSplitter) (hU : U.Isometry) : DoubledSpinWave n where
  value := ψ.splitValue U
  gradient := ψ.splitGradient U
  antisymmetric := ψ.splitValue_antisymmetric U
  square_integrable := ψ.splitValue_L2 U
  normalized := ψ.split_normalized U hU
  gradient_L2 := ψ.splitGradient_L2 U
  weak_gradient := ψ.split_weak_gradient U
  interaction_integrable := ψ.split_coulomb_integrable U hU

end TSGA.ManyBody
