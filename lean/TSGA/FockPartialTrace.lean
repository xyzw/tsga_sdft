import TSGA.GeometricSpinRemoval
import TSGA.SectorOneObservable
import TSGA.SpinFockPairObservable

/-! # From the Fock partial trace to spin removal

The only Fock-theoretic input here is the partial trace over the discarded
copy and the spectral decomposition of the retained finite-sector state.
It applies to any doubled-spin wave. No contraction occurs in its statement.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker MatrixOrder ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

def PureState.positionObservable : PureState → Set Position → SpinMatrix → ℂ
  | .vacuum, _, _ => 0
  | .occupied ψ, E, A => sectorOneObservable ψ.value E A

def PureState.momentumObservable (F : SectorFourierTransform) : PureState → Set Position → SpinMatrix → ℂ
  | .vacuum, _, _ => 0
  | .occupied ψ, E, A => sectorOneObservable (F.amplitude ψ) E A

def DoubledSpinWave.fourier {n : ℕ} (w : DoubledSpinWave n) (F : SectorFourierTransform)
    (t : Fin n → SplitSpin) : Space n → ℂ := F.transform n ((w.square_integrable t).toLp (w.value t))

def DoubledSpinWave.pairObservable : {n : ℕ} → DoubledSpinWave (n+1) →
    (PairSpace → ℂ) → Matrix (SplitSpin × SplitSpin) (SplitSpin × SplitSpin) ℂ → ℂ
  | 0, _, _, _ => 0
  | _+1, w, b, A => sectorPairObservable w.value b A

/-- Spectral expansion of the partial trace onto the first copy of the
one-particle space. Its test operators are bounded spin matrices times
spectral projections or bounded two-position multipliers. The trace-class
spectral theorem supplies normalized waves in the finite-energy form domain.
All tests use the same sector decomposition. -/
def FockPartialTraceSpectralTheorem (F : SectorFourierTransform) : Prop :=
  ∀ {n : ℕ} (w : DoubledSpinWave (n+1)), ∃ d : SectorSpectralResolution,
    (∀ k, d.weight k ≠ 0 → (d.component k).particles ≤ n+1) ∧
    (∀ E, MeasurableSet E → ∀ A, HasSum (fun k => (d.weight k : ℂ) * (d.component k).positionObservable E A)
      (sectorOneObservable w.value E (retainedSpinTest A))) ∧
    (∀ E, MeasurableSet E → ∀ A, HasSum (fun k => (d.weight k : ℂ) * (d.component k).momentumObservable F E A)
      (sectorOneObservable (w.fourier F) E (retainedSpinTest A))) ∧
    (∀ b : PairSpace → ℂ, Measurable b → (∃ C : ℝ, ∀ z, ‖b z‖ ≤ C) → ∀ A,
      HasSum (fun k => (d.weight k : ℂ) * (d.component k).pairObservable b A)
        (w.pairObservable b (retainedPairTest A)))

private theorem positionProbe_zero (E : Set Position) : positionProbe E 0 = 0 := by
  ext i j
  change (∫ _ in E, (0 : ℂ)) = 0
  simp

private theorem pairProbe_zero (b : PairSpace → ℂ) : pairProbe b 0 = 0 := by
  ext i j
  change (∫ z, b z * (0 : ℂ) ∂pairVolume) = 0
  simp

private theorem vacuum_probe {ι : Type*} (X : PureState → Matrix ι ι ℂ) :
    sectorProbe (SectorSpectralResolution.ofMixedState MixedState.vacuum) X = X .vacuum := by
  ext i j
  change (∑' k : ℕ, ((if k = 0 then 1 else 0 : ℝ) : ℂ) * X .vacuum i j) = X .vacuum i j
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    rw [ite_eq_right hk,Complex.ofReal_zero,zero_mul]

private theorem position_dual (s : PureState) (E : Set Position) (A : SpinMatrix) :
    (A * positionProbe E s.matrixDensity).trace = s.positionObservable E A := by
  cases s with
  | vacuum => simp [PureState.positionObservable,PureState.matrixDensity,positionProbe_zero]
  | occupied ψ => exact ψ.position_duality E A

private theorem momentum_dual (F : SectorFourierTransform) (s : PureState) (E : Set Position) (A : SpinMatrix) :
    (A * positionProbe E (F.profile s)).trace = s.momentumObservable F E A := by
  cases s with
  | vacuum => simp [PureState.momentumObservable,SectorFourierTransform.profile,positionProbe_zero]
  | occupied ψ => exact F.momentum_duality ψ E A

private theorem trace_sandwich {ι : Type*} [Fintype ι] (S A Y : Matrix ι ι ℂ) :
    (A * (S * Y * star S)).trace = ((star S * A * S) * Y).trace := by
  calc
    _ = ((A * (S * Y)) * star S).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

private theorem spectral_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (d : SectorSpectralResolution)
    (X : PureState → Matrix ι ι ℂ) (S Y : Matrix ι ι ℂ)
    (h : ∀ A, HasSum (fun k => (d.weight k : ℂ) * (A * X (d.component k)).trace) (((star S * A * S) * Y).trace))
    (A : Matrix ι ι ℂ) : (A * sectorProbe d X).trace = ((star S * A * S) * Y).trace := by
  have he : sectorProbe d X = S * Y * star S := by
    ext i j
    have h₁ := h (Matrix.single j i 1)
    rw [← trace_sandwich] at h₁
    simpa only [Matrix.trace_single_mul,one_smul,sectorProbe] using h₁.tsum_eq
  rw [he,trace_sandwich]

/-- Apply the general partial trace to the tensor power of the explicit
isometry, then pull each bounded spin test through that tensor power. -/
theorem FockPartialTraceSpectralTheorem.geometric {F : SectorFourierTransform}
    (pt : FockPartialTraceSpectralTheorem F) : FiniteSectorGeometricLocalization F := by
  intro s U hU
  cases s with
  | vacuum =>
    refine ⟨SectorSpectralResolution.ofMixedState MixedState.vacuum,?_⟩
    constructor
    · intro k _
      exact le_rfl
    · intro E _ A
      rw [vacuum_probe]
      change (A * positionProbe E 0).trace = (_ * positionProbe E 0).trace
      simp [positionProbe_zero]
    · intro E _ A
      rw [vacuum_probe]
      change (A * positionProbe E 0).trace = (_ * positionProbe E 0).trace
      simp [positionProbe_zero]
    · intro b _ _ A
      rw [vacuum_probe]
      change (A * pairProbe b 0).trace = (_ * pairProbe b 0).trace
      simp [pairProbe_zero]
  | @occupied n ψ =>
    obtain ⟨d,hs,hx,hp,hW⟩ := pt (ψ.split U hU)
    refine ⟨d,hs,?_,?_,?_⟩
    · intro E hE A
      rw [U.compress_one]
      apply spectral_trace
      intro B
      simp_rw [position_dual]
      change HasSum _ (sectorOneObservable ψ.value E (star U.active * B * U.active))
      rw [← U.compress_one]
      exact (sectorOneObservable_pullback ψ.value U hU E B) ▸ hx E hE B
    · intro E hE A
      rw [U.compress_one]
      apply spectral_trace
      intro B
      simp_rw [momentum_dual]
      rw [show PureState.momentumObservable F (.occupied ψ) E (star U.active * B * U.active) =
          sectorOneObservable (F.amplitude ψ) E (star U.active * B * U.active) from rfl, ← U.compress_one]
      have he := sectorOneObservable_congr (F.splitAmplitude_eq ψ U) E (retainedSpinTest B)
      exact ((he.trans (sectorOneObservable_pullback (F.amplitude ψ) U hU E B)) ▸ hp E hE B)
    · intro b hb bound A
      rw [U.compress_two]
      apply spectral_trace
      intro B
      simp_rw [pure_pair_duality _ b hb bound]
      have he : (ψ.split U hU).pairObservable b (retainedPairTest B) =
          (PureState.occupied ψ).pairObservable b (star (U.active ⊗ₖ U.active) * B * (U.active ⊗ₖ U.active)) := by
        cases n with
        | zero => rfl
        | succ n => exact ψ.split_pairObservable U hU b B
      exact he ▸ hW b hb bound B

/-- The mixed-state witness required in Lemma E.1, starting from the
ordinary spectral partial trace and scalar Fourier moment identities. -/
theorem fock_partial_trace_spin_removal {F : SectorFourierTransform} (pl : SectorPlancherelMoments F)
    (pt : FockPartialTraceSpectralTheorem F) (Γ : MixedState) (S : SpinMatrix) (hS : star S * S ≤ 1) :
    let D := Γ.spinMomentumDistribution F.profile pl.pure
    ∃ Λ : MixedState, feasible (fun x => S * Γ.matrixDensity x * star S) Λ ∧
      Λ.kinetic = ((star S * S) * momentumKinetic D.profile).trace.re ∧
      Λ.interaction = (((star S * S) ⊗ₖ (star S * S)) * Γ.coulombPairMatrix).trace.re ∧
      ∀ q : Position, ⟪q,Λ.axialCurrent⟫_ℝ = D.form q S S :=
  geometric_spin_removal pl pt.geometric Γ S hS

theorem FockPartialTraceSpectralTheorem.spinCurrentTraces {F : SectorFourierTransform}
    (pt : FockPartialTraceSpectralTheorem F) (pl : SectorPlancherelMoments F) : FockSpinCurrentTraces :=
  geometric_fockSpinCurrentTraces pl pt.geometric

/-- Lemma E.1 with the retained-state traces discharged. -/
theorem FockPartialTraceSpectralTheorem.levyLieb_spin_removal {F : SectorFourierTransform}
    (pt : FockPartialTraceSpectralTheorem F) (pl : SectorPlancherelMoments F)
    {M : Position → SpinMatrix} (rep : ∃ Γ, feasible M Γ) (S : SpinMatrix) (hS : star S * S ≤ 1) :
    levyLieb (fun x => S * M x * star S) ≤ levyLieb M :=
  levyLieb_spin_removal_of_geometric_localization pl pt.geometric rep S hS

theorem FockPartialTraceSpectralTheorem.energy_ordered_cutoff {F : SectorFourierTransform}
    (pt : FockPartialTraceSpectralTheorem F) (pl : SectorPlancherelMoments F)
    {A B : SpinMatrix} (hA : A.PosSemidef) (hAB : A ≤ B) (f : Position → ℝ)
    (rep : ∃ Γ, feasible (fun x => f x • B) Γ) :
    energy (fun x => f x • A) ≤ energy (fun x => f x • B) + (B.trace.re^2 - A.trace.re^2) * hartree f :=
  energy_ordered_cutoff_of_geometric_localization pl pt.geometric hA hAB f rep

end TSGA.ManyBody
