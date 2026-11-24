import TSGA.CoulombLocalToGlobal
import TSGA.EndpointBulkTile

/-! # Freezing with the interpolated zero-wavevector gas modulus -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW Set Metric
open scoped ComplexOrder

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}

def PowerEndpointTileBound (η : Mollifier) (θ α J : ℝ) : Prop :=
  ∀ {N : Density} {R : ℝ} {c : Position} {s : SmallBallScale N R c}
    (m : SmallBallMatrices s) {F : SpinMatrix}, F.PosSemidef → F=m.low ∨ F=m.high →
    ∀ x ∈ closedBall c R, |sswEnergy energy η F 0-sswEnergy energy η (N.matrix x) 0| ≤
      J*smallGasBulk s.r (s.omega θ) θ (min 1 (α/θ))

private theorem endpoint_comparison {K p θ α J : ℝ} (P : CoulombModelInputs μ ι η)
    (L : CoulombGasInputs η K) (hθ : 0 < θ) (hJ : 0 ≤ J)
    (lip : PowerEndpointTileBound η θ α J) :
    PhaseGasComparison η .minority p θ 0 K J Phase.zero (min 1 (α/θ)) := by
  intro ε he _ D N G c s m e cn _ phase _ _ F hF sel profile support σ
  let b := smallGasBulk s.r (s.omega θ) θ (min 1 (α/θ))
  have hb : 0 ≤ b := by unfold b smallGasBulk; positivity [s.r_nonneg,s.omega_nonneg θ hθ]
  have hjb := mul_nonneg hJ hb
  have mass := bounded_cutoff_integral profile c (f := fun _ => J*b) aestronglyMeasurable_const hjb
    (ae_of_all _ fun _ _ => (abs_of_nonneg hjb).le)
  refine ⟨fun _ => J*b,L.local_cutoff_integrable P.fock.oneBody P.difference e cn phase profile c σ _ (by positivity) support,
    mass.1,?_,?_⟩
  · filter_upwards [e] with x ex
    intro cut
    change |sswEnergy energy η F 0-sswEnergy energy η (D.matrix x) 0| ≤ J*b
    rw [←ex]
    exact lip m hF sel x (support x cut)
  · obtain ⟨_,_,v,_⟩ := tilePhaseOscillation_attained phase c (inv_pos.mpr he)
    have hz : tilePhaseOscillation Phase.zero c ε⁻¹ = 0 := by simpa [Phase.zero] using v
    have coeff : J ≤ smallGasConstant J K := by unfold smallGasConstant; linarith only [hJ,L.rate.one_le]
    apply mass.2.trans
    rw [hz]
    simpa [b,BulkRegime.densityPower,Phase.zero,smallBallPhaseCost] using mul_le_mul_of_nonneg_right coeff hb

/-- The finite replacement is bounded at the native minority exponent. Only
the gas comparison uses the interpolated exponent and contributes the extra
bulk gradient term. -/
theorem CoulombModelInputs.endpoint_small_tiles {K p θ α C V a J : ℝ}
    (P : CoulombModelInputs μ ι η) (L : CoulombGasInputs η K)
    (hp : 3 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1) (hα : 0 < α) (hpθ : 2 ≤ p*θ)
    (M : MatrixSobolevMorrey p C) (vec : VectorMorreyOnBalls p V) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) (hJ : 0 ≤ J) (lip : PowerEndpointTileBound η θ α J) :
    ∃ A ≥ 1, SmallBallBoundWithError P.orientations P.frames η .minority 0 p θ C K A
      (fun φ G => φ=Phase.zero ∧ G=0)
      (fun D T ε c => (8*smallGasConstant J K)*endpointTileCost D T p (endpointBulkExponent p θ α) ε C c) := by
  obtain ⟨B,hB,hE,hI,radii⟩ := TetraPoissonLaws.radii P.poisson P.poisson_nonneg P.difference P.directional.toDifferenceBounds P.fock
  let U := smallBallScalarCoefficient P.fock.oneBody B a K p
  have hK := zero_le_one.trans L.rate.one_le
  have hU : 0 ≤ U := smallBallScalarCoefficient_nonneg P.fock.oneBody hB ha hK (by linarith)
  let Vg := smallGasConstant J K
  have hVg : 0 ≤ Vg := by dsimp only [Vg,smallGasConstant]; positivity
  let A := smallBallErrorConstant p θ C V U 0
  refine ⟨max 1 A,le_max_left ..,?_⟩
  intro D φ S T G reg phase hr allowed ε he hle admissible side profile tiles F cut c test
  obtain ⟨rfl,rfl⟩ := allowed
  have hR : 0 < 3*ε⁻¹ := by positivity
  obtain ⟨N,e,cn,powers,s,hω,⟨m⟩⟩ := smallBallMatrices_of_regular M hp hθ hθ' reg hR le_rfl c test
  have small : s.omega θ ≤ s.r^θ := hω.trans (mul_le_of_le_one_left (Real.rpow_nonneg s.r_nonneg _) (by linarith))
  let σ := tileSign side
  let H := if σ=1 then m.low else m.high
  have sel : H=m.low ∨ H=m.high := by dsimp only [H]; split <;> first | exact Or.inl rfl | exact Or.inr rfl
  have range := m.trace_range sel
  let k := ∫ x in closedBall c (3*ε⁻¹), kineticDensity S x
  have hk : 0 ≤ k := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨_,_,hz,_⟩ := tilePhaseOscillation_attained phase.regular c (inv_pos.mpr he)
  have v0 : tilePhaseOscillation Phase.zero c ε⁻¹ = 0 := by simpa [Phase.zero] using hz
  have sum := smallBallScalarCost s (0 : Position) P.fock.oneBody (by linarith : 1 ≤ p) he (by linarith)
    hB ha hK (v := 0) le_rfl hk ((div_nonneg s.r_nonneg (by norm_num : (0:ℝ) ≤ 2)).trans range.1) range.2
  let w := smallBallErrorDensity .minority D Phase.zero S T 0 p θ ε C c
  let extra := endpointTileCost D T p (endpointBulkExponent p θ α) ε C c
  let err := max 1 A*w+(8*Vg)*extra
  let raw := fun _ : Position => err-profile.directCost c
  obtain ⟨X,_,_⟩ := m.freeze_at_phase L P.fock (radii he (by linarith)) P.leibniz P.phaseProduct P.product
    (levyLiebBorel_of_lowerSemicontinuous P.lowerSemicontinuity) P.composition P.window P.orientations P.frames
    ((subset_tsupport _).trans P.support) P.difference .minority side he hle admissible ha area hE hI reg phase hr
    e cn powers hp small (P.ballComposition c _ hR) (endpoint_comparison P L hθ hJ lip) profile cut raw (by
      have est := s.error_density_bound .minority e reg phase hr M vec hp hpθ hθ hθ' he (by linarith) hC hV
        powers small (by intro h; contradiction) hU (le_refl 0)
      have expense := s.endpoint_bulk M hp hθ hα hpθ he hC reg e (powers θ hθ) small
      have pos := smallBallErrorDensity_nonneg .minority D Phase.zero S T 0 p θ he hC c
      dsimp only at est
      rw [v0] at est
      have finite := sum.trans (c := A*w) (by
        simpa only [A,w,U,k,show Phase.zero.grad c = 0 from rfl,zero_mul,add_zero,
          show 2*(3*s.omega 1)=6*s.omega 1 by ring] using est)
      have total := add_le_add (finite.trans (mul_le_mul_of_nonneg_right (le_max_right 1 A) pos))
        (mul_le_mul_of_nonneg_left expense hVg)
      simp only [v0,show Phase.zero.grad c = 0 from rfl,smallBallPhaseCost,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,
        zero_div,add_zero,BulkRegime.densityPower] at total ⊢
      dsimp only [raw,err,extra,w,σ,H,k,Vg] at total ⊢
      linarith only [total])
  have sign : σ=1 ∨ σ=-1 := by cases side <;> first | exact Or.inl rfl | exact Or.inr rfl
  have signed := X.estimate sign cut
  have sc : cutoffAverage profile.cutoff (fun x => σ*localEnergy F D Phase.zero x) c =
      σ*cutoffAverage profile.cutoff (localEnergy F D Phase.zero) c := by
    change (∫ x, (σ*localEnergy F D Phase.zero x)*profile.cutoff (c-x)) = σ*∫ x, localEnergy F D Phase.zero x*profile.cutoff (c-x)
    simp_rw [mul_assoc,integral_const_mul]
  dsimp only [TileProfile.localBase,TileProfile.directCost,raw] at signed
  rw [sc] at signed
  change σ*(_-_) ≤ err
  dsimp only [tiles,F,σ] at signed ⊢
  linarith only [signed]

end TSGA.ManyBody
