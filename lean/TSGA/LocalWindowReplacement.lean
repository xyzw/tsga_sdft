import TSGA.FreeWindowReplacement

/-! # Application of the free-window estimate to local Sobolev data

The analytic input is ordinary Sobolev reflection and cutoff on a ball, stated for
arbitrary matrix-valued functions. Using one spatial reflection and one nonnegative
cutoff for every spectral power preserves positivity and both weak gradients on K.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW Set Metric
open scoped ComplexOrder MatrixOrder

/-- Reflection across a ball in a collar followed by a compact smooth cutoff.
The cutoff is chosen flat at its outer boundary so that every positive power may
be used. The Sobolev pullback rule concerns arbitrary functions and exponents. -/
structure BallSobolevReflection (c : Position) (R : ℝ) where
  mirror : Position → Position
  continuous : Continuous mirror
  range : ∀ x, mirror x ∈ closedBall c R
  fixes : ∀ x ∈ closedBall c R, mirror x = x
  cutoff : Position → ℝ
  nonneg : ∀ x, 0 ≤ cutoff x
  cutoff_cont : Continuous cutoff
  compact : HasCompactSupport cutoff
  one : ∀ x ∈ closedBall c R, cutoff x = 1
  pullback : ∀ (u : Position → SpinMatrix) (G : MatrixGradient) (a q : ℝ), 0 < a → 1 ≤ q →
    ContinuousOn u (closedBall c R) → IsMatrixGradientOn (ball c R) u G →
    MemLp (matrixGradNorm G) (ENNReal.ofReal q) (volume.restrict (ball c R)) → ∃ J : MatrixGradient,
      IsMatrixGradientOn univ (fun x => (cutoff x)^a • u (mirror x)) J ∧
      MemLp (matrixGradNorm J) (ENNReal.ofReal q) ∧ J =ᵐ[volume.restrict (closedBall c R)] G

private def BallSobolevReflection.lift {c : Position} {R : ℝ} (H : BallSobolevReflection c R) (D : Density) : Density where
  matrix x := H.cutoff x • D.matrix (H.mirror x)
  positive x := (D.positive (H.mirror x)).smul (H.nonneg x)

private theorem BallSobolevReflection.lift_power {c : Position} {R : ℝ} (H : BallSobolevReflection c R)
    (D : Density) (a : ℝ) : (H.lift D).power a = fun x => (H.cutoff x)^a • D.power a (H.mirror x) := by
  funext _
  exact positive_power_smul (D.positive _) (H.nonneg _) a

open scoped Matrix.Norms.L2Operator in
private theorem continuousOn_power {K : Set Position} {D : Density} (hc : ContinuousOn D.matrix K) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (D.power a) K := by
  have cu : Continuous (fun x : K => D.matrix x.1) := continuousOn_iff_continuous_domRestrict.mp hc
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun x : K => D.power a x.1)
  have e : (fun x : K => D.power a x.1) = fun x : K => cfc (fun t : ℝ => t^a) (D.matrix x.1) :=
    funext fun x => ((D.positive x.1).1.cfc_eq _).symm
  rw [e]
  exact cu.cfc_of_mem_nhdsSet (fun t : ℝ => t^a) (s := univ) Filter.univ_mem
    (fun x => (D.positive x.1).1.isSelfAdjoint) (Real.continuous_rpow_const ha.le).continuousOn

private theorem BallSobolevReflection.lift_regular {c : Position} {p θ R : ℝ} (H : BallSobolevReflection c R)
    (hp : 3 < p) (hθ : 0 < θ) {D : Density} {S T : MatrixGradient} (reg : SqrtRegular D S)
    (cont : ContinuousOn D.matrix (closedBall c R)) (pow : ∀ a : ℝ, 0 < a → ContinuousOn (D.power a) (closedBall c R))
    (weak : IsMatrixGradientOn (ball c R) (D.power θ) T) (lp : MemLp (matrixGradNorm T) (ENNReal.ofReal p) (volume.restrict (ball c R))) :
    ∃ S' T' : MatrixGradient, DensityRegular (H.lift D) p θ S' T' ∧ Continuous (H.lift D).matrix ∧
      (∀ a : ℝ, 0 < a → Continuous ((H.lift D).power a)) ∧ S' =ᵐ[volume.restrict (closedBall c R)] S ∧
      T' =ᵐ[volume.restrict (closedBall c R)] T := by
  let N := H.lift D
  have cn : Continuous N.matrix := H.cutoff_cont.smul (cont.comp_continuous H.continuous H.range)
  have cp (a : ℝ) (ha : 0 < a) : Continuous (N.power a) := by
    rw [show N.power a = _ from H.lift_power D a]
    exact (H.cutoff_cont.rpow_const (fun _ => Or.inr ha.le)).smul ((pow a ha).comp_continuous H.continuous H.range)
  have rho : Continuous N.charge := by unfold Density.charge; fun_prop
  have compact : HasCompactSupport N.charge := H.compact.of_isClosed_subset (isClosed_tsupport _) <|
    closure_minimal (fun x hx => by
      by_contra h
      have hw : H.cutoff x = 0 := by
        by_contra nz
        exact h (subset_closure (show x ∈ Function.support H.cutoff from nz))
      apply hx
      simp [N,lift,Density.charge,hw]) (isClosed_tsupport _)
  have rs : IsMatrixGradientOn (ball c R) (D.power (1/2)) S := fun i j k =>
    weakPartialOn_restrict MeasurableSet.univ (subset_univ _) (reg.weak i j k)
  obtain ⟨S',sW,sL,es⟩ := H.pullback _ S (1/2) 2 (by norm_num) (by norm_num) (pow _ (by norm_num)) rs
    (by simpa using reg.grad.restrict (ball c R))
  obtain ⟨T',tW,tL,et⟩ := H.pullback _ T θ p hθ (by linarith) (pow _ hθ) weak lp
  rw [← H.lift_power] at sW tW
  exact ⟨S',T',⟨rho.integrable_of_hasCompactSupport compact,rho.memLp_of_hasCompactSupport compact,
    sW,by simpa using sL,tW,tL⟩,cn,cp,es,et⟩

private theorem BallSobolevReflection.on_ball {c : Position} {R : ℝ} (H : BallSobolevReflection c R)
    (D : Density) {x : Position} (hx : x ∈ closedBall c R) : (H.lift D).matrix x = D.matrix x := by
  simp [lift,H.one x hx,H.fixes x hx]

private theorem BallSobolevReflection.oscillation {c : Position} {R θ κ : ℝ} (H : BallSobolevReflection c R)
    (D : Density) (small : SmallPowerOscillation D θ κ R c) : SmallPowerOscillation (H.lift D) θ κ R c := by
  let μ := volume.restrict (ball c R)
  have e : ∀ᵐ x ∂μ, (H.lift D).charge x = D.charge x :=
    (ae_restrict_mem measurableSet_ball).mono fun x hx => congrArg (fun B : SpinMatrix => B.trace.re)
      (H.on_ball D (ball_subset_closedBall hx))
  have w : ∀ᵐ x ∂μ, (H.lift D).power θ x = D.power θ x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have h := ball_subset_closedBall hx
    simp [H.lift_power,H.one x h,H.fixes x h]
  change ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, _
  filter_upwards [small,w] with x pair ex
  filter_upwards [pair,w] with y h ey
  have sup : essSup (H.lift D).charge (volume.restrict (ball c R)) = essSup D.charge (volume.restrict (ball c R)) := essSup_congr_ae e
  simpa only [ex,ey,sup] using h

private theorem BallSobolevReflection.transfer {c : Position} {R p θ ε r d : ℝ}
    (H : BallSobolevReflection c R) (D : Density) (t : SpiralTaper (closedBall c R)) (tr : FrozenTaperRegular t)
    {S T S' T' : MatrixGradient} (eS : S' =ᵐ[volume.restrict (closedBall c R)] S)
    (eT : T' =ᵐ[volume.restrict (closedBall c R)] T) :
    energy (t.field (H.lift D)).matrix = energy (t.field D).matrix ∧
    freeWindowError t tr (H.lift D) S' T' p θ ε r d = freeWindowError t tr D S T p θ ε r d := by
  let B := closedBall c R
  have charge (x : Position) (hx : x ∈ B) : (H.lift D).charge x = D.charge x :=
    congrArg (fun A : SpinMatrix => A.trace.re) (H.on_ball D hx)
  have taper {f g : Position → ℝ} (e : f =ᵐ[volume.restrict B] g) :
      (∫ x, t.shape x*f x) = ∫ x, t.shape x*g x := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp e] with x hx
    by_cases xb : x ∈ B
    · rw [hx xb]
    · simp [t.outside _ xb]
  refine ⟨energy_congr (Filter.Eventually.of_forall fun x => ?_),?_⟩
  · by_cases xb : x ∈ B
    · change cutoffSpiral t.shape ((H.lift D).matrix x) t.wavevector x = _
      rw [H.on_ball D xb]
      rfl
    · simp [SpiralTaper.field,cutoffSpiral,t.outside _ xb]
  · have em : (∫ x, t.shape x*((H.lift D).charge x+((H.lift D).charge x)^2)) =
        ∫ x, t.shape x*(D.charge x+(D.charge x)^2) :=
      taper ((ae_restrict_mem measurableSet_closedBall).mono fun x hx => by simp only [charge x hx])
    have ef : (∫ x in B, (H.lift D).charge x*‖tr.grad x‖^2) = ∫ x in B, D.charge x*‖tr.grad x‖^2 :=
      integral_congr_ae ((ae_restrict_mem measurableSet_closedBall).mono fun x hx => by simp only [charge x hx])
    have ek : (∫ x, t.shape x*kineticDensity S' x) = ∫ x, t.shape x*kineticDensity S x :=
      taper (eS.mono fun x hx => by simp [kineticDensity,matrixGradNorm,hx])
    have eg : (∫ x in B, rootPower T' p x) = ∫ x in B, rootPower T p x :=
      integral_congr_ae (eT.mono fun x hx => by simp [rootPower,matrixGradNorm,hx])
    unfold freeWindowError
    rw [em,ef,ek,eg]

/-- The local form of Proposition 4.16. The density and its positive powers are evaluated
on their continuous representatives on the closed comparison ball. Only the power
θ derivative on the open ball is assumed, and all costs use the original density and gradients. -/
theorem local_free_window_replacement {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {p θ C M : ℝ}
    (F : IslandFockInputs μ) (radii : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → CoulombIslandRadii μ ι ε C)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (sob : SobolevLipschitzComposition)
    (morrey : MatrixSobolevMorrey p M) (hM : 0 ≤ M) (hp : 3 < p) (hθ : 0 < θ) (hleθ : θ < 1) (hpθ : 2 ≤ θ*p)
    (hE : exteriorFormConstant F.oneBody ≤ C) (hI : F.oneBody.interiorConstant ≤ C) :
    ∃ A > 0, ∀ {D : Density} {S T : MatrixGradient} {R : ℝ} {c : Position},
      SqrtRegular D S → ContinuousOn D.matrix (closedBall c R) →
      IsMatrixGradientOn (ball c R) (D.power θ) T → MemLp (matrixGradNorm T) (ENNReal.ofReal p) (volume.restrict (ball c R)) →
      0 < R → BallSobolevReflection c R → SobolevCompositionOn (closedBall c R) → SmallPowerOscillation D θ (θ/64) R c →
      ∃ N : Density, (∀ x ∈ closedBall c R, N.matrix x = D.matrix x) ∧
      ∃ s : SmallBallScale N R c, ∃ m : SmallBallMatrices s, ∀ (t : SpiralTaper (closedBall c R)) (tr : FrozenTaperRegular t),
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      let E := A*freeWindowError t tr D S T p θ ε s.r (s.omega (1/p)/s.r^(1/p))
      energy (t.field D).matrix ≤ energy (cutoffSpiral t.shape m.low t.wavevector)+E ∧
      energy (cutoffSpiral t.shape m.high t.wavevector)-E ≤ energy (t.field D).matrix := by
  obtain ⟨A,hA,global⟩ := free_window_replacement F radii leibniz chain sob morrey hM hp hθ hleθ hpθ hE hI
  refine ⟨A,hA,?_⟩
  intro D S T R c reg cn weak lp hR H comp small
  have cp : ∀ a : ℝ, 0 < a → ContinuousOn (D.power a) (closedBall c R) := fun _ ha => continuousOn_power cn ha
  obtain ⟨S',T',regular,cont,powers,eS,eT⟩ := H.lift_regular hp hθ reg cn cp weak lp
  obtain ⟨s,m,est⟩ := global regular cont powers hR comp (H.oscillation D small)
  refine ⟨H.lift D,fun x hx => H.on_ball D hx,s,m,?_⟩
  intro t tr ε he hhalf
  obtain ⟨energyEq,costEq⟩ := H.transfer D t tr eS eT (p := p) (θ := θ) (ε := ε) (r := s.r)
    (d := s.omega (1/p)/s.r^(1/p))
  simpa only [energyEq,costEq] using est t tr ε he hhalf

end TSGA.ManyBody
