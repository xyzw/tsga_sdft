import TSGA.OrderedScale
import TSGA.SpinRemoval
import TSGA.CoulombSpiral
import TSGA.TetrahedronCoulomb

/-! # Ordered spin matrices in the full-polarization estimate

In a finite tetrahedron a trial for the larger matrix is put in the rotating
frame, localized in spin and rotated back. Only the current and direct terms
can increase. Optimizing the tetrahedron size against Proposition D.1 yields
the cube root of the removed fraction.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Filter SSW TSGA.Localization
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

private abbrev Direction := Metric.sphere (0 : Position) 1
private abbrev directions := (volume : Measure Position).toSphere

/-- The interior tiling comparison already integrates the energy over all
directions at every admissible scale. -/
theorem tile_directions_integrable {η : Mollifier} {E : EnergyFunctional} {K : ℝ}
    (rate : FiniteRateTiling E η K) {A : SpinMatrix} (hA : A.PosSemidef) (q : Position)
    {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) (hscale : δ*K ≤ ℓ) :
    Integrable (fun ω : Metric.sphere (0 : Position) 1 => tileEnergy E η A ℓ δ (‖q‖ • (ω : Position)))
      (volume : Measure Position).toSphere := by
  obtain ⟨_,h⟩ := (rate.interior A hA q ℓ δ he hd hscale).exists
  exact h.choose_spec.1

abbrev CutoffState (f : Position → ℝ) (A : SpinMatrix) :=
  {Γ : MixedState // feasible (fun x => f x • A) Γ}

abbrev RotatingCutoffState (f : Position → ℝ) (A : SpinMatrix) (q : Position) :=
  {Γ : MixedState // feasible (cutoffSpiral f A q) Γ}

/-- The real polarized current of two constant spin tests acting on the same
one-particle orbitals, contracted against the wavevector and divided by volume.
Symmetry comes from self-adjointness of the spin momentum. -/
structure SpinCurrentPairing (A : SpinMatrix) (q : Position) (k : ℝ) where
  form : SpinMatrix →ₗ[ℝ] SpinMatrix →ₗ[ℝ] ℝ
  symm : ∀ X Y, form X Y = form Y X
  cauchy : ∀ X Y, star Y * Y ≤ 1 → (form X Y)^2 ≤
    ‖q‖^2 * hilbertSchmidt (X * CFC.sqrt A)^2 * k

/-- Spin rotation and geometric localization on the one- and two-particle
observables of an individual mixed state. -/
structure OrderedSpiralFrame (f : Position → ℝ) (V : ℝ) (q : Position) where
  current : MixedState → ℝ
  rotate : ∀ A, CutoffState f A ≃ RotatingCutoffState f A q
  coulomb : ∀ A s, (rotate A s).val.interaction = s.val.interaction
  kinetic : ∀ A s, (rotate A s).val.kinetic / V =
    s.val.kinetic / V - current s.val + ‖q‖^2 * A.trace.re/4
  reduced : ∀ A, A.PosSemidef → ∀ s : CutoffState f A,
    ∃ (P : SpinCurrentPairing A q (s.val.kinetic/V)) (T : SpinMatrix)
      (W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      current s.val = P.form 1 1 ∧ T.PosSemidef ∧ W.PosSemidef ∧
      T.trace.re = s.val.kinetic ∧ W.trace.re = s.val.interaction ∧
      ∀ S : SpinMatrix, star S * S ≤ 1 → ∃ t : CutoffState f (S*A*star S),
        t.val.kinetic = ((star S*S)*T).trace.re ∧
        t.val.interaction = (((star S*S) ⊗ₖ (star S*S))*W).trace.re ∧ current t.val = P.form S S

theorem OrderedSpiralFrame.current_sq {f V q} (F : OrderedSpiralFrame f V q) (A : SpinMatrix)
    (hA : A.PosSemidef) (s : CutoffState f A) :
    (F.current s.val)^2 ≤ ‖q‖^2 * A.trace.re * (s.val.kinetic/V) := by
  obtain ⟨P,_,_,hc,_⟩ := F.reduced A hA s
  have h := P.cauchy 1 1 (by simp)
  rw [hc]
  have hs : hilbertSchmidt (CFC.sqrt A)^2 = A.trace.re := by
    rw [hilbertSchmidt, Real.sq_sqrt (by positivity), hs_trace, (CFC.sqrt_nonneg A).star_eq,
      CFC.sqrt_mul_sqrt_self A hA.nonneg]
  simpa only [one_mul,hs] using h

/-- Subtracting the two diagonal currents produces two matrix elements.
Each contains one factor of the discarded spin amplitude. -/
theorem OrderedSpiralFrame.localize {f V q} (F : OrderedSpiralFrame f V q) (A : SpinMatrix)
    (hA : A.PosSemidef) (s : CutoffState f A) (S : SpinMatrix) (hS : star S*S ≤ 1) :
    ∃ (t : CutoffState f (S*A*star S)) (T : SpinMatrix) (W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      T.PosSemidef ∧ W.PosSemidef ∧ T.trace.re = s.val.kinetic ∧ W.trace.re = s.val.interaction ∧
      t.val.kinetic = ((star S*S)*T).trace.re ∧
      t.val.interaction = (((star S*S) ⊗ₖ (star S*S))*W).trace.re ∧
      (F.current s.val - F.current t.val)^2 ≤
        4*‖q‖^2 * hilbertSchmidt ((1-S)*CFC.sqrt A)^2 * (s.val.kinetic/V) := by
  obtain ⟨P,T,W,hs,hT,hW,ht,hw,loc⟩ := F.reduced A hA s
  obtain ⟨t,hk,hi,hc⟩ := loc S hS
  refine ⟨t,T,W,hT,hW,ht,hw,hk,hi,?_⟩
  have hu : F.current s.val-F.current t.val = P.form (1-S) 1 + P.form (1-S) S := by
    simp only [hs,hc,map_sub,LinearMap.sub_apply]
    rw [P.symm S 1]
    ring
  rw [hu]
  nlinarith only [P.cauchy (1-S) 1 (by simp), P.cauchy (1-S) S hS,
    sq_nonneg (P.form (1-S) 1 - P.form (1-S) S)]

/-- Finite-volume data for the ordered estimate. All energy inequalities
here refer to a single tetrahedron or a single physical mixed state. -/
structure SpiralRemovalTrials (η : Mollifier) (J : ℝ) : Prop where
  one_le : 1 ≤ J
  geometry_le : tetrahedronDirectConstant ≤ J
  frame : ∀ ℓ > 0, ∀ δ > 0, δ ≤ ℓ → ∀ q : Position,
    Nonempty (OrderedSpiralFrame (smoothedIndicator (tetrahedron ℓ) η δ) (regionVolume (tetrahedron ℓ)) q)
  represented : ∀ (A : SpinMatrix), A.PosSemidef → ∀ ℓ > 0, ∀ δ > 0, δ ≤ ℓ →
    Nonempty (CutoffState (smoothedIndicator (tetrahedron ℓ) η δ) A)

structure SpiralRemovalInputs (η : Mollifier) (J : ℝ) : Prop extends SpiralRemovalTrials η J where
  liebOxford : ∀ (D : Density) (Γ : MixedState), feasible D.matrix Γ →
    -J * (∫ x, D.charge x^(4/3:ℝ)) ≤ Γ.interaction - hartree D.charge

private theorem liebOxford_mono {c d : ℝ} (h : c ≤ d) (D : Density) :
    -d * (∫ x, D.charge x^(4/3:ℝ)) ≤ -c * (∫ x, D.charge x^(4/3:ℝ)) :=
  mul_le_mul_of_nonneg_right (neg_le_neg h) (integral_nonneg fun x =>
    Real.rpow_nonneg ((RCLike.nonneg_iff.mp (D.positive x).trace_nonneg).1) _)

theorem SpiralRemovalTrials.enlarge {η : Mollifier} {J L : ℝ} (h : SpiralRemovalTrials η J)
    (hJL : J ≤ L) : SpiralRemovalTrials η L :=
  ⟨h.one_le.trans hJL, h.geometry_le.trans hJL, h.frame, h.represented⟩

/-- Supply the same statewise Lieb–Oxford estimate used for coordinate scaling. -/
theorem SpiralRemovalTrials.withLiebOxford {η : Mollifier} {J c : ℝ} (h : SpiralRemovalTrials η J)
    (lo : ∀ (D : Density) (Γ : MixedState), feasible D.matrix Γ →
      -c * (∫ x, D.charge x^(4/3:ℝ)) ≤ Γ.interaction - hartree D.charge) :
    SpiralRemovalInputs η (max J c) :=
  ⟨h.enlarge (le_max_left ..), fun D Γ hg => (liebOxford_mono (le_max_right ..) D).trans (lo D Γ hg)⟩

theorem SpiralRemovalInputs.enlarge {η : Mollifier} {J L : ℝ} (h : SpiralRemovalInputs η J)
    (hJL : J ≤ L) : SpiralRemovalInputs η L :=
  ⟨h.toSpiralRemovalTrials.enlarge hJL, fun D Γ hg => (liebOxford_mono hJL D).trans (h.liebOxford D Γ hg)⟩

private theorem bounded_spin_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {X T : Matrix ι ι ℂ}
    (hx : X ≤ 1) (ht : T.PosSemidef) : (X*T).trace.re ≤ T.trace.re := by
  have hw := trace_product_nonneg (Matrix.le_iff.mp hx) ht
  simpa [sub_mul, Matrix.trace_sub] using hw

private theorem hartree_cutoffSpiral (f : Position → ℝ) (A : SpinMatrix) (q : Position) :
    hartree (fun x => (cutoffSpiral f A q x).trace.re) = A.trace.re^2 * hartree f := by
  rw [← hartree_const_mul]
  congr 1
  funext x
  simp [cutoffSpiral, Matrix.trace_smul, mul_comm]

private theorem tile_indirect {η : Mollifier} {J : ℝ} (H : SpiralRemovalInputs η J)
    {A : SpinMatrix} (hA : A.PosSemidef) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) (q : Position)
    (s : RotatingCutoffState (smoothedIndicator (tetrahedron ℓ) η δ) A q) :
    -J * A.trace.re^(4/3:ℝ) ≤
      (s.val.interaction - A.trace.re^2 * hartree (smoothedIndicator (tetrahedron ℓ) η δ)) /
        regionVolume (tetrahedron ℓ) := by
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  let D : Density := ⟨cutoffSpiral f A q, fun x =>
    (rotate_posSemidef _ hA).smul (RCLike.nonneg_iff.mpr
      ⟨(smoothedIndicator_bounds _ _ hd x).1, by simp⟩ : (0:ℂ) ≤ (f x:ℂ))⟩
  have hlo := H.liebOxford D s.val s.property
  change _ ≤ s.val.interaction - hartree (fun x => (cutoffSpiral f A q x).trace.re) at hlo
  rw [hartree_cutoffSpiral] at hlo
  apply (le_div_iff₀ (tetrahedron_volume_pos he)).2
  have hm := mul_le_mul_of_nonneg_left (tile_charge_moment η he hd hA q) (zero_le_one.trans H.one_le)
  change J*(∫ x, D.charge x^(4/3:ℝ)) ≤ _ at hm
  linarith only [hm,hlo]

/-- Completing the square in the current estimate controls the kinetic
energy of a state after undoing its spiral rotation. -/
private theorem untwisted_kinetic {k t j v : ℝ} (hk : 0 ≤ k) (hv : 0 ≤ v)
    (ht : t = k - j + v/4) (hc : j^2 ≤ v*k) : k ≤ 2*t + v/2 := by
  have h : 2*j ≤ k+v := by
    by_contra! h
    nlinarith only [hc, sq_nonneg (k-v), mul_pos (sub_pos.mpr h) (show 0 < 2*j + (k+v) by linarith)]
  linarith

private def trial (V : ℝ) (f : Position → ℝ) (A : SpinMatrix) (Γ : MixedState) : ℝ :=
  (Γ.kinetic + Γ.interaction - A.trace.re^2*hartree f)/V

private theorem trial_glb (V : ℝ) (hV : 0 < V) (f : Position → ℝ) (A : SpinMatrix) (q : Position)
    (h : Nonempty (RotatingCutoffState f A q)) :
    IsGLB (Set.range fun s : RotatingCutoffState f A q => trial V f A s.val)
      (energy (cutoffSpiral f A q)/V) := by
  obtain ⟨s⟩ := h
  have hg := energy_isGLB ⟨s.val,s.property⟩
  rw [hartree_cutoffSpiral] at hg
  constructor
  · rintro _ ⟨t,rfl⟩
    exact div_le_div_of_nonneg_right (hg.1 (Set.mem_range_self t)) hV.le
  · intro x hx
    apply (le_div_iff₀ hV).2
    apply hg.2
    rintro _ ⟨t,rfl⟩
    exact (le_div_iff₀ hV).1 (hx (Set.mem_range_self t))

private theorem near_trial {V : ℝ} (hV : 0 < V) (f : Position → ℝ) (A : SpinMatrix) (q : Position)
    (rep : Nonempty (RotatingCutoffState f A q)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : RotatingCutoffState f A q, trial V f A s.val < energy (cutoffSpiral f A q)/V + ε := by
  by_contra! h
  have hx : energy (cutoffSpiral f A q)/V + ε ≤ energy (cutoffSpiral f A q)/V :=
    (trial_glb V hV f A q rep).2 (by rintro _ ⟨s,rfl⟩; exact h s)
  linarith

private theorem holderGrowth_parts {r : ℝ} (hr : 0 < r) (q : Position) :
    0 < holderGrowth r q ∧ r^(4/3 : ℝ) ≤ holderGrowth r q ∧ r*‖q‖^2 ≤ holderGrowth r q := by
  have h1 := Real.rpow_pos_of_pos hr (4/3:ℝ)
  have h2 := Real.rpow_pos_of_pos hr (5/3:ℝ)
  have h3 := mul_nonneg hr.le (sq_nonneg ‖q‖)
  unfold holderGrowth
  exact ⟨by linarith,by linarith,by linarith⟩

/-- A zero-wavevector trial controls the unaveraged finite energy at every
wavevector. Cauchy–Schwarz bounds its current after rotation. -/
theorem tile_upper_from_zero {η : Mollifier} {K J : ℝ} (rate : FiniteRateTiling energy η K)
    (H : SpiralRemovalInputs η J) (B : SpinMatrix) (hB : B.PosSemidef) (hr : 0 < B.trace.re)
    (ℓ : ℝ) (he : 0 < ℓ) (δ : ℝ) (hd : 0 < δ) (hs : δ ≤ ℓ) (q : Position) :
    tileEnergy energy η B ℓ δ q ≤ 4*(K+J+1) * (holderGrowth B.trace.re q + B.trace.re/(ℓ*δ)) := by
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  let V := regionVolume (tetrahedron ℓ)
  let r := B.trace.re
  let G := holderGrowth r q + r/(ℓ*δ)
  have hV : 0 < V := tetrahedron_volume_pos he
  have hp := holderGrowth_parts hr q
  have hRG : holderGrowth r q ≤ G := le_add_of_nonneg_right (div_nonneg hr.le (mul_pos he hd).le)
  have hG : 0 < G := hp.1.trans_le hRG
  have hv : r*‖q‖^2 ≤ G := hp.2.2.trans hRG
  have hJ := zero_le_one.trans H.one_le
  have hK := zero_le_one.trans rate.one_le
  have h0 : tileEnergy energy η B ℓ δ 0 ≤ K*G := by
    have h := (rate.rough B hB 0 ℓ δ he hd).2
    simp only [averagedTile, norm_zero, directionAverage_zero] at h
    have hg : r*rateGrowth r 0 ≤ holderGrowth r q := by
      rw [← holderGrowth_eq hr]
      simp only [holderGrowth, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
      exact le_add_of_nonneg_right (mul_nonneg hr.le (sq_nonneg _))
    have hw := mul_le_mul_of_nonneg_left (add_le_add_left hg (r/(ℓ*δ))) hK
    have hf := mul_nonneg hK (mul_nonneg hr.le (Real.rpow_nonneg hr.le (1/3:ℝ)))
    change tileEnergy energy η B ℓ δ 0 + K*(r*r^(1/3:ℝ)) ≤ K*(r*rateGrowth r 0+r/(ℓ*δ)) at h
    dsimp only [G]
    linarith only [h,hw,hf]
  obtain ⟨F₀⟩ := H.frame ℓ he δ hd hs 0
  obtain ⟨F⟩ := H.frame ℓ he δ hd hs q
  have rep := H.represented B hB ℓ he δ hd hs
  obtain ⟨g,hg⟩ := near_trial hV f B 0 (rep.map (F₀.rotate B)) hG
  have field : cutoffSpiral f B 0 = fun x => f x • B := by
    ext x i j
    simp [cutoffSpiral, Matrix.smul_apply, Complex.real_smul]
  let s : CutoffState f B := ⟨g.val, by rw [←field]; exact g.property⟩
  let v := F.rotate B s
  have hlo := tile_indirect H hB he hd 0 g
  have hgt : trial V f B g.val = g.val.kinetic/V + (g.val.interaction-r^2*hartree f)/V := by
    dsimp only [trial,r]
    ring
  change trial V f B g.val < tileEnergy energy η B ℓ δ 0 + G at hg
  change -J*r^(4/3:ℝ) ≤ (g.val.interaction-r^2*hartree f)/V at hlo
  have hm := mul_le_mul_of_nonneg_left (hp.2.1.trans hRG) hJ
  have hk : s.val.kinetic/V ≤ (K+J+1)*G := by
    change g.val.kinetic/V ≤ _
    change J*r^(4/3:ℝ) ≤ J*G at hm
    linarith only [hgt,hg.le,h0,hlo,hm]
  have hcurr : |F.current s.val| ≤ (s.val.kinetic/V+‖q‖^2*r)/2 := by
    have hn := div_nonneg s.val.kinetic_nonneg hV.le
    apply (sq_le_sq₀ (abs_nonneg _) (div_nonneg (add_nonneg hn (mul_nonneg (sq_nonneg _) hr.le)) (by norm_num))).mp
    rw [sq_abs]
    apply (F.current_sq B hB s).trans
    change ‖q‖^2*r*(s.val.kinetic/V) ≤ _
    nlinarith only [sq_nonneg (s.val.kinetic/V-‖q‖^2*r)]
  have hrot := F.kinetic B s
  have hdif : trial V f B v.val - trial V f B g.val = -F.current s.val + ‖q‖^2*r/4 := by
    have hW : v.val.interaction = g.val.interaction := F.coulomb B s
    change v.val.kinetic/V = g.val.kinetic/V-F.current s.val+‖q‖^2*r/4 at hrot
    unfold trial
    rw [hW]
    linear_combination hrot
  have hGLB := (trial_glb V hV f B q ⟨v⟩).1 (Set.mem_range_self v)
  change tileEnergy energy η B ℓ δ q ≤ trial V f B v.val at hGLB
  change tileEnergy energy η B ℓ δ q ≤ 4*(K+J+1)*G
  linarith only [hGLB,hdif,hg.le,h0,hk,hcurr,neg_le_abs (F.current s.val),hv,hG.le,
    mul_nonneg hK hG.le,mul_nonneg hJ hG.le]

/-- Comparison for a general constant spin contraction, keeping the full
direct-energy difference. The parameter d measures its effect on the spin
amplitudes in the original state. -/
theorem contraction_tile_comparison {η : Mollifier} {J : ℝ} (H : SpiralRemovalInputs η J)
    {A B : SpinMatrix} (hB : B.PosSemidef) (hr : 0 < B.trace.re)
    (S : SpinMatrix) (hS : star S*S ≤ 1) (hSA : S*B*star S = A) (har : A.trace.re ≤ B.trace.re)
    {d : ℝ} (hd₀ : 0 ≤ d) (hloss : hilbertSchmidt ((1-S)*CFC.sqrt B)^2 ≤ B.trace.re*d^2)
    (q : Position) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) (hs : δ ≤ ℓ)
    (hcut : B.trace.re/(ℓ*δ) ≤ 4*holderGrowth B.trace.re q)
    (hupper : tileEnergy energy η B ℓ δ q ≤ J*(holderGrowth B.trace.re q + B.trace.re/(ℓ*δ))) :
    tileEnergy energy η A ℓ δ q ≤ tileEnergy energy η B ℓ δ q + 8*J*holderGrowth B.trace.re q*d +
      (B.trace.re^2 - A.trace.re^2) *
        (hartree (smoothedIndicator (tetrahedron ℓ) η δ)/regionVolume (tetrahedron ℓ)) := by
  let r := B.trace.re
  let a := A.trace.re
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  let V := regionVolume (tetrahedron ℓ)
  let H₀ := holderGrowth r q
  have hV := tetrahedron_volume_pos he
  have hJ := H.one_le
  have hJ₀ := zero_le_one.trans hJ
  obtain ⟨hH,h4,hq⟩ := holderGrowth_parts hr q
  change 0 < H₀ at hH
  change _ ≤ H₀ at h4 hq
  obtain ⟨F⟩ := H.frame ℓ he δ hd hs q
  have rep := (H.represented B hB ℓ he δ hd hs).map (F.rotate B)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g,hg⟩ := near_trial hV f B q rep (lt_min hε hH)
  let s := (F.rotate B).symm g
  have heq : F.rotate B s = g := (F.rotate B).apply_symm_apply _
  obtain ⟨u,T,W,hT,hW,ht,hw,hut,huw,hj⟩ := F.localize B hB s S hS
  let v := F.rotate (S*B*star S) u
  have hA' : (S*B*star S).trace.re = a := congrArg (fun X : SpinMatrix => X.trace.re) hSA
  have huK : u.val.kinetic ≤ s.val.kinetic := by
    rw [hut,← ht]
    exact bounded_spin_trace hS hT
  have huW : u.val.interaction ≤ s.val.interaction := by
    rw [huw,← hw]
    exact bounded_spin_trace (contraction_pair_le_one (Matrix.posSemidef_conjTranspose_mul_self S) hS) hW
  have horig := F.kinetic B s
  rw [heq] at horig
  have hk := untwisted_kinetic (div_nonneg s.val.kinetic_nonneg hV.le)
    (mul_nonneg (sq_nonneg ‖q‖) hr.le) horig (F.current_sq B hB s)
  have hvK := F.kinetic (S*B*star S) u
  change v.val.kinetic / V = _ at hvK
  rw [hA'] at hvK
  have hWW : v.val.interaction ≤ g.val.interaction := by
    change (F.rotate _ u).val.interaction ≤ _
    rw [F.coulomb,←heq,F.coulomb]
    exact huW
  let e := tileEnergy energy η B ℓ δ q
  change trial V f B g.val < e + min ε H₀ at hg
  have hLO := tile_indirect H hB he hd q g
  have hem := hupper
  change e ≤ J*(H₀ + r/(ℓ*δ)) at hem
  have hkin : s.val.kinetic/V ≤ 16*J*H₀ := by
    change -J*r^(4/3:ℝ) ≤ (g.val.interaction - r^2*hartree f)/V at hLO
    have htrial : trial V f B g.val = g.val.kinetic/V + (g.val.interaction - r^2*hartree f)/V := by
      unfold trial
      dsimp only [r]
      ring
    rw [htrial] at hg
    change s.val.kinetic/V ≤ 2*(g.val.kinetic/V) + ‖q‖^2*r/2 at hk
    have hm := min_le_right ε H₀
    have hc := mul_le_mul_of_nonneg_left hcut hJ₀
    have hf := mul_le_mul_of_nonneg_left h4 hJ₀
    have hJH := le_mul_of_one_le_left hH.le hJ
    change J*(r/(ℓ*δ)) ≤ J*(4*H₀) at hc
    change J*r^(4/3:ℝ) ≤ J*H₀ at hf
    change r*‖q‖^2 ≤ H₀ at hq
    linarith only [hg.le,hLO,hem,hm,hc,hf,hk,hq,hJH,mul_nonneg hJ₀ hH.le]
  have hj' : F.current s.val-F.current u.val ≤ 8*J*H₀*d := by
    have hsq : (F.current s.val-F.current u.val)^2 ≤ (8*J*H₀*d)^2 := by
      apply hj.trans
      calc
        _ ≤ 4*‖q‖^2*(r*d^2)*(16*J*H₀) := mul_le_mul
          (mul_le_mul_of_nonneg_left hloss (by positivity)) hkin
          (div_nonneg s.val.kinetic_nonneg hV.le) (by positivity)
        _ = (64*J*H₀*d^2)*(r*‖q‖^2) := by ring
        _ ≤ (64*J*H₀*d^2)*H₀ := mul_le_mul_of_nonneg_left hq (by positivity)
        _ ≤ ((64*J*H₀*d^2)*H₀)*J := le_mul_of_one_le_right (by positivity) hJ
        _ = _ := by ring
    have hpos : 0 ≤ 8*J*H₀*d := by positivity
    exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) hpos).mp (by simpa [sq_abs] using hsq))
  have hvtrial : tileEnergy energy η A ℓ δ q ≤ trial V f (S*B*star S) v.val := by
    change energy (cutoffSpiral f A q)/V ≤ _
    rw [← hSA]
    exact (trial_glb V hV _ _ q ⟨v⟩).1 (Set.mem_range_self v)
  have diff : trial V f (S*B*star S) v.val - trial V f B g.val =
      (v.val.kinetic/V - g.val.kinetic/V) + (v.val.interaction-g.val.interaction)/V +
        (r^2-a^2)*(hartree f/V) := by
    unfold trial
    rw [hA']
    dsimp only [r]
    ring
  have htk := div_le_div_of_nonneg_right huK hV.le
  have hww := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hWW) hV.le
  have hco := mul_le_mul_of_nonneg_left har (sq_nonneg ‖q‖)
  change g.val.kinetic/V = s.val.kinetic/V - F.current s.val + ‖q‖^2*r/4 at horig
  change tileEnergy energy η A ℓ δ q ≤ e + 8*J*H₀*d + (r^2-a^2)*(hartree f/V) + ε
  linarith only [hvtrial,diff,hg.le,min_le_left ε H₀,hvK,horig,htk,hww,hco,hj']

/-- Finite-volume comparison before averaging. The  ℓ² loss in the
direct energy and the square-root loss in the current have different origins. -/
theorem ordered_tile_comparison {η : Mollifier} {J : ℝ} (H : SpiralRemovalInputs η J)
    {A B : SpinMatrix} (hA : A.PosSemidef) (hAB : (B-A).PosSemidef) (hr : 0 < B.trace.re)
    (q : Position) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) (hs : δ ≤ ℓ)
    (hcut : B.trace.re/(ℓ*δ) ≤ 4*holderGrowth B.trace.re q)
    (hupper : tileEnergy energy η B ℓ δ q ≤ J*(holderGrowth B.trace.re q + B.trace.re/(ℓ*δ))) :
    let r := B.trace.re
    let h := (r - A.trace.re)/r
    tileEnergy energy η A ℓ δ q ≤ tileEnergy energy η B ℓ δ q +
      8*J*holderGrowth r q * Real.sqrt h + 2*J*r^2*h*ℓ^2 := by
  let r := B.trace.re
  let a := A.trace.re
  let h := (r-a)/r
  have ha : 0 ≤ a := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have har : a ≤ r := by simpa [r,a,Matrix.trace_sub] using (RCLike.nonneg_iff.mp hAB.trace_nonneg).1
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr har) hr.le
  have hrh : r*h = r-a := by dsimp only [h]; field_simp [show r ≠ 0 from hr.ne']
  have hB : B.PosSemidef := by simpa using hAB.add hA
  obtain ⟨S,hS,hSA,hloss⟩ := exists_spinContraction_charge_deficit hA (Matrix.le_iff.mpr hAB)
  have hc := contraction_tile_comparison H hB hr S hS hSA har (Real.sqrt_nonneg h)
    (by rw [Real.sq_sqrt hh]; exact hloss.trans_eq hrh.symm) q he hd hs hcut hupper
  change tileEnergy energy η A ℓ δ q ≤ tileEnergy energy η B ℓ δ q + 8*J*holderGrowth r q*√h + 2*J*r^2*h*ℓ^2
  apply hc.trans (add_le_add (le_refl _) _)
  have hf := (tile_hartree_bound η he hd).trans (mul_le_mul_of_nonneg_right H.geometry_le (sq_nonneg ℓ))
  have hJ₀ := zero_le_one.trans H.one_le
  have hab := sq_le_sq₀ ha hr.le |>.mpr har
  have hab' : r^2-a^2 ≤ 2*r*(r-a) := by nlinarith [sq_nonneg (r-a)]
  calc
    _ ≤ (r^2-a^2)*(J*ℓ^2) := mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr hab)
    _ ≤ 2*r*(r-a)*(J*ℓ^2) := mul_le_mul_of_nonneg_right hab' (by positivity)
    _ = _ := by rw [← hrh]; ring

theorem direction_mono_add {f g : Position → ℝ} {r d : ℝ}
    (hf : Integrable (fun ω : Direction => f (r • (ω : Position))) directions)
    (hg : Integrable (fun ω : Direction => g (r • (ω : Position))) directions)
    (hle : ∀ ω : Direction, f (r • (ω : Position)) ≤ g (r • (ω : Position)) + d) :
    directionAverage f r ≤ directionAverage g r + d := by
  let : NeZero directions := ⟨Measure.toSphere_ne_zero volume⟩
  have hd : Integrable (fun _ : Direction => d) directions := integrable_const d
  change (⨍ ω : Direction, f (r • (ω : Position)) ∂directions) ≤
    (⨍ ω : Direction, g (r • (ω : Position)) ∂directions) + d
  have h := mul_le_mul_of_nonneg_left (integral_mono hf (hg.add hd) hle)
    (inv_nonneg.mpr (show 0 ≤ directions.real Set.univ from ENNReal.toReal_nonneg))
  simpa only [← smul_eq_mul, ← average_eq, Pi.add_apply, average_fun_add hg hd, average_const] using h

/-- The one-sided full-polarization estimate in Proposition E.2(v).
Its coefficient is independent of the two matrices and of the wavevector. -/
private theorem ordered_ssw_holder_at {η : Mollifier} {K J : ℝ} (rate : FiniteRateTiling energy η K)
    (input : SpiralRemovalInputs η J)
    (upper : ∀ (B : SpinMatrix), B.PosSemidef → 0 < B.trace.re → ∀ ℓ > 0, ∀ δ > 0, δ ≤ ℓ → ∀ q : Position,
      tileEnergy energy η B ℓ δ q ≤ J*(holderGrowth B.trace.re q + B.trace.re/(ℓ*δ))) :
    ∃ C > 0, ∀ (A B : SpinMatrix), A.PosSemidef → (B-A).PosSemidef → 0 < B.trace.re →
      ∀ q : Position, sswEnergy energy η A q - sswEnergy energy η B q ≤
        C * holderGrowth B.trace.re q * ((B.trace.re-A.trace.re)/B.trace.re)^(1/3:ℝ) := by
  let C := 4*K + 16*(K^2+K) + 8*J + 8*J*K^2
  have hK := rate.one_le
  have hJ := input.one_le
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hJ₀ : 0 ≤ J := zero_le_one.trans hJ
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro A B hA hAB hr q
  have hB : B.PosSemidef := by simpa using hAB.add hA
  let r := B.trace.re
  let a := A.trace.re
  let h := (r-a)/r
  let G := holderGrowth r q
  have hG : 0 ≤ G := (holderGrowth_parts hr q).1.le
  have ha : 0 ≤ a := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have hdiff := RCLike.nonneg_iff.mp hAB.trace_nonneg
  have har : a ≤ r := by simpa [a,r,Matrix.trace_sub] using hdiff.1
  rcases har.eq_or_lt with heq | hlt
  · have ht : (B-A).trace.re = 0 := by
      rw [Matrix.trace_sub,Complex.sub_re]
      exact sub_eq_zero.mpr heq.symm
    have hz := hAB.trace_eq_zero_iff.mp (Complex.ext ht hdiff.2)
    rw [sub_eq_zero.mp hz]
    simp
  have hh : 0 < h := div_pos (sub_pos.mpr hlt) hr
  have hh1 : h ≤ 1 := (div_le_one hr).2 (sub_le_self _ ha)
  let z := h^(1/3:ℝ)
  have hz := Real.rpow_pos_of_pos hh (1/3:ℝ)
  have hsqrt : Real.sqrt h ≤ z := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by norm_num)
  obtain ⟨ℓ,δ,he,hd,hscale,hu,hsc⟩ := ordered_scales hr hh hh1 hK q
  have hlower := rate.lower_rate hA q he hd hscale
  have hl := lowerRateError_le_upper ha hlt.le he hd q
  have hsmall := mul_le_mul_of_nonneg_left (hl.trans hu) hK₀
  have hbig : scaleAverage (fun t => averagedTile energy η A q (t*ℓ) (t*δ)) ≤
      sswEnergy energy η B q + (16*(K^2+K) + 8*J + 8*J*K^2)*G*z := by
    apply TSGA.Localization.scaleAverage_le_const (rate.dilation_integrable A hA q ℓ δ he hd hscale)
    intro t ht
    have htpos : 0 < t := by linarith [show (1/2:ℝ) ≤ t from ht.1]
    have hte := mul_pos htpos he
    have htd := mul_pos htpos hd
    have htk : (t*δ)*K ≤ t*ℓ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hscale htpos.le
    have htdl := (le_mul_of_one_le_right htd.le hK).trans htk
    obtain ⟨hc,hdir,hrate⟩ := hsc t ht
    let Eₐ := averagedTile energy η A q (t*ℓ) (t*δ)
    let Eᵦ := averagedTile energy η B q (t*ℓ) (t*δ)
    have hcmp : Eₐ ≤ Eᵦ + (8*J*G*√h + 2*J*r^2*h*(t*ℓ)^2) := by
      apply direction_mono_add (tile_directions_integrable rate hA q hte htd htk)
        (tile_directions_integrable rate hB q hte htd htk)
      intro ω
      have hnorm : ‖‖q‖ • (ω : Position)‖ = ‖q‖ := by
        have hω : ‖(ω : Position)‖ = 1 := by simp
        simp [norm_smul, hω]
      have hscaleG : holderGrowth r (‖q‖ • (ω : Position)) = G := by simp [G,holderGrowth,hnorm]
      have hcutω : r/((t*ℓ)*(t*δ)) ≤ 4*holderGrowth r (‖q‖ • (ω : Position)) := by
        rw [hscaleG]
        exact hc
      have H := ordered_tile_comparison input hA hAB hr (‖q‖ • (ω : Position)) hte htd htdl hcutω
        (upper B hB hr _ hte _ htd htdl _)
      change _ ≤ _ + 8*J*holderGrowth r (‖q‖ • (ω : Position))*√h + 2*J*r^2*h*(t*ℓ)^2 at H
      rwa [hscaleG,add_assoc] at H
    have hupper := rate.upper_rate hB q hte htd htk
    have hkin := mul_le_mul_of_nonneg_left hrate (add_nonneg (sq_nonneg K) hK₀)
    have hcurrent := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 8*J*G by positivity)
    have hD := mul_le_mul_of_nonneg_left hdir (show 0 ≤ 2*J by positivity)
    change Eᵦ ≤ _ at hupper
    change _ ≤ (K^2+K)*(16*G*z) at hkin
    change _ ≤ 2*J*(4*K^2*G*z) at hD
    change Eₐ ≤ _
    linarith only [hupper,hcmp,hkin,hcurrent,hD]
  change _ - _ ≤ C*G*z
  change _ ≤ K*(4*G*z) at hsmall
  dsimp only [C]
  linarith only [hlower,hsmall,hbig]

/-- Ordered comparison for the physical gas. The only finite energy upper
estimate used here is the zero-wavevector instance of the finite tiling bound. -/
theorem ordered_ssw_holder {η : Mollifier} {K J : ℝ} (rate : FiniteRateTiling energy η K)
    (input : SpiralRemovalInputs η J) :
    ∃ C > 0, ∀ (A B : SpinMatrix), A.PosSemidef → (B-A).PosSemidef → 0 < B.trace.re →
      ∀ q : Position, sswEnergy energy η A q - sswEnergy energy η B q ≤
        C * holderGrowth B.trace.re q * ((B.trace.re-A.trace.re)/B.trace.re)^(1/3:ℝ) := by
  have hJ : J ≤ 4*(K+J+1) := by linarith [rate.one_le,input.one_le]
  apply ordered_ssw_holder_at rate (J := 4*(K+J+1))
    (input.enlarge hJ)
  exact tile_upper_from_zero rate input

end TSGA.ManyBody
