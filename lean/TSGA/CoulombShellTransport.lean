import TSGA.CoulombLatticeShell
import TSGA.TetrahedronShellTransport
import TSGA.SkeletonFourier
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Negative Sobolev norm of the physical periodic charge

The analytic inputs are the polar-coordinate formula in a star body, duality
of periodic convolution, and the bounded-density transport inequality on the
flat torus (Peyré, ESAIM COCV 24 (2018), Theorem 2.5).
None of the three specifies a shell cost or a Coulomb energy.
-/

noncomputable section
namespace TSGA.SSW
open MeasureTheory Set Metric Skeleton
open scoped InnerProductSpace BoundedContinuousFunction

def unitPeriodic (f : Position → ℝ) : Prop :=
  ∀ (m : Fin 3 → ℤ) x, f (latticeShift 1 m+x) = f x

/-- Normalized cone measure on the boundary, together with an independent
uniform volume coordinate. The formula is the ordinary radial Jacobian r²dr
with the substitution v=(r³-a³)/(1-a³). -/
structure HomotheticCoordinates (body : ℝ → Set Position) (V R : ℝ) where
  law : Measure (ℝ × Position)
  probability : IsProbabilityMeasure law
  support : ∀ᵐ z ∂law, z.1 ∈ Icc (0:ℝ) 1 ∧ ‖z.2‖ ≤ R
  integrate : ∀ {s : ℝ}, 0 < s → s < 1 → ∀ f : Position →ᵇ ℝ,
    (∫ x in (body 1 \ body (1-s)), f x) =
      V*shellFraction s * ∫ z, f (shellQuantile s z.1 • z.2) ∂law

/-- The duality formula for convolution on a fundamental cube, tested
against bounded continuous periodic functions. The probability law is the
unscaled kernel. This formula applies to every measurable periodic set. -/
structure PeriodicKernelCalculus (η : Mollifier) where
  law : Measure Position
  probability : IsProbabilityMeasure law
  support : ∀ᵐ y ∂law, y ∈ tsupport η.kernel
  probe : ℝ → (Position →ᵇ ℝ) → (Position →ᵇ ℝ)
  probe_eq : ∀ d φ x, probe d φ x = ∫ y, φ (x+d • y) ∂law
  convolution : ∀ (S : Set Position), MeasurableSet S →
    (∀ m x, latticeShift 1 m + x ∈ S ↔ x ∈ S) → ∀ {d}, 0 < d →
    AEStronglyMeasurable (smoothedIndicator S η d) volume ∧
    ∀ φ : Position →ᵇ ℝ, unitPeriodic φ →
    (∫ x in latticeCube 1 0, smoothedIndicator S η d x * φ x) =
      ∫ x in latticeCube 1 0 ∩ S, probe d φ x

attribute [instance] HomotheticCoordinates.probability PeriodicKernelCalculus.probability

abbrev TetrahedronCone := HomotheticCoordinates tetrahedron (regionVolume (tetrahedron 1)) 2
abbrev ShellSampleSpace := (ℝ × Position) × Position

def tileSample (o : CubeOrientation) (s : ℝ) (z : ShellSampleSpace) : Position :=
  shellSample o s z.1.1 z.1.2 z.2

theorem continuous_tileSample (o : CubeOrientation) (s : ℝ) : Continuous (tileSample o s) := by
  unfold tileSample shellSample
  have hq : Continuous (fun z : ShellSampleSpace => shellQuantile s z.1.1) := by
    unfold shellQuantile
    fun_prop (disch := norm_num)
  exact ((latticeChartEquiv 1 (0,o)).symm.continuous.comp (hq.smul (by fun_prop))).add (by fun_prop)

/-- Both thicknesses are sampled with the same probability space. This is
the marginal identity for the explicitly constructed transport plan. -/
theorem periodic_shell_marginal (C : TetrahedronCone) {η : Mollifier} (K : PeriodicKernelCalculus η)
    {s : ℝ} (hs : 0 < s) (hu : s < 1) (φ : Position →ᵇ ℝ) (hp : unitPeriodic φ) :
    (∫ x in latticeCube 1 0, smoothedIndicator (latticeShell 1 s) η s x * φ x) =
      regionVolume (tetrahedron 1)*shellFraction s *
        ∑ o : CubeOrientation, ∫ z, φ (tileSample o s z) ∂(C.law.prod K.law) := by
  let D := tetrahedron 1 \ tetrahedron (1-s)
  let S (o : CubeOrientation) := latticeChart 1 (0,o) ⁻¹' D
  have hD : MeasurableSet D := (tetrahedron_open _).measurableSet.diff (tetrahedron_open _).measurableSet
  have hm (o) : MeasurableSet (S o) := hD.preimage (latticeChart_isometry 1 (0,o)).continuous.measurable
  have hfin := (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos (by norm_num : (0:ℝ)<1))).2.ne
  have fin (o) : volume (S o) ≠ ⊤ := by
    rw [(latticeChart_preserving 1 (0,o)).measure_preimage hD.nullMeasurableSet]
    exact measure_ne_top_of_subset sdiff_subset hfin
  have integ (o) : IntegrableOn (K.probe s φ) (S o) := by
    have : IsFiniteMeasure (volume.restrict (S o)) := isFiniteMeasure_restrict.mpr (fin o)
    exact (integrable_const ‖K.probe s φ‖).mono' (K.probe s φ).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => (K.probe s φ).norm_coe_le_norm x)
  have eqn (o) : (∫ x in S o, K.probe s φ x) = regionVolume (tetrahedron 1)*shellFraction s *
      ∫ z, φ (tileSample o s z) ∂(C.law.prod K.law) := by
    let e := latticeChartEquiv 1 (0,o)
    let f := (K.probe s φ).compContinuous ⟨e.symm,e.symm.continuous⟩
    have h1 := (latticeChart_preserving 1 (0,o)).setIntegral_preimage_emb
      e.toHomeomorph.measurableEmbedding (fun y => f y) D
    have hpre : (∫ x in S o, K.probe s φ x) = ∫ x in D, f x := by
      convert h1 using 1
      apply setIntegral_congr_fun (hm o)
      intro x _
      change _ = K.probe s φ (e.symm (e x))
      rw [e.symm_apply_apply]
    rw [hpre,C.integrate hs hu f]
    congr 1
    have hprod : Integrable (fun z : ShellSampleSpace => φ (tileSample o s z)) (C.law.prod K.law) :=
      (integrable_const ‖φ‖).mono' (φ.continuous.comp (continuous_tileSample o s)).aestronglyMeasurable
        (ae_of_all _ fun z => φ.norm_coe_le_norm _)
    rw [integral_prod _ hprod]
    exact integral_congr_ae (ae_of_all _ fun z => K.probe_eq s φ _)
  have hconv := (K.convolution (latticeShell 1 s) (latticeShell_measurable 1 s) (fun m x => latticeShell_mem_shift m x) hs).2 φ hp
  rw [hconv,setIntegral_congr_set (latticeShell_cube_ae (by norm_num : (0:ℝ)<1) hs.le)]
  change (∫ x in ⋃ o, S o, K.probe s φ x) = _
  rw [integral_iUnion_fintype hm (fun i j h =>
    (latticeChart_disjoint (by norm_num : (0:ℝ)<1) (show ((0,i) : LatticeTile) ≠ (0,j) from
      fun e => h (congrArg Prod.snd e))).mono (fun _ hx => hx.1) (fun _ hx => hx.1)) integ]
  simp_rw [eqn]
  rw [Finset.mul_sum]

/-- Squared homogeneous H⁻¹ norm in the ordinary Fourier normalization
on the unit three-torus. Division at frequency zero contributes zero. -/
def periodicNegativeNorm (f : Position → ℝ) : ℝ := ∑' n : Mode,
  ‖∫ x in latticeCube 1 0, (f x : ℂ)*Complex.exp (-(⟪frequency n,x⟫_ℝ : ℂ)*Complex.I)‖^2 /
    ‖frequency n‖^2

/-- The bounded-density W₂ to homogeneous H⁻¹ inequality on the flat
torus, in weak coupling form. Projecting pairs of points to the torus only
decreases their separation. Each of N equally weighted couplings has mass m. -/
def PeriodicTransportInequality (A : ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (X Y : ι → Z → Position) (u v : Position → ℝ)
    {m B r : ℝ}, 0 ≤ m → 0 ≤ B → 0 ≤ r →
    AEStronglyMeasurable u volume → AEStronglyMeasurable v volume →
    (∀ x, u x ∈ Icc 0 B ∧ v x ∈ Icc 0 B) →
    (∀ i, Measurable (X i) ∧ Measurable (Y i) ∧ ∀ᵐ z ∂μ, dist (X i z) (Y i z) ≤ r) →
    (∀ φ : Position →ᵇ ℝ, unitPeriodic φ →
      (∫ x in latticeCube 1 0, u x * φ x) = m * ∑ i, ∫ z, φ (X i z) ∂μ) →
    (∀ φ : Position →ᵇ ℝ, unitPeriodic φ →
      (∫ x in latticeCube 1 0, v x * φ x) = m * ∑ i, ∫ z, φ (Y i z) ∂μ) →
    periodicNegativeNorm (fun x => u x-v x) ≤ A*B*((Fintype.card ι:ℝ)*m)*r^2

/-- The sharp cubic estimate for the actual periodic electrostatic fluctuation. -/
theorem physical_lattice_negative_norm (C : TetrahedronCone) {η : Mollifier}
    (K : PeriodicKernelCalculus η) (hk : tsupport η.kernel ⊆ closedBall 0 (1/100))
    {A : ℝ} (hA : 0 ≤ A) (transport : PeriodicTransportInequality A)
    {s : ℝ} (hs : 0 < s) (hu : s ≤ 1/2) :
    periodicNegativeNorm (fun x => (∑' p : LatticeTile, latticeWindow 1 s η p x) +
      upperSkeleton (latticeChart 1) η 1 s x - 1) ≤ 54*A*s^3 := by
  let w (d : ℝ) := smoothedIndicator (latticeShell 1 d) η d
  let c := shellCoefficient s
  have hvol := tetrahedron_volume (by norm_num : (0:ℝ)<1)
  have hc := shellCoefficient_bounds hs hu
  have m_eq : c*(regionVolume (tetrahedron 1)*shellFraction (s/2)) =
      regionVolume (tetrahedron 1)*shellFraction s := by
    have hn := (shellFraction_pos (half_pos hs) (by linarith : s/2≤1)).ne'
    dsimp only [c,shellCoefficient]
    field_simp
  have hm {d : ℝ} (hd : 0 < d) : AEStronglyMeasurable (w d) volume :=
    (K.convolution _ (latticeShell_measurable _ _) (fun m x => latticeShell_mem_shift m x) hd).1
  have bound (x) : (c*w (s/2) x) ∈ Icc 0 2 ∧ w s x ∈ Icc 0 2 := by
    have hf := smoothedIndicator_bounds (latticeShell 1 (s/2)) η (half_pos hs) x
    have hg := smoothedIndicator_bounds (latticeShell 1 s) η hs x
    exact ⟨⟨mul_nonneg hc.1 hf.1,(mul_le_mul hc.2 hf.2 hf.1 (by norm_num)).trans_eq (by norm_num)⟩,
      hg.1,hg.2.trans (by norm_num)⟩
  have hsupport (o) : ∀ᵐ z ∂C.law.prod K.law,
      dist (tileSample o (s/2) z) (tileSample o s z) ≤ 3*s := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
      ((continuous_tileSample o (s/2)).dist (continuous_tileSample o s)).measurable measurable_const)).2
    filter_upwards [C.support] with z hz
    filter_upwards [K.support] with k hm
    rw [dist_comm]
    exact shellSample_dist hs hu hz.1 hz.2 (mem_closedBall_zero_iff.mp (hk hm)) o
  have h := transport (C.law.prod K.law) (fun o => tileSample o (s/2)) (fun o => tileSample o s)
    (fun x => c*w (s/2) x) (w s) (m := regionVolume (tetrahedron 1)*shellFraction s)
    (mul_nonneg ENNReal.toReal_nonneg (shellFraction_pos hs (by linarith)).le) (by norm_num : (0:ℝ)≤2)
    (show 0 ≤ 3*s by positivity) ((hm (half_pos hs)).const_mul c) (hm hs) bound
    (fun o => ⟨(continuous_tileSample _ _).measurable,(continuous_tileSample _ _).measurable,hsupport o⟩)
    (by intro φ hφ
        simp_rw [mul_assoc]
        rw [integral_const_mul,periodic_shell_marginal C K (half_pos hs) (by linarith) φ hφ,← mul_assoc,m_eq,mul_assoc])
    (fun φ hφ => periodic_shell_marginal C K hs (by linarith) φ hφ)
  have eqn (x) := lattice_charge_shells (by norm_num : (0:ℝ)<1) hs η x
  simp only [div_one] at eqn
  change periodicNegativeNorm (fun x => _) ≤ _
  simp_rw [eqn]
  apply h.trans
  rw [card_cubeOrientation,hvol]
  have hfrac := shellFraction_le hs.le (by linarith : s≤1)
  nlinarith only [mul_le_mul_of_nonneg_right hfrac (show 0≤18*A*s^2 by positivity)]

end TSGA.SSW
