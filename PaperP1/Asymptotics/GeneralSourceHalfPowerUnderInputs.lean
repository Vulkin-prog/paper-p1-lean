module

public import PaperP1.Arithmetic.UniformSourceSurfaceCover
public import PaperP1.Asymptotics.SourceCurvePointCover
public import PaperP1.Asymptotics.HalfPowerSurfaceCountParameters
public import PaperP1.Asymptotics.SurfaceCurveCoverPowerBound
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Actual general split-product integer hosts have a uniform half-power count under geometric inputs

The generic curve count and chosen-source surface covering are explicit
unproved arguments. Literal roots, source points, heights, curve degrees,
finite covers and exponent composition are proved internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralSourceHalfPowerUnderInputs

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.SplitRadicalPointHeight

theorem uniform_hosts (C A₀ ε : ℝ) (K D Jexp : ℕ) (hA₀ : 0 ≤ A₀) (hD : 0 < D)
    (hdegree : A₀ + (K : ℝ) ≤ 2 * D) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ kmax ≥ k, UniformSourceSurfaceCover.UniformCover kmax K D →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((D + 2).choose 2 + kmax) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ Jexp →
      ∀ s : List (PolynomialRing ℚ), k ≤ s.length → s.length ≤ kmax →
      ∀ (d : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ),
      (∀ i, s.get i = radicand (d i : ℚ) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) →
      (∀ i, d i ≠ 0) → (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) → (∀ i, (I i).Nonempty) → (∀ i, (J i).Nonempty) →
      (∀ i, (I i).card + (J i).card ≤ K) →
      (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, ∀ z ∈ J i, z.natAbs ≤ B) →
      (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, J i ⊆ T) →
      ∀ F : Finset (ℤ × ℤ), (∀ p ∈ F, SourceCurvePointCover.Admissible S T p) →
      (∀ p ∈ F, p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
      (∀ p ∈ F, ∃ w : Fin s.length → ℤ,
        ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * integerProduct (J i) p.2) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨k, δ, hk, hδ, hparameters⟩ := HalfPowerSurfaceCountParameters.parameters D ε hD hε
  obtain ⟨Noff, hoff⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) Jexp
  refine ⟨k, ?_⟩
  intro kmax _hkkmax hCover hPila
  obtain ⟨M, C₀, hC₀, hcover⟩ := hCover δ hδ
  obtain ⟨A₁, hA₁, hfinite⟩ := SourceCurvePointCover.finite_cover_bound kmax D M hD δ hδ (hPila M)
  let B₀ := OrdinaryRootPointHeight.constant K D
  let α := 2 / Real.sqrt ((2 : ℝ) ^ k) + δ
  let β := 1 / Real.sqrt ((2 : ℝ) ^ k) + δ
  let γ := 1 / (2 * (D : ℝ)) + δ
  let A := C₀ * B₀ ^ α + C₀ * A₁ * B₀ ^ (β + γ)
  have hB₀ : 1 ≤ B₀ := OrdinaryRootPointHeight.constant_ge_one K D
  have hB₀pos : 0 < B₀ := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, max 1 Noff, ?_⟩
  intro N hN L B hcrit hB hBL s hlength hcap d I J hs hd hI hJ hneI hneJ hK hiB hjB hdheight S T hiS hjT F hadmiss hxy hroots
  classical
  have hNpos : 1 ≤ N := by omega
  have hpolyR : ((L + 1 : ℕ) : ℝ) ^ Jexp < (N : ℝ) := by
    simpa only [one_mul] using hoff N (by omega) L hcrit
  have hBN : B ≤ N := hBL.trans (by exact_mod_cast hpolyR.le)
  have hiN (i) (z : ℤ) (hz : z ∈ I i) : z.natAbs ≤ N := (hiB i z hz).trans hBN
  have hjN (i) (z : ℤ) (hz : z ∈ J i) : z.natAbs ≤ N := (hjB i z hz).trans hBN
  have hK₂ : K ≤ 2 * D := by exact_mod_cast (show (K : ℝ) ≤ 2 * D by linarith)
  have hdeg (i) : (I i).card + (J i).card ≤ 2 * D := (hK i).trans hK₂
  have hexists (p : ℤ × ℤ) : ∃ w : Fin s.length → ℤ,
      p ∈ F → ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * integerProduct (J i) p.2 := by
    by_cases hp : p ∈ F
    · obtain ⟨w, hw⟩ := hroots p hp
      exact ⟨w, fun _ ↦ hw⟩
    · exact ⟨fun _ ↦ 0, fun h ↦ (hp h).elim⟩
  choose w hw using hexists
  let R := B₀ * (N : ℝ) ^ D
  let H := ⌊R⌋₊
  have hR : 1 ≤ R := by
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ D := one_le_pow₀ (by exact_mod_cast hNpos)
    dsimp [R]
    nlinarith
  have hH : 1 ≤ H := (Nat.one_le_floor_iff R).mpr hR
  have hheight : (H : ℝ) ≤ B₀ * (N : ℝ) ^ (D : ℝ) := by
    rw [Real.rpow_natCast]
    exact Nat.floor_le (by linarith)
  let U := F.image fun p ↦ SourceIntegerLift.point D p.1 p.2 (w p)
  have hU : U ⊆ SourceIntegerPoints.curvePoints D
      (RingHom.ker (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD).toRingHom) H := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    have hbox := (SourceIntegerPointHeight.point_floor_box I J d (w p) p.1 p.2 N K D A₀ hD hNpos
      (hxy p hp).1 (hxy p hp).2 hiN hjN hK hdegree hdheight (hw p hp)).2.2
    apply (SourceIntegerPoints.mem_curvePoints D _ H _).mpr
    exact ⟨(SourceIntegerPoints.mem_box D H _).mp hbox,
      SourceIntegerLift.global_relations_le_kernel d D I J hdeg hD p.1 p.2 (w p) (hw p hp)⟩
  obtain ⟨V, curves, hM, hV, hcurves, hcovered⟩ := hcover s hcap d I J hs hdeg hD hd hI hJ hneI hneJ hK H hH U hU
  have hfinite' := hfinite s hcap (hk.trans hlength) d I J hs hdeg hd hI hJ hneI hneJ S T hiS hjT F w
    hadmiss hw V curves H hH hM (fun p hp hnot ↦ hcovered _ (mem_image.mpr ⟨p, hp, rfl⟩) hnot)
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hdecay := UniformOrdinarySurfaceCover.decay_mono hlength
  have htwo : 2 / Real.sqrt ((2 : ℝ) ^ s.length) ≤ 2 / Real.sqrt ((2 : ℝ) ^ k) := by
    convert mul_le_mul_of_nonneg_left hdecay (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hV' : (V.card : ℝ) ≤ C₀ * (H : ℝ) ^ α := hV.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hHreal (add_le_add htwo (le_refl δ))) hC₀.le)
  have hcurves' : (curves.card : ℝ) ≤ C₀ * (H : ℝ) ^ β := hcurves.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hHreal (add_le_add hdecay (le_refl δ))) hC₀.le)
  obtain ⟨hfirst, hsecond⟩ := hparameters k le_rfl
  exact SurfaceCurveCoverPowerBound.finite_cover_bound N H B₀ (D : ℝ) (1 / 2 + ε) α β γ C₀ A₁
    (F.card : ℝ) (V.card : ℝ) (curves.card : ℝ) hNpos hH hB₀pos.le
    (by dsimp [α]; positivity) (by dsimp [β, γ]; positivity) hC₀.le hA₁.le
    hheight hfirst hsecond hfinite' hV' hcurves'

end PaperP1.GeneralSourceHalfPowerUnderInputs
