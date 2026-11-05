module

public import PaperP1.Diophantine.ProjectivePrimeHeight
public import PaperP1.Diophantine.GeometricEndpointExceptions
public import PaperP1.Arithmetic.DyadicPrimeCover

/-! # Global finite-prime counting from two explicit numerical comparisons -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePrimeBiformCount

open Polynomial Finset PaperP1.BidegreeOneFibreCount PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.SmoothResidueClasses

theorem bounded_count (G : ℤ[X][X]) (hne : G ≠ 0) (hgeom : GeometricFactorSwap.Geometric G)
    (ha : 0 < degreeX G) (hb : 0 < degreeY G) (H J : ℕ) (hJ : J < degreeY G)
    (L Y : ℝ) (hL : 1 ≤ L) (hY : 1 ≤ Y) (P m : ℕ) (hP : 0 < P)
    (hdet : ((H + 1) * (J + 1)).factorial * (L ^ H * Y ^ J) ^ ((H + 1) * (J + 1)) <
      (P : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2))
    (hheight : (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      L ^ (degreeX G + 1) * Y ^ degreeY G < (P : ℝ) ^ m)
    (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (hx : ∀ z ∈ S, ∀ c, |(z.1 c : ℝ)| ≤ L)
    (hy : ∀ z ∈ S, ∀ c, |(z.2 c : ℝ)| ≤ Y) :
    S.card ≤ 4 * (degreeY G + 1) + 4 * (degreeX G + 1) + 8 * degreeX G * degreeY G ^ 2 +
      4 * (degreeX G + degreeY G) ^ 2 * (H + J) * (m * 2 ^ m * P) := by
  classical
  let R := S.filter (fun z ↦ badInteger G z ≠ 0)
  obtain ⟨T, _hcard, hprime, hsum, havoid⟩ := DyadicPrimeCover.uniform_pool P m hP
  have hsize (z : Point) (hz : z ∈ S) : (badInteger G z).natAbs < P ^ m := by
    have hh := (ProjectivePrimeHeight.badInteger_bound G hb z L Y hL hY (hx z hz) (hy z hz)).trans_lt hheight
    have hc : ((badInteger G z).natAbs : ℝ) < ((P ^ m : ℕ) : ℝ) := by
      simpa only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, Nat.cast_pow] using hh
    exact_mod_cast hc
  have hcover (z : Point) (hz : z ∈ R) : ∃ p ∈ T, ¬(p : ℤ) ∣ badInteger G z :=
    havoid _ (mem_filter.mp hz).2 (hsize z (mem_filter.mp hz).1)
  let U (p : ℕ) := R.filter (fun z ↦ ¬(p : ℤ) ∣ badInteger G z)
  have hU (p : ℕ) (hp : p ∈ T) : (U p).card ≤ 4 * (degreeX G + degreeY G) ^ 2 * (H + J) * p := by
    have hPp : (P : ℝ) ≤ p := by exact_mod_cast (hprime p hp).2.1.le
    have hd : (P : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2) ≤
        (p : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2) := by gcongr
    apply fixed_prime_count p (hprime p hp).1 G hne hgeom H J hJ L Y (by linarith) (by linarith) (U p)
      (fun z hz ↦ hprim z (mem_filter.mp (mem_filter.mp hz).1).1)
      (fun _ hz ↦ (mem_filter.mp hz).2)
      (fun z hz ↦ hcurve z (mem_filter.mp (mem_filter.mp hz).1).1)
      (fun z hz c ↦ hx z (mem_filter.mp (mem_filter.mp hz).1).1 c)
      (fun z hz c ↦ hy z (mem_filter.mp (mem_filter.mp hz).1).1 c) (hdet.trans_le hd)
  have hR : R.card ≤ 4 * (degreeX G + degreeY G) ^ 2 * (H + J) * (m * 2 ^ m * P) := by
    have hsub : R ⊆ T.biUnion U := by
      intro z hz
      obtain ⟨p, hp, hgood⟩ := hcover z hz
      exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hz, hgood⟩⟩
    calc
      _ ≤ (T.biUnion U).card := card_le_card hsub
      _ ≤ ∑ p ∈ T, (U p).card := card_biUnion_le
      _ ≤ ∑ p ∈ T, 4 * (degreeX G + degreeY G) ^ 2 * (H + J) * p := sum_le_sum hU
      _ = (4 * (degreeX G + degreeY G) ^ 2 * (H + J)) * ∑ p ∈ T, p := (mul_sum _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hsum
  have hE := ProjectivePrimeExceptions.exceptional_card G hne hgeom ha hb S hprim hcurve
  have hpartition : (ProjectivePrimeExceptions.exceptional G S).card + R.card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun z ↦ badInteger G z = 0)
  omega

theorem unrestricted_second_pair_count (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : GeometricFactorSwap.Geometric G) (ha : 0 < degreeX G) (hb : 0 < degreeY G)
    (H J : ℕ) (hJ : J < degreeY G) (L : ℝ) (hL : 1 ≤ L) (P m : ℕ) (hP : 0 < P)
    (hdet : let Y : ℝ := (degreeX G + 1) * (height G : ℝ) * L ^ degreeX G
      ((H + 1) * (J + 1)).factorial * (L ^ H * Y ^ J) ^ ((H + 1) * (J + 1)) <
        (P : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2))
    (hheight : let Y : ℝ := (degreeX G + 1) * (height G : ℝ) * L ^ degreeX G
      (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
        L ^ (degreeX G + 1) * Y ^ degreeY G < (P : ℝ) ^ m)
    (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (hx : ∀ z ∈ S, ∀ c, |(z.1 c : ℝ)| ≤ L) :
    S.card ≤ 8 * (degreeX G + 1) * (degreeY G + 1) +
      4 * (degreeY G + 1) + 4 * (degreeX G + 1) + 8 * degreeX G * degreeY G ^ 2 +
        4 * (degreeX G + degreeY G) ^ 2 * (H + J) * (m * 2 ^ m * P) := by
  classical
  let E := GeometricEndpointExceptions.exceptional G S
  let R := S \ E
  let Y : ℝ := (degreeX G + 1) * (height G : ℝ) * L ^ degreeX G
  have hheightG : (1 : ℝ) ≤ height G := by exact_mod_cast GeometricBiformCoarseCount.height_pos G hne
  have hpow : (1 : ℝ) ≤ L ^ degreeX G := one_le_pow₀ hL
  have hY : 1 ≤ Y := by
    have haR : (1 : ℝ) ≤ degreeX G + 1 := by
      have hn : (0 : ℝ) ≤ degreeX G := Nat.cast_nonneg _
      linarith
    exact (by norm_num : (1 : ℝ) = 1 * 1 * 1).trans_le
      (mul_le_mul (mul_le_mul haR hheightG (by norm_num) (by positivity)) hpow (by norm_num) (by positivity))
  have hs := GeometricEndpointExceptions.height_split G hne hgeom ha hb S hprim hcurve L (by linarith) hx
  have hc := bounded_count G hne hgeom ha hb H J hJ L Y hL hY P m hP hdet hheight R
    (fun z hz ↦ hprim z (mem_sdiff.mp hz).1) (fun z hz ↦ hcurve z (mem_sdiff.mp hz).1)
    (fun z hz c ↦ hx z (mem_sdiff.mp hz).1 c) hs.2
  have hpartition : R.card + E.card = S.card :=
    Finset.card_sdiff_add_card_eq_card (show E ⊆ S from Finset.filter_subset _ _)
  have he : E.card ≤ 8 * (degreeX G + 1) * (degreeY G + 1) := hs.1
  omega

end PaperP1.FinitePrimeBiformCount
