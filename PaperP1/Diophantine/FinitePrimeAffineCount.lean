module

public import PaperP1.Diophantine.AffineSmoothResidueClasses
public import PaperP1.Diophantine.FinitePrimeBiformCount

/-! # A global finite-prime count on the actual signed affine integer population

The two explicit numerical comparisons concern the exact determinant weights
and the actual derivative-divisor obstruction. All prime covers are proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePrimeAffineCount

open Polynomial Finset BivariateDegrees BivariateHeight GeometricFactorSwap
open AffineMonomialDeterminant CoarseGeometricPlaneCount SmoothResidueClasses

theorem bounded_count (G : ℤ[X][X]) (hne : G ≠ 0) (hgeom : Geometric G)
    (ha : 0 < degreeX G) (hb : 0 < degreeY G) (A J : ℕ) (hJ : J < degreeY G)
    (B : ℝ) (hB : 1 ≤ B) (P m : ℕ) (hP : 0 < P)
    (hdet : (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J <
      (P : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2))
    (hheight : (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      B ^ (degreeX G + 1) * B ^ degreeY G < (P : ℝ) ^ m)
    (S : Finset (ℤ × ℤ)) (hcurve : ∀ z ∈ S, G.evalEval z.1 z.2 = 0)
    (hx : ∀ z ∈ S, |(z.1 : ℝ)| ≤ B) (hy : ∀ z ∈ S, |(z.2 : ℝ)| ≤ B) :
    S.card ≤ 4 * (degreeY G + 1) + 4 * (degreeX G + 1) + 8 * degreeX G * degreeY G ^ 2 +
      (degreeX G + degreeY G) ^ 2 * (A + J) * (m * 2 ^ m * P) := by
  classical
  let R := S.filter (fun z ↦ badInteger G (lift z) ≠ 0)
  obtain ⟨T, _hcard, hprime, hsum, havoid⟩ := DyadicPrimeCover.uniform_pool P m hP
  have hsize (z : ℤ × ℤ) (hz : z ∈ S) : (badInteger G (lift z)).natAbs < P ^ m := by
    have hboxes := lift_box z B hB (hx z hz) (hy z hz)
    have hh := (ProjectivePrimeHeight.badInteger_bound G hb (lift z) B B hB hB
      (fun i ↦ (hboxes i).1) (fun i ↦ (hboxes i).2)).trans_lt hheight
    have hc : ((badInteger G (lift z)).natAbs : ℝ) < ((P ^ m : ℕ) : ℝ) := by
      simpa only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, Nat.cast_pow] using hh
    exact_mod_cast hc
  have hcover (z : ℤ × ℤ) (hz : z ∈ R) : ∃ p ∈ T, ¬(p : ℤ) ∣ badInteger G (lift z) :=
    havoid _ (mem_filter.mp hz).2 (hsize z (mem_filter.mp hz).1)
  let U (p : ℕ) := R.filter (fun z ↦ ¬(p : ℤ) ∣ badInteger G (lift z))
  have hU (p : ℕ) (hp : p ∈ T) : (U p).card ≤ (degreeX G + degreeY G) ^ 2 * (A + J) * p := by
    have hPp : (P : ℝ) ≤ p := by exact_mod_cast (hprime p hp).2.1.le
    have hd : (P : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2) ≤
        (p : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2) := by gcongr
    apply AffineSmoothResidueClasses.fixed_prime_count p (hprime p hp).1 G
      (ScalarIrreducibilityReflection.geometric_rational_irreducible G hne hgeom)
      A J hJ B (by linarith) (U p)
      (fun _ hz ↦ (mem_filter.mp hz).2)
      (fun z hz ↦ hcurve z (mem_filter.mp (mem_filter.mp hz).1).1)
      (fun z hz ↦ hx z (mem_filter.mp (mem_filter.mp hz).1).1)
      (fun z hz ↦ hy z (mem_filter.mp (mem_filter.mp hz).1).1) (hdet.trans_le hd)
  have hR : R.card ≤ (degreeX G + degreeY G) ^ 2 * (A + J) * (m * 2 ^ m * P) := by
    have hsub : R ⊆ T.biUnion U := by
      intro z hz
      obtain ⟨p, hp, hgood⟩ := hcover z hz
      exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hz, hgood⟩⟩
    calc
      _ ≤ (T.biUnion U).card := card_le_card hsub
      _ ≤ ∑ p ∈ T, (U p).card := card_biUnion_le
      _ ≤ ∑ p ∈ T, (degreeX G + degreeY G) ^ 2 * (A + J) * p := sum_le_sum hU
      _ = ((degreeX G + degreeY G) ^ 2 * (A + J)) * ∑ p ∈ T, p := (mul_sum _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hsum
  let E := S.filter (fun z ↦ badInteger G (lift z) = 0)
  have hE : E.card ≤ 4 * (degreeY G + 1) + 4 * (degreeX G + 1) +
      8 * degreeX G * degreeY G ^ 2 := by
    have hc := ProjectivePrimeExceptions.zero_product_card G hne hgeom ha hb (E.image lift) (by
      intro z hz
      obtain ⟨w, _hw, rfl⟩ := mem_image.mp hz
      exact lift_primitive w) (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact lift_curve G w (hcurve w (mem_filter.mp hw).1)) (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp hw).2)
    simpa only [card_image_of_injective _ lift_injective] using hc
  have hpartition : E.card + R.card = S.card :=
    card_filter_add_card_filter_not (s := S) (fun z ↦ badInteger G (lift z) = 0)
  omega

end PaperP1.FinitePrimeAffineCount
