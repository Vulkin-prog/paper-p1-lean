module

public import PaperP1.Diophantine.AffineSmoothResidueClasses
public import PaperP1.Arithmetic.RedundantPrimeCover
public import PaperP1.Diophantine.FinitePrimeBiformCount

/-! # Affine point counts averaged over a redundant actual prime pool

The absolute pool threshold precedes the equation, degrees, scale and population.
Each nonexceptional point is counted by at least m primes. Averaging cancels the pool cardinality factor in the global bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AveragedPrimeAffineCount

open Polynomial Finset BivariateDegrees BivariateHeight GeometricFactorSwap
open AffineMonomialDeterminant CoarseGeometricPlaneCount SmoothResidueClasses

theorem uniform_bound : ∃ P₀ : ℕ, 16 ≤ P₀ ∧ ∀ P ≥ P₀, ∀ m : ℕ, 1 ≤ m → (m : ℝ) * Real.log P ≤ P →
    ∀ G : ℤ[X][X], G ≠ 0 → Geometric G →
    0 < degreeX G → 0 < degreeY G → ∀ A J : ℕ, J < degreeY G →
    ∀ B : ℝ, 1 ≤ B →
    (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J <
      (P : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2) →
    (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      B ^ (degreeX G + 1) * B ^ degreeY G < (P : ℝ) ^ m →
    ∀ S : Finset (ℤ × ℤ), (∀ z ∈ S, G.evalEval z.1 z.2 = 0) →
    (∀ z ∈ S, |(z.1 : ℝ)| ≤ B) → (∀ z ∈ S, |(z.2 : ℝ)| ≤ B) →
    S.card ≤ 4 * (degreeY G + 1) + 4 * (degreeX G + 1) + 8 * degreeX G * degreeY G ^ 2 +
      (degreeX G + degreeY G) ^ 2 * (A + J) * (32 * P) := by
  classical
  obtain ⟨P₀, hP₀, hpool⟩ := RedundantPrimeCover.uniform_pool
  refine ⟨P₀, hP₀, ?_⟩
  intro P hP m hmpos hm G hne hgeom ha hb A J hJ B hB hdet hheight S hcurve hx hy
  let R := S.filter (fun z ↦ badInteger G (lift z) ≠ 0)
  obtain ⟨T, _hcard, hprime, hsum, havoid⟩ := hpool P hP m hm
  have hsize (z : ℤ × ℤ) (hz : z ∈ S) : (badInteger G (lift z)).natAbs < P ^ m := by
    have hboxes := lift_box z B hB (hx z hz) (hy z hz)
    have hh := (ProjectivePrimeHeight.badInteger_bound G hb (lift z) B B hB hB
      (fun i ↦ (hboxes i).1) (fun i ↦ (hboxes i).2)).trans_lt hheight
    have hc : ((badInteger G (lift z)).natAbs : ℝ) < ((P ^ m : ℕ) : ℝ) := by
      simpa only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, Nat.cast_pow] using hh
    exact_mod_cast hc
  have hcover (z : ℤ × ℤ) (hz : z ∈ R) :
      m ≤ (T.filter (fun p : ℕ ↦ ¬(p : ℤ) ∣ badInteger G (lift z))).card :=
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
  have hR : R.card ≤ (degreeX G + degreeY G) ^ 2 * (A + J) * (32 * P) := by
    have hincidence : R.card * m ≤ ∑ p ∈ T, (U p).card := by
      calc
        _ = ∑ _z ∈ R, m := by simp
        _ ≤ ∑ z ∈ R, (T.filter (fun p : ℕ ↦ ¬(p : ℤ) ∣ badInteger G (lift z))).card :=
          sum_le_sum hcover
        _ = ∑ p ∈ T, (U p).card := by
          simp only [U, card_eq_sum_ones, sum_filter]
          rw [sum_comm]
    have hbound : (∑ p ∈ T, (U p).card) ≤
        ((degreeX G + degreeY G) ^ 2 * (A + J) * (32 * P)) * m := by
      calc
        _ ≤ ∑ p ∈ T, (degreeX G + degreeY G) ^ 2 * (A + J) * p := sum_le_sum hU
        _ = ((degreeX G + degreeY G) ^ 2 * (A + J)) * ∑ p ∈ T, p := (mul_sum _ _ _).symm
        _ ≤ ((degreeX G + degreeY G) ^ 2 * (A + J)) * (32 * m * P) := Nat.mul_le_mul_left _ hsum
        _ = _ := by ring
    have hh := hincidence.trans hbound
    nlinarith only [hh, hmpos]
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

end PaperP1.AveragedPrimeAffineCount
