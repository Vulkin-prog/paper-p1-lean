module

public import PaperP1.Arithmetic.AsymmetricShiftedWitness

/-! # The shifted family lies outside radius one and inside radius two

The exclusion is uniform over EVERY reduced slope up to the actual cubic
height cap. A shifted rational family is not excluded merely by checking
its obvious slope.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedAlignmentRadius

open PaperP1.AsymmetricShiftedWitness

theorem reduced_two_three {r s : ℕ} (hcop : r.Coprime s) (he : 3 * r = 2 * s) : r = 2 ∧ s = 3 := by
  have hdiv : 2 ∣ r := (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 2 3)).mp ⟨s, he⟩
  obtain ⟨q, hq⟩ := hdiv
  have hs : s = 3 * q := by omega
  have hg : Nat.gcd (2 * q) (3 * q) = 1 := by rw [← hq, ← hs]; exact hcop.gcd_eq_one
  norm_num [Nat.gcd_mul_right] at hg
  exact ⟨by omega, by omega⟩

theorem shifted_difference (t k : ℕ) :
    (2 : ℤ) * target t k - 3 * source t = 6 * (width k : ℤ) := by
  dsimp [target, source]
  ring

theorem narrow_nonalignment (t k : ℕ) (hlarge : 5 * (width k) ^ 4 < t) :
    ¬ CompressedTargetAlignment.Aligned 1 (source t) (target t k) (3 * k) := by
  rintro ⟨r, s, _hr, _hs, hcop, hrB, hsB, hgeom₀⟩
  have hgeom : |(r : ℤ) * target t k - (s : ℤ) * source t| ≤
      ((r : ℤ) + s) * (width k : ℤ) := by
    simpa [width] using hgeom₀
  have hrB' : r ≤ (width k) ^ 3 := hrB
  have hsB' : s ≤ (width k) ^ 3 := hsB
  have hnum : (4 * r + s) * width k ≤ 5 * (width k) ^ 4 := by
    calc
      _ ≤ (5 * (width k) ^ 3) * width k := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have heq : ((3 : ℤ) * r - 2 * s) * t =
      ((r : ℤ) * target t k - (s : ℤ) * source t) - 3 * r * (width k : ℤ) := by
    dsimp [target, source]
    ring
  have hbound : |((3 : ℤ) * r - 2 * s) * t| ≤ ((5 * (width k) ^ 4 : ℕ) : ℤ) := by
    calc
      _ = |((r : ℤ) * target t k - (s : ℤ) * source t) - 3 * r * (width k : ℤ)| := congrArg abs heq
      _ ≤ |(r : ℤ) * target t k - (s : ℤ) * source t| + |3 * r * (width k : ℤ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le ((r : ℤ) * target t k - (s : ℤ) * source t) 0 (3 * r * (width k : ℤ))
      _ ≤ ((r : ℤ) + s) * (width k : ℤ) + 3 * r * (width k : ℤ) :=
        add_le_add hgeom (le_of_eq (abs_of_nonneg (by positivity)))
      _ = (4 * (r : ℤ) + s) * (width k : ℤ) := by ring
      _ ≤ _ := by exact_mod_cast hnum
  have hdet : (3 : ℤ) * r - 2 * s = 0 := by
    by_contra hne
    have hone := Int.one_le_abs hne
    have ht : (t : ℤ) ≤ |((3 : ℤ) * r - 2 * s) * t| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) t)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (Nat.cast_nonneg (α := ℤ) t)
    have hlargeZ : ((5 * (width k) ^ 4 : ℕ) : ℤ) < t := by exact_mod_cast hlarge
    omega
  have hslope : 3 * r = 2 * s := by exact_mod_cast sub_eq_zero.mp hdet
  obtain ⟨hr, hs⟩ := reduced_two_three hcop hslope
  rw [hr, hs] at hgeom
  norm_num only [Nat.cast_ofNat] at hgeom
  rw [shifted_difference, abs_of_nonneg (by positivity)] at hgeom
  have hB : (0 : ℤ) < width k := by dsimp [width]; omega
  omega

theorem enlarged_alignment (t k : ℕ) (hk : 1 ≤ k) :
    CompressedTargetAlignment.Aligned 2 (source t) (target t k) (3 * k) := by
  have hB : 2 ≤ width k := by dsimp [width]; omega
  have hpow : 8 ≤ (width k) ^ 3 := Nat.pow_le_pow_left hB 3
  refine ⟨2, 3, by decide, by decide, by decide,
    by change 2 ≤ (width k) ^ 3; omega,
    by change 3 ≤ (width k) ^ 3; omega, ?_⟩
  change |(2 : ℤ) * target t k - 3 * source t| ≤ (2 + 3) * (2 * (width k : ℤ))
  rw [shifted_difference, abs_of_nonneg (by positivity)]
  nlinarith only [Nat.cast_nonneg (α := ℤ) (width k)]

end PaperP1.ShiftedAlignmentRadius
