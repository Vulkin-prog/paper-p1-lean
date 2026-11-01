module

public import PaperP1.Arithmetic.RationalTripleOverlap
public import Mathlib.Data.Int.GCD

/-! # The literal integer-slope statement of main Lemma 14.2 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleIntegers

open PaperP1.RationalTripleDensity

def density (u v w : ℤ) : ℝ :=
  (Int.gcd u v : ℝ) / (v : ℝ) +
    ((Int.gcd u w : ℝ) + Int.gcd v w - 1) / (w : ℝ)

theorem positive_reduction {u v w : ℤ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Int.gcd (Int.gcd u v : ℤ) w = 1) :
    u.natAbs < v.natAbs ∧ v.natAbs < w.natAbs ∧
      w.natAbs < 2 * u.natAbs ∧ Nat.gcd (Nat.gcd u.natAbs v.natAbs) w.natAbs = 1 := by
  have hu : 0 ≤ u := by omega
  have hv : 0 ≤ v := by omega
  have hw : 0 ≤ w := by omega
  refine ⟨Int.natAbs_lt_natAbs_of_nonneg_of_lt hu huv,
    Int.natAbs_lt_natAbs_of_nonneg_of_lt hv hvw, ?_, ?_⟩
  · have h := Int.natAbs_lt_natAbs_of_nonneg_of_lt hw hw2u
    simpa only [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 by rfl] using h
  · simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] using hprimitive

theorem density_eq_nat {u v w : ℤ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u) :
    density u v w = RationalTripleDensity.density u.natAbs v.natAbs w.natAbs := by
  have hu : 0 ≤ u := by omega
  have hv : 0 ≤ v := by omega
  have hw : 0 ≤ w := by omega
  have huvN := Int.natAbs_lt_natAbs_of_nonneg_of_lt hu huv
  have hvwN := Int.natAbs_lt_natAbs_of_nonneg_of_lt hv hvw
  have hvR : (v.natAbs : ℝ) = (v : ℝ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.natAbs_of_nonneg hv)
    simpa only [Int.cast_natCast] using h
  have hwR : (w.natAbs : ℝ) = (w : ℝ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.natAbs_of_nonneg hw)
    simpa only [Int.cast_natCast] using h
  rw [RationalTripleDensity.density_ordered huvN.le hvwN.le]
  simp only [density, Int.gcd_eq_natAbs_gcd_natAbs, hvR, hwR]

theorem extremal_value : density 10 12 15 = 19 / 30 := by
  norm_num [density, Int.gcd_eq_natAbs_gcd_natAbs]

theorem next_value : density 8 9 12 = 11 / 18 := by
  norm_num [density, Int.gcd_eq_natAbs_gcd_natAbs]

theorem gap {u v w : ℤ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Int.gcd (Int.gcd u v : ℤ) w = 1) :
    (u = 10 ∧ v = 12 ∧ w = 15) ∨ density u v w ≤ 11 / 18 := by
  obtain ⟨huvN, hvwN, hw2uN, hprimitiveN⟩ := positive_reduction huv hvw hw2u hprimitive
  rcases RationalTripleOverlap.gap huvN hvwN hw2uN hprimitiveN with h | h
  · have hu : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg (by omega)
    have hv : (v.natAbs : ℤ) = v := Int.natAbs_of_nonneg (by omega)
    have hw : (w.natAbs : ℤ) = w := Int.natAbs_of_nonneg (by omega)
    left
    omega
  · right
    rwa [density_eq_nat huv hvw hw2u]

/-- Main Lemma 14.2 for every integer triple in the printed range. -/
theorem article_14_2 {u v w : ℤ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Int.gcd (Int.gcd u v : ℤ) w = 1) : density u v w ≤ 19 / 30 := by
  rcases gap huv hvw hw2u hprimitive with ⟨rfl, rfl, rfl⟩ | h
  · exact extremal_value.le
  · exact h.trans (by norm_num)

theorem equality_iff {u v w : ℤ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Int.gcd (Int.gcd u v : ℤ) w = 1) :
    density u v w = 19 / 30 ↔ u = 10 ∧ v = 12 ∧ w = 15 := by
  constructor
  · intro heq
    rcases gap huv hvw hw2u hprimitive with h | h
    · exact h
    · rw [heq] at h
      norm_num at h
  · rintro ⟨rfl, rfl, rfl⟩
    exact extremal_value

theorem bound_away_from_extremal {u v w : ℤ} (huv : u < v) (hvw : v < w)
    (hw2u : w < 2 * u) (hprimitive : Int.gcd (Int.gcd u v : ℤ) w = 1)
    (hne : ¬(u = 10 ∧ v = 12 ∧ w = 15)) : density u v w ≤ 11 / 18 :=
  (gap huv hvw hw2u hprimitive).resolve_left hne

/-- Both endpoints are attained in the actual primitive ordered domain. -/
theorem sharp_witnesses :
    (10 : ℤ) < 12 ∧ (12 : ℤ) < 15 ∧ (15 : ℤ) < 2 * 10 ∧
      Int.gcd (Int.gcd 10 12 : ℤ) 15 = 1 ∧ density 10 12 15 = 19 / 30 ∧
    (8 : ℤ) < 9 ∧ (9 : ℤ) < 12 ∧ (12 : ℤ) < 2 * 8 ∧
      Int.gcd (Int.gcd 8 9 : ℤ) 12 = 1 ∧ density 8 9 12 = 11 / 18 := by
  norm_num [density, Int.gcd_eq_natAbs_gcd_natAbs]

end PaperP1.RationalTripleIntegers
