module

public import PaperP1.Algebra.ThirdFactorialCumulant
public import Mathlib.Tactic.Positivity

/-! # Explicit repeated-index cost at third factorial order -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.RepeatedIndexCost

open Finset

variable {ι : Type*}

def cost (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) : ℝ :=
  -6 * (∑ e ∈ G.powersetCard 2, (∑ x ∈ e, p x) * c e) + 2 * ∑ x ∈ G, (p x) ^ 3

theorem pair_bound (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) (P : ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x) (hcap : ∀ x ∈ G, p x ≤ P) :
    |∑ e ∈ G.powersetCard 2, (∑ x ∈ e, p x) * c e| ≤
      (2 * P) * ∑ e ∈ G.powersetCard 2, |c e| := by
  calc
    _ ≤ ∑ e ∈ G.powersetCard 2, |(∑ x ∈ e, p x) * c e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ G.powersetCard 2, (2 * P) * |c e| := by
      apply sum_le_sum
      intro e he
      obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp he
      have hpe : 0 ≤ ∑ x ∈ e, p x := sum_nonneg fun x hx ↦ hp x (hsub hx)
      have hbound : (∑ x ∈ e, p x) ≤ 2 * P := by
        calc
          _ ≤ ∑ _x ∈ e, P := sum_le_sum fun x hx ↦ hcap x (hsub hx)
          _ = _ := by simp only [sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat]
      rw [abs_mul, abs_of_nonneg hpe]
      exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
    _ = _ := (mul_sum _ _ _).symm

theorem cube_bound (p : ι → ℝ) (G : Finset ι) (P : ℝ) (hP : 0 ≤ P)
    (hp : ∀ x ∈ G, 0 ≤ p x) (hcap : ∀ x ∈ G, p x ≤ P) :
    (∑ x ∈ G, (p x) ^ 3) ≤ P ^ 2 * ∑ x ∈ G, p x := by
  rw [mul_sum]
  apply sum_le_sum
  intro x hx
  have hsq : (p x) ^ 2 ≤ P ^ 2 := by
    simpa only [pow_two] using mul_le_mul (hcap x hx) (hcap x hx) (hp x hx) hP
  calc
    (p x) ^ 3 = (p x) ^ 2 * p x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsq (hp x hx)

theorem bound (p : ι → ℝ) (c : Finset ι → ℝ) (G : Finset ι) (P : ℝ) (hP : 0 ≤ P)
    (hp : ∀ x ∈ G, 0 ≤ p x) (hcap : ∀ x ∈ G, p x ≤ P) :
    |cost p c G| ≤ 12 * P * (∑ e ∈ G.powersetCard 2, |c e|) +
      2 * P ^ 2 * ∑ x ∈ G, p x := by
  have hcubes : 0 ≤ ∑ x ∈ G, (p x) ^ 3 := sum_nonneg fun x hx ↦ pow_nonneg (hp x hx) 3
  calc
    _ ≤ |-6 * (∑ e ∈ G.powersetCard 2, (∑ x ∈ e, p x) * c e)| +
        |2 * ∑ x ∈ G, (p x) ^ 3| := abs_add_le _ _
    _ = 6 * |∑ e ∈ G.powersetCard 2, (∑ x ∈ e, p x) * c e| + 2 * ∑ x ∈ G, (p x) ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hcubes]
      norm_num
    _ ≤ 6 * ((2 * P) * ∑ e ∈ G.powersetCard 2, |c e|) + 2 * (P ^ 2 * ∑ x ∈ G, p x) :=
      add_le_add (mul_le_mul_of_nonneg_left (pair_bound p c G P hp hcap) (by norm_num))
        (mul_le_mul_of_nonneg_left (cube_bound p G P hP hp hcap) (by norm_num))
    _ = _ := by ring

end PaperP1.RepeatedIndexCost
