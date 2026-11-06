module

public import PaperP1.Arithmetic.SeparatedQuadraticPointCount
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Exact main term and explicit error from one-variable quadratic-character sums

The one-variable cancellation hypotheses in `error_bound` are explicit. The
identity itself and the trivial comparison for the other variable are proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedQuadraticPointError

open Finset SeparatedQuadraticPointCount QuadraticCharacterRootCount
open scoped Classical

variable {F ι : Type*} [Field F] [Fintype F] [Fintype ι]

omit [Fintype ι] in
theorem character_sum_abs_le_card (A : ι → F → F) (s : Finset ι) :
    |(characterSum A s : ℝ)| ≤ Fintype.card F := by
  rw [characterSum, Int.cast_sum]
  calc
    _ ≤ ∑ x : F, |(quadraticChar F (∏ i ∈ s, A i x) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : F, (1 : ℝ) := sum_le_sum (fun x _ ↦ quadratic_character_abs_le_one _)
    _ = _ := by simp

theorem error_identity (hodd : ringChar F ≠ 2) (c : ι → F) (A B : ι → F → F) :
    ((points c A B).card : ℝ) - (Fintype.card F : ℝ) ^ 2 =
      ∑ s ∈ (univ : Finset ι).powerset.erase ∅,
        (quadraticChar F (∏ i ∈ s, c i) : ℝ) * characterSum A s * characterSum B s := by
  have he : ((points c A B).card : ℝ) =
      ∑ s ∈ (univ : Finset ι).powerset,
        (quadraticChar F (∏ i ∈ s, c i) : ℝ) * characterSum A s * characterSum B s := by
    exact_mod_cast character_expansion hodd c A B
  have hsum := sum_erase_add (s := (univ : Finset ι).powerset)
    (fun s ↦ (quadraticChar F (∏ i ∈ s, c i) : ℝ) * characterSum A s * characterSum B s)
    (empty_mem_powerset (s := univ))
  have hempty : (quadraticChar F (∏ i ∈ (∅ : Finset ι), c i) : ℝ) *
      characterSum A ∅ * characterSum B ∅ = (Fintype.card F : ℝ) ^ 2 := by
    simp only [prod_empty, map_one, Int.cast_one, one_mul, empty_character_sum, Int.cast_natCast, pow_two]
  rw [hempty, ← he] at hsum
  linarith only [hsum]

theorem error_bound (hodd : ringChar F ≠ 2) (c : ι → F) (A B : ι → F → F)
    (E : ℝ) (hE : 0 ≤ E)
    (hcancel : ∀ s ∈ (univ : Finset ι).powerset.erase ∅,
      |(characterSum A s : ℝ)| ≤ E ∨ |(characterSum B s : ℝ)| ≤ E) :
    |((points c A B).card : ℝ) - (Fintype.card F : ℝ) ^ 2| ≤
      ((univ : Finset ι).powerset.erase ∅).card * E * Fintype.card F := by
  rw [error_identity hodd]
  calc
    _ ≤ ∑ s ∈ (univ : Finset ι).powerset.erase ∅,
        |(quadraticChar F (∏ i ∈ s, c i) : ℝ) * characterSum A s * characterSum B s| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ (univ : Finset ι).powerset.erase ∅, E * Fintype.card F := by
      apply sum_le_sum
      intro s hs
      rw [abs_mul, abs_mul]
      have hc := quadratic_character_abs_le_one (∏ i ∈ s, c i)
      have hA := character_sum_abs_le_card A s
      have hB := character_sum_abs_le_card B s
      have hcoef : |(quadraticChar F (∏ i ∈ s, c i) : ℝ)| * |(characterSum A s : ℝ)| *
          |(characterSum B s : ℝ)| ≤ |(characterSum A s : ℝ)| * |(characterSum B s : ℝ)| := by
        simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hc
          (mul_nonneg (abs_nonneg (characterSum A s : ℝ)) (abs_nonneg (characterSum B s : ℝ)))
      apply hcoef.trans
      rcases hcancel s hs with ha | hb
      · exact mul_le_mul ha hB (abs_nonneg _) hE
      · calc
          _ ≤ (Fintype.card F : ℝ) * E := mul_le_mul hA hb (abs_nonneg _) (by positivity)
          _ = _ := mul_comm _ _
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_assoc]

end PaperP1.SeparatedQuadraticPointError
