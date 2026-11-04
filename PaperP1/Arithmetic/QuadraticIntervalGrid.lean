module

public import PaperP1.Asymptotics.RelativeIntervalSideSum

/-! # The actual quadratic interval grid has uniformly bounded multiplicity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticIntervalGrid

open Finset

def grid (M k : ℕ) : ℕ := k ^ 2 / M

theorem same_grid_square_gaps (M k l : ℕ) (hM : 0 < M) (heq : grid M k = grid M l) :
    k ^ 2 < l ^ 2 + M ∧ l ^ 2 < k ^ 2 + M := by
  change k ^ 2 / M = l ^ 2 / M at heq
  have hk := Nat.div_add_mod (k ^ 2) M
  have hl := Nat.div_add_mod (l ^ 2) M
  rw [heq] at hk
  have hrk := Nat.mod_lt (k ^ 2) hM
  have hrl := Nat.mod_lt (l ^ 2) hM
  constructor <;> omega

theorem same_grid_close (M k l : ℕ) (hM : 0 < M) (hk : M ≤ 4 * k) (hl : M ≤ 4 * l)
    (heq : grid M k = grid M l) : k ≤ l + 1 ∧ l ≤ k + 1 := by
  have h := same_grid_square_gaps M k l hM heq
  constructor
  · by_contra hn
    have hgap : l + 2 ≤ k := by omega
    have hsq := Nat.pow_le_pow_left hgap 2
    nlinarith [h.1]
  · by_contra hn
    have hgap : k + 2 ≤ l := by omega
    have hsq := Nat.pow_le_pow_left hgap 2
    nlinarith [h.2]

theorem fibre_card (M : ℕ) (hM : 0 < M) (I : Finset ℕ) (hlow : ∀ k ∈ I, M ≤ 4 * k) (q : ℕ) :
    (I.filter (fun k ↦ grid M k = q)).card ≤ 2 := by
  let S := I.filter (fun k ↦ grid M k = q)
  rcases S.eq_empty_or_nonempty with hS | hS
  · change S.card ≤ 2
    rw [hS, card_empty]
    omega
  · let m := S.min' hS
    have hm : m ∈ S := S.min'_mem hS
    have hsub : S ⊆ Icc m (m + 1) := by
      intro k hk
      have hki := mem_filter.mp hk
      have hmi := mem_filter.mp hm
      have heq : grid M k = grid M m := hki.2.trans hmi.2.symm
      have hclose := same_grid_close M k m hM (hlow k hki.1) (hlow m hmi.1) heq
      exact mem_Icc.mpr ⟨S.min'_le k hk, hclose.1⟩
    calc
      _ ≤ (Icc m (m + 1)).card := card_le_card hsub
      _ = 2 := by rw [Nat.card_Icc]; omega

theorem grid_upper (M k : ℕ) (hM : 0 < M) (hk : k ≤ 2 * M) : grid M k ≤ 4 * M := by
  have hsq : k ^ 2 ≤ (4 * M) * M := by
    have h := Nat.pow_le_pow_left hk 2
    nlinarith
  exact Nat.le_of_mul_le_mul_right ((Nat.div_mul_le_self (k ^ 2) M).trans hsq) hM

theorem grid_lower (M k : ℕ) (hM : 32 ≤ M) (hk : M ≤ 4 * k) : M ≤ 32 * grid M k := by
  have hMp : 0 < M := by omega
  have hsq : M ^ 2 ≤ 16 * k ^ 2 := by
    have h := Nat.pow_le_pow_left hk 2
    nlinarith
  have hd := Nat.div_add_mod (k ^ 2) M
  have hr := Nat.mod_lt (k ^ 2) hMp
  have hupper : k ^ 2 < (grid M k + 1) * M := by dsimp [grid]; nlinarith
  have hprod : M * M < (16 * (grid M k + 1)) * M := by nlinarith
  have hlinear : M < 16 * (grid M k + 1) := by
    by_contra h
    have hh : 16 * (grid M k + 1) ≤ M := by omega
    have hmul := Nat.mul_le_mul_right M hh
    omega
  omega

theorem remainder_identity (M k : ℕ) (hM : 0 < M) :
    (k : ℝ) ^ 2 / M - grid M k = (((k ^ 2) % M : ℕ) : ℝ) / M := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hd : (grid M k : ℝ) * M + (((k ^ 2) % M : ℕ) : ℝ) = (k : ℝ) ^ 2 := by
    have hn : grid M k * M + (k ^ 2) % M = k ^ 2 := by
      simpa only [grid, Nat.mul_comm] using Nat.div_add_mod (k ^ 2) M
    exact_mod_cast hn
  field_simp
  nlinarith only [hd]

theorem grid_error (M k : ℕ) (hM : 0 < M) :
    0 ≤ (k : ℝ) ^ 2 / M - grid M k ∧ (k : ℝ) ^ 2 / M - grid M k < 1 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hr : (((k ^ 2) % M : ℕ) : ℝ) < M := by exact_mod_cast Nat.mod_lt (k ^ 2) hM
  rw [remainder_identity M k hM]
  exact ⟨div_nonneg (Nat.cast_nonneg _) hMR.le, (div_lt_one hMR).mpr hr⟩

theorem quadratic_grid_error (M k : ℕ) (hM : 0 < M) :
    0 ≤ ((k : ℝ) / M) ^ 2 - (grid M k : ℝ) / M ∧
      ((k : ℝ) / M) ^ 2 - (grid M k : ℝ) / M ≤ 1 / M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : ((k : ℝ) / M) ^ 2 - (grid M k : ℝ) / M =
      ((k : ℝ) ^ 2 / M - grid M k) / M := by field_simp
  rw [heq]
  have he := grid_error M k hM
  exact ⟨div_nonneg he.1 hMR.le, div_le_div_of_nonneg_right he.2.le hMR.le⟩

theorem scaled_center_error (M k : ℕ) (hM : 0 < M) (r : ℝ) (hr : 0 ≤ r) :
    |r * ((k : ℝ) / M) ^ 2 - r * ((grid M k : ℝ) / M)| ≤ r / M := by
  have he := quadratic_grid_error M k hM
  rw [← mul_sub, abs_mul, abs_of_nonneg hr, abs_of_nonneg he.1]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he.2 hr

end PaperP1.QuadraticIntervalGrid
