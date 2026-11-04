module

public import PaperP1.Analysis.AdjacentSquarefreeBudget
public import PaperP1.Diophantine.QuadraticKernelRanges
public import Mathlib.Data.Nat.Squarefree

/-! # An elementary finite lower bound for consecutive squarefree integers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AdjacentSquarefreeCount

open Finset PaperP1.AdjacentSquarefreeBudget

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def good (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun n ↦ Squarefree n ∧ Squarefree (n + 1))

def bad (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun n ↦ ¬(Squarefree n ∧ Squarefree (n + 1)))

def divisorStarts (X d t : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun n ↦ d ∣ n + t)

theorem divisor_count (X d t : ℕ) (hd : 0 < d) :
    ((divisorStarts X d t).card : ℝ) ≤ ((X + t : ℕ) : ℝ) / d := by
  have hinj : Function.Injective (fun n : ℕ ↦ n + t) := by
    intro n m h
    change n + t = m + t at h
    omega
  rw [← card_image_of_injective _ hinj]
  apply PaperP1.QuadraticKernelRanges.divisible_card _ (by positivity) d hd
  intro q hq
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
  obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hnI
  exact ⟨by omega, by exact_mod_cast (show n + t ≤ X + t by omega), hdiv⟩

theorem square_divisor_index (n X : ℕ) (hn : 0 < n) (hX : n ≤ X + 1)
    (hs : ¬Squarefree n) : ∃ j ∈ range ((X + 1) + 1), modulus j ∣ n := by
  have hp : ¬∀ p : ℕ, Nat.Prime p → ¬p * p ∣ n := by
    intro h
    exact hs (Nat.squarefree_iff_prime_squarefree.mpr h)
  push Not at hp
  obtain ⟨p, hp, hdiv⟩ := hp
  have hpn : p ≤ n := Nat.le_of_dvd hn ((dvd_mul_right p p).trans hdiv)
  rcases hp.eq_two_or_odd' with htwo | hodd
  · refine ⟨0, by simp, ?_⟩
    subst p
    exact hdiv
  · obtain ⟨j, hj⟩ := hodd
    have hpos := hp.two_le
    have hj0 : j ≠ 0 := by omega
    have heq : p = 2 * j + 1 := by omega
    refine ⟨j, mem_range.mpr (by omega), ?_⟩
    simpa only [modulus, ite_eq_right hj0, pow_two, ← heq] using hdiv

theorem bad_cover (X : ℕ) : bad X ⊆ (range ((X + 1) + 1)).biUnion
    (fun j ↦ divisorStarts X (modulus j) 0 ∪ divisorStarts X (modulus j) 1) := by
  intro n hn
  obtain ⟨hnI, hs⟩ := mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hnI
  by_cases hsn : Squarefree n
  · have hsucc : ¬Squarefree (n + 1) := fun h ↦ hs ⟨hsn, h⟩
    obtain ⟨j, hj, hd⟩ := square_divisor_index (n + 1) X (by omega) (by omega) hsucc
    exact mem_biUnion.mpr ⟨j, hj, mem_union_right _ (mem_filter.mpr ⟨hnI, hd⟩)⟩
  · obtain ⟨j, hj, hd⟩ := square_divisor_index n X (by omega) (by omega) hsn
    exact mem_biUnion.mpr ⟨j, hj, mem_union_left _ (mem_filter.mpr ⟨hnI, by simpa using hd⟩)⟩

theorem bad_card_bound (X : ℕ) :
    ((bad X).card : ℝ) ≤ (35 / 36 : ℝ) * ((X + 1 : ℕ) : ℝ) := by
  let F := fun j ↦ divisorStarts X (modulus j) 0 ∪ divisorStarts X (modulus j) 1
  have hc : (bad X).card ≤ ∑ j ∈ range ((X + 1) + 1), (F j).card :=
    (card_le_card (bad_cover X)).trans (card_biUnion_le)
  have hterm : ∀ j : ℕ, ((F j).card : ℝ) ≤
      2 * ((X + 1 : ℕ) : ℝ) * (1 / (modulus j : ℝ)) := by
    intro j
    have hp : (0 : ℝ) < modulus j := by exact_mod_cast modulus_positive j
    have h0 := divisor_count X (modulus j) 0 (modulus_positive j)
    have h1 := divisor_count X (modulus j) 1 (modulus_positive j)
    have h01 : ((X + 0 : ℕ) : ℝ) / (modulus j : ℝ) ≤
        ((X + 1 : ℕ) : ℝ) / (modulus j : ℝ) := by
      apply div_le_div_of_nonneg_right _ hp.le
      exact_mod_cast (show X + 0 ≤ X + 1 by omega)
    have hu : ((F j).card : ℝ) ≤
        ((divisorStarts X (modulus j) 0).card : ℝ) +
        ((divisorStarts X (modulus j) 1).card : ℝ) := by
      exact_mod_cast card_union_le (divisorStarts X (modulus j) 0)
        (divisorStarts X (modulus j) 1)
    calc
      _ ≤ 2 * (((X + 1 : ℕ) : ℝ) / (modulus j : ℝ)) := by linarith
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ range ((X + 1) + 1), ((F j).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ j ∈ range ((X + 1) + 1),
        2 * ((X + 1 : ℕ) : ℝ) * (1 / (modulus j : ℝ)) :=
      sum_le_sum (fun j _ ↦ hterm j)
    _ = 2 * ((X + 1 : ℕ) : ℝ) *
        (∑ j ∈ range ((X + 1) + 1), 1 / (modulus j : ℝ)) := by rw [mul_sum]
    _ ≤ 2 * ((X + 1 : ℕ) : ℝ) * (35 / 72 : ℝ) :=
      mul_le_mul_of_nonneg_left (modulus_reciprocal_sum (X + 1)) (by positivity)
    _ = _ := by ring

theorem good_bad_card (X : ℕ) : (good X).card + (bad X).card = X := by
  simpa only [good, bad, Nat.card_Icc, Nat.add_sub_cancel] using
    (card_filter_add_card_filter_not (s := Icc 1 X)
      (fun n ↦ Squarefree n ∧ Squarefree (n + 1)))

theorem good_card_lower (X : ℕ) :
    ((X : ℝ) - 35) / 36 ≤ ((good X).card : ℝ) := by
  have hc : ((good X).card : ℝ) + ((bad X).card : ℝ) = (X : ℝ) := by
    exact_mod_cast good_bad_card X
  have hb := bad_card_bound X
  push_cast at hb
  linarith

theorem arbitrarily_large (M : ℕ) :
    ∃ N : ℕ, max 1 M < N ∧ Squarefree N ∧ Squarefree (N + 1) := by
  let m := max 1 M
  let X := 36 * (m + 2) + 35
  have hl := good_card_lower X
  have hcount : m < (good X).card := by
    dsimp [X] at hl
    push_cast at hl
    exact_mod_cast (show (m : ℝ) < ((good X).card : ℝ) by linarith)
  have hex : ∃ N ∈ good X, m < N := by
    by_contra! h
    have hsub : good X ⊆ Icc 1 m := by
      intro n hn
      exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hn).1).1, h n hn⟩
    have hc : (good X).card ≤ m := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
    omega
  obtain ⟨N, hN, hlarge⟩ := hex
  exact ⟨N, hlarge, (mem_filter.mp hN).2⟩

end PaperP1.AdjacentSquarefreeCount
