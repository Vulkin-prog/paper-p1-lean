module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Lean.Elab.Tactic.Omega

/-! # A finite maximal product gives a large certificate or small remaining groups -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TopProductSelection

open Finset

variable {κ : Type*} [DecidableEq κ]

theorem outside_le_selected (G A : Finset κ) (f : κ → ℕ) (k : ℕ)
    (hpos : ∀ a ∈ G, 0 < f a) (hA : A ∈ G.powersetCard k)
    (hmax : ∀ B ∈ G.powersetCard k, (∏ a ∈ B, f a) ≤ ∏ a ∈ A, f a)
    {b : κ} (hbG : b ∈ G) (hbA : b ∉ A) {a : κ} (ha : a ∈ A) : f b ≤ f a := by
  obtain ⟨hAG, hAcard⟩ := mem_powersetCard.mp hA
  have hbErase : b ∉ A.erase a := fun h ↦ hbA (erase_subset a A h)
  have hB : insert b (A.erase a) ∈ G.powersetCard k := by
    apply mem_powersetCard.mpr
    refine ⟨insert_subset hbG ((erase_subset a A).trans hAG), ?_⟩
    rw [card_insert_of_notMem hbErase, card_erase_of_mem ha, hAcard]
    have hcard := card_pos.mpr (show A.Nonempty from ⟨a, ha⟩)
    omega
  have hproduct := hmax _ hB
  rw [prod_insert hbErase, ← mul_prod_erase A f ha] at hproduct
  have hP : 0 < ∏ c ∈ A.erase a, f c := prod_pos (fun c hc ↦ hpos c (hAG (erase_subset a A hc)))
  by_contra hnot
  exact (Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hnot) hP).not_ge hproduct

theorem outside_power_le (G A : Finset κ) (f : κ → ℕ) (k : ℕ)
    (hpos : ∀ a ∈ G, 0 < f a) (hA : A ∈ G.powersetCard k)
    (hmax : ∀ B ∈ G.powersetCard k, (∏ a ∈ B, f a) ≤ ∏ a ∈ A, f a)
    {b : κ} (hbG : b ∈ G) (hbA : b ∉ A) : f b ^ k ≤ ∏ a ∈ A, f a := by
  have hcard := (mem_powersetCard.mp hA).2
  calc
    _ = ∏ _a ∈ A, f b := by rw [prod_const, hcard]
    _ ≤ _ := prod_le_prod (fun a ha ↦ outside_le_selected G A f k hpos hA hmax hbG hbA ha)

theorem certificate_or_small_groups (G : Finset κ) (f : κ → ℕ) (N k : ℕ)
    (hpos : ∀ a ∈ G, 0 < f a) :
    ∃ A ⊆ G, A.card ≤ k ∧
      ((A.card = k ∧ N < ∏ a ∈ A, f a) ∨ ∀ b ∈ G \ A, f b ^ k ≤ N) := by
  classical
  by_cases hk : k ≤ G.card
  · obtain ⟨B, hBG, hBcard⟩ := exists_subset_card_eq hk
    have hB : B ∈ G.powersetCard k := mem_powersetCard.mpr ⟨hBG, hBcard⟩
    obtain ⟨A, hA, hmax⟩ := exists_max_image (G.powersetCard k) (fun A ↦ ∏ a ∈ A, f a) ⟨B, hB⟩
    obtain ⟨hAG, hAcard⟩ := mem_powersetCard.mp hA
    refine ⟨A, hAG, hAcard.le, ?_⟩
    by_cases hlarge : N < ∏ a ∈ A, f a
    · exact Or.inl ⟨hAcard, hlarge⟩
    · refine Or.inr ?_
      intro b hb
      exact (outside_power_le G A f k hpos hA hmax (mem_sdiff.mp hb).1 (mem_sdiff.mp hb).2).trans
        (Nat.le_of_not_gt hlarge)
  · refine ⟨G, Subset.rfl, by omega, Or.inr ?_⟩
    simp

theorem real_root_bound {g N k : ℕ} (hk : 1 ≤ k) (hpow : g ^ k ≤ N) :
    (g : ℝ) ≤ (N : ℝ) ^ (1 / (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcast : (g : ℝ) ^ k ≤ N := by exact_mod_cast hpow
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ (g : ℝ) ^ k) hcast
    (by positivity : 0 ≤ 1 / (k : ℝ))
  have hid : ((g : ℝ) ^ k) ^ (1 / (k : ℝ)) = g := by
    rw [← Real.rpow_natCast (g : ℝ) k, ← Real.rpow_mul (Nat.cast_nonneg g)]
    have heq : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
    rw [heq, Real.rpow_one]
  rwa [hid] at hroot

end PaperP1.TopProductSelection
