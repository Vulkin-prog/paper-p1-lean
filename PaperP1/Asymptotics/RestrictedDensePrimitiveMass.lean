module

public import PaperP1.Asymptotics.DensePrimitiveRankMass
public import PaperP1.Asymptotics.DensePrimitiveNominalMass

/-! # The full restricted-source dense primitive bound has no geometric input

The stronger full dense population bound handles nonnegative source exponents.
For a negative source exponent its finite prescribed source pool is empty.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RestrictedDensePrimitiveMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (s : ℕ) (hs : 1 ≤ s) (C η σ ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ S F : Finset (Finset ℕ),
      (∀ E ∈ S, E ⊆ dyadicBlock N ∧ E.card = s) →
      (S.card : ℝ) ≤ (N : ℝ) ^ σ →
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = s + 2 ∧
        ConnectedWindowFamilies.Primitive L I ∧ η * L ≤ (runRelativeNullity L I : ℝ)) →
      (∀ I ∈ F, ∃ E ∈ S, E ⊆ I) →
      PrimitiveWindowMass.mass F L ≤ (N : ℝ) ^ (-1 - s + σ + ε) := by
  classical
  obtain ⟨NM, hNM, hm⟩ := DensePrimitiveRankMass.uniform_rank_mass (s + 2) (by omega) C η ε hη hε
  refine ⟨NM, hNM, ?_⟩
  intro N hN L hband S F _hS hScard hF hcover
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  by_cases hσ : 0 ≤ σ
  · have hh := hm N hN L hband F (by
      intro I hI
      obtain ⟨hdyadic, hcard, hprim, hdense⟩ := hF I hI
      exact ⟨hcard, hdyadic, hprim, hdense⟩)
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hn1
    push_cast
    linarith only [hσ]
  · have hpow : (N : ℝ) ^ σ < 1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (show 1 < N by omega)) (lt_of_not_ge hσ)
    have hFempty : F = ∅ := by
      by_contra hne
      obtain ⟨I, hI⟩ := nonempty_iff_ne_empty.mpr hne
      obtain ⟨E, hE, _⟩ := hcover I hI
      have hSpos : (1 : ℝ) ≤ S.card := by
        have hh : 0 < S.card := card_pos.mpr ⟨E, hE⟩
        exact_mod_cast (show 1 ≤ S.card by omega)
      linarith only [hSpos, hScard, hpow]
    rw [hFempty, PrimitiveWindowMass.mass, sum_empty]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _


theorem uniform_nominal_bound (s : ℕ) (hs : 1 ≤ s) (C η σ ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ S F : Finset (Finset ℕ),
      (∀ E ∈ S, E ⊆ dyadicBlock N ∧ E.card = s) →
      (S.card : ℝ) ≤ (N : ℝ) ^ σ →
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = s + 2 ∧
        ConnectedWindowFamilies.Primitive L I ∧ η * L ≤ (runRelativeNullity L I : ℝ)) →
      (∀ I ∈ F, ∃ E ∈ S, E ⊆ I) →
      PrimitiveNominalMass.mass F L ≤ (N : ℝ) ^ (-1 - s + σ + ε) := by
  classical
  obtain ⟨NM, hNM, hm⟩ := DensePrimitiveNominalMass.uniform_mass (s + 2) (by omega) C η ε hη hε
  refine ⟨NM, hNM, ?_⟩
  intro N hN L hband S F _hS hScard hF hcover
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  by_cases hσ : 0 ≤ σ
  · have hh := hm N hN L hband F (by
      intro I hI
      obtain ⟨hdyadic, hcard, hprim, hdense⟩ := hF I hI
      exact ⟨hcard, hdyadic, hprim, hdense⟩)
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hn1
    push_cast
    linarith only [hσ]
  · have hpow : (N : ℝ) ^ σ < 1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (show 1 < N by omega)) (lt_of_not_ge hσ)
    have hFempty : F = ∅ := by
      by_contra hne
      obtain ⟨I, hI⟩ := nonempty_iff_ne_empty.mpr hne
      obtain ⟨E, hE, _⟩ := hcover I hI
      have hSpos : (1 : ℝ) ≤ S.card := by
        have hh : 0 < S.card := card_pos.mpr ⟨E, hE⟩
        exact_mod_cast (show 1 ≤ S.card by omega)
      linarith only [hSpos, hScard, hpow]
    rw [hFempty, PrimitiveNominalMass.mass, sum_empty]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _


end PaperP1.RestrictedDensePrimitiveMass
