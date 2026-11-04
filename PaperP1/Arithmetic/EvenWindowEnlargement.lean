module

public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # Literal monotone embeddings into a longer complete window

Effective even spaces are embedded without any private-prime or normalization
assumption. An old block centred at X is translated only in its index range;
all of its actual integer labels and parity vectors remain unchanged.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenWindowEnlargement

open Finset PaperP1.Arithmetic PaperP1.Model

theorem space_mono {S T : Finset ℕ} (hST : S ⊆ T) :
    FiniteEvenSquareClasses.space S ≤ FiniteEvenSquareClasses.space T := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    rw [FiniteEvenSquareClasses.space_eq_span S a ha,
      FiniteEvenSquareClasses.space_eq_span T a (hST ha)]
    exact Submodule.span_mono (Set.image_mono hST)
  · rw [not_nonempty_iff_eq_empty.mp hS, FiniteEvenSquareClasses.space_empty]
    exact bot_le

theorem window_mono {L H x : ℕ} (hx : 0 < x) (hLH : L ≤ H) :
    squareClassSpace x L ≤ squareClassSpace x H := by
  rw [← NormalizedWindowSets.space_values, ← NormalizedWindowSets.space_values]
  apply space_mono
  rw [NormalizedWindowSets.values_eq_interval hx, NormalizedWindowSets.values_eq_interval hx]
  intro n hn
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hn
  exact mem_Ico.mpr ⟨hlo, by omega⟩

theorem block_le_window {U : Finset ℕ} {X R : ℕ} (hRX : R < X)
    (hU : ∀ n ∈ U, X - R ≤ n ∧ n ≤ X + R) :
    FiniteEvenSquareClasses.space U ≤ squareClassSpace (X - R + 1) (2 * R) := by
  rw [← NormalizedWindowSets.space_values]
  apply space_mono
  rw [NormalizedWindowSets.values_eq_interval (by omega : 0 < X - R + 1)]
  intro n hn
  obtain ⟨hlo, hhi⟩ := hU n hn
  apply mem_Ico.mpr
  omega

end PaperP1.EvenWindowEnlargement
