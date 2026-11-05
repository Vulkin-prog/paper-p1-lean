module

public import PaperP1.Asymptotics.PrimitiveTripleMass
public import PaperP1.Asymptotics.PrimitiveGeneralMass

/-! # Unconditional rank-weight mass at every fixed primitive order at least three -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPrimitiveMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.PrimitiveWindowMass

theorem uniform_triples (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I) →
      mass F L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := PrimitiveTripleMass.uniform_rank_mass C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hF
  exact (h N hN L hband F hF).trans
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only []))

theorem uniform_fixed (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I) →
      mass F L ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  by_cases hthree : r = 3
  · subst r
    exact uniform_triples C ε hε
  · obtain ⟨NM, hm⟩ := PrimitiveGeneralMass.uniform_submass r (by omega) C ε hε
    refine ⟨3 + NM, by omega, ?_⟩
    intro N hN L hband F hF
    have hsub : F ⊆ primitiveFamilies (dyadicBlock N) L r := by
      intro I hI
      obtain ⟨hIG, hcard, hprim⟩ := hF I hI
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hIG, hcard⟩, hprim⟩
    apply (hm N (by omega) L (dyadicBlock N) F hband Subset.rfl hsub).trans
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    have hrR : (4 : ℝ) ≤ r := by exact_mod_cast (show 4 ≤ r by omega)
    linarith only [hrR]

end PaperP1.FixedPrimitiveMass
