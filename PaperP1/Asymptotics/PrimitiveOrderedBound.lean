module

public import PaperP1.Model.PrimitiveOrderedMass
public import PaperP1.Asymptotics.FixedPrimitiveMass

/-! # Companion T4.3 with the stronger fixed-order exponent one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveOrderedBound

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_strong (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → PrimitiveOrderedMass.mass N L r ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NM, _hNM, hm⟩ := FixedPrimitiveMass.uniform_fixed r hr C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (r.factorial : ℝ) (-1 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NF + NG + NM, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hF : ∀ I ∈ primitiveFamilies (RegularStarts.regularStarts N L) L r,
      I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I := by
    intro I hI
    obtain ⟨hIG, hprim⟩ := mem_filter.mp hI
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
    exact ⟨hsub.trans (RegularStarts.regularStarts_subset N L), hcard, hprim⟩
  calc
    _ ≤ (r.factorial : ℝ) * PrimitiveWindowMass.mass (primitiveFamilies (RegularStarts.regularStarts N L) L r) L :=
      PrimitiveOrderedMass.finite_bound (by omega) hL
    _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (-1 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L hband _ hF) (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T4_3 (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → PrimitiveOrderedMass.mass N L r ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨N₀, hN₀, hh⟩ := uniform_strong r hr C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  exact (hh N hN L hband).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith))

end PaperP1.PrimitiveOrderedBound
