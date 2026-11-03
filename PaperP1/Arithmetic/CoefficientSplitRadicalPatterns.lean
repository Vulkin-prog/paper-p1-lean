module

public import PaperP1.Arithmetic.GeneralSplitRadicalPatternPool

/-! # Bounded split-radical offset patterns with any actual finite coefficient list -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoefficientSplitRadicalPatterns

open Finset PaperP1.BoundedIntegerMotifs PaperP1.GeneralSplitRadicalPatternPool

abbrev Pattern (k : ℕ) := ((Fin k → Finset ℤ) × (Fin k → Finset ℤ)) × (Fin k → ℕ)

def pool (k L K : ℕ) (Q : Finset ℕ) : Finset (Pattern k) :=
  (leftPatterns k L K ×ˢ rightPatterns k L K) ×ˢ Fintype.piFinset (fun _ : Fin k ↦ Q)

def coefficient {k : ℕ} (p : Pattern k) (i : Fin k) : ℤ := p.2 i

theorem mem_pool (k L K : ℕ) (Q : Finset ℕ) (p : Pattern k) : p ∈ pool k L K Q ↔
    (∀ i, p.1.1 i ⊆ offsets (L + 1) ∧ (p.1.1 i).card ≤ K) ∧
    (∀ i, p.1.2 i ⊆ offsets (L + 1) ∧ (p.1.2 i).card ≤ K) ∧ (∀ i, p.2 i ∈ Q) := by
  simp only [pool, mem_product, leftPatterns, rightPatterns, Fintype.mem_piFinset,
    leftPool, BoundedSubsets.mem_sets]
  exact and_assoc

theorem card_pool (k L K : ℕ) (Q : Finset ℕ) :
    (pool k L K Q).card = (leftPatterns k L K ×ˢ rightPatterns k L K).card * Q.card ^ k := by
  rw [pool, card_product, Fintype.card_piFinset_const]

theorem coefficient_mem {k L K : ℕ} {Q : Finset ℕ} {p : Pattern k}
    (hp : p ∈ pool k L K Q) (i : Fin k) : p.2 i ∈ Q := ((mem_pool k L K Q p).mp hp).2.2 i

theorem coefficient_pos {k L K : ℕ} {Q : Finset ℕ} {p : Pattern k}
    (hQ : ∀ d ∈ Q, 0 < d) (hp : p ∈ pool k L K Q) (i : Fin k) : 0 < coefficient p i := by
  change (0 : ℤ) < (p.2 i : ℤ)
  exact_mod_cast hQ _ (coefficient_mem hp i)

theorem coefficient_height {k L K N A : ℕ} {Q : Finset ℕ} {p : Pattern k}
    (hQ : ∀ d ∈ Q, d ≤ N ^ A) (hp : p ∈ pool k L K Q) (i : Fin k) :
    (coefficient p i).natAbs ≤ N ^ A := by
  simpa only [coefficient, Int.natAbs_natCast] using hQ _ (coefficient_mem hp i)

theorem left_bound {k L K : ℕ} {Q : Finset ℕ} {p : Pattern k} (hp : p ∈ pool k L K Q)
    (i : Fin k) (z : ℤ) (hz : z ∈ p.1.1 i) : z.natAbs ≤ L + 1 :=
  (subset_offsets (L + 1) (p.1.1 i)).mp (((mem_pool k L K Q p).mp hp).1 i).1 z hz

theorem right_bound {k L K : ℕ} {Q : Finset ℕ} {p : Pattern k} (hp : p ∈ pool k L K Q)
    (i : Fin k) (z : ℤ) (hz : z ∈ p.1.2 i) : z.natAbs ≤ L + 1 :=
  (subset_offsets (L + 1) (p.1.2 i)).mp (((mem_pool k L K Q p).mp hp).2.1 i).1 z hz

end PaperP1.CoefficientSplitRadicalPatterns
