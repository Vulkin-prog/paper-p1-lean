module

public import PaperP1.Arithmetic.TernaryTopProducts

/-! # Increasing the prime cutoff can only decrease actual group products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryCutoffMonotonicity

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryTopProducts

theorem primes_mono (u : Fin 3 → ℕ) {h H : ℕ} (hle : h ≤ H) : primes H u ⊆ primes h u := by
  intro p hp
  obtain ⟨hpH, hpvalues⟩ := (mem_primes H u p).mp hp
  exact (mem_primes h u p).mpr ⟨hle.trans_lt hpH, hpvalues⟩

theorem group_le (u : Fin 3 → ℕ) {h H : ℕ} (hle : h ≤ H) : group H u ≤ group h u := by
  apply Nat.le_of_dvd (group_pos h u)
  exact prod_dvd_prod_of_subset (primes H u) (primes h u) id (primes_mono u hle)

theorem active_mono (U : Fin 3 → Finset ℕ) {h H : ℕ} (hle : h ≤ H) : active U H ⊆ active U h := by
  intro u hu
  obtain ⟨hum, hug⟩ := (mem_active U H u).mp hu
  exact (mem_active U h u).mpr ⟨hum, hug.trans_le (group_le u hle)⟩

theorem top_product_le (U : Fin 3 → Finset ℕ) (k : ℕ) {h H : ℕ} (hle : h ≤ H) :
    topProduct U H k ≤ topProduct U h k := by
  apply Finset.sup_le
  intro S hS
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hS
  calc
    _ ≤ ∏ u ∈ S, group h u := prod_le_prod (fun u _ ↦ group_le u hle)
    _ ≤ _ := selected_le_top U h k S (hsub.trans (active_mono U hle)) hcard

end PaperP1.TernaryCutoffMonotonicity
