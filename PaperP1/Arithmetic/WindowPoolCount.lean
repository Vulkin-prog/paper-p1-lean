module

public import PaperP1.Arithmetic.ConditionalWindowRank
public import PaperP1.Arithmetic.SmoothSquarefreeCount

/-! # The total incidence budget of the values supported by an old prime pool -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowPoolCount

open Finset PaperP1.Arithmetic PaperP1.ConditionalWindowRank PaperP1.SmoothSquarefreeCount
  PaperP1.DefectivePredicate

def poolValues (R : Finset ℕ) (B X : ℕ) : Finset ℕ := naturalValues (primePool R B) X

theorem card_fixed_offset_le {R G : Finset ℕ} {B X : ℕ}
    (hlo : ∀ x ∈ G, 2 ≤ x) (hhi : ∀ x ∈ G, x + (B - 1) ≤ X) (i : Fin B) :
    (G.filter fun x ↦ oddPrimeSupport (x - 1 + i.val) ⊆ primePool R B).card ≤ (poolValues R B X).card := by
  apply card_le_card_of_injOn (fun x ↦ x - 1 + i.val)
  · intro x hx
    obtain ⟨hxG, hsupp⟩ := mem_filter.mp hx
    apply mem_naturalValues.mpr
    dsimp
    have hxlo := hlo x hxG
    have hxhi := hhi x hxG
    have hi := i.isLt
    exact ⟨by omega, by omega, hsupp⟩
  · intro x hx y hy hxy
    change x - 1 + i.val = y - 1 + i.val at hxy
    have hxlo := hlo x (mem_filter.mp hx).1
    have hylo := hlo y (mem_filter.mp hy).1
    omega

theorem sum_supportedIndices_le {R G : Finset ℕ} {B X : ℕ}
    (hlo : ∀ x ∈ G, 2 ≤ x) (hhi : ∀ x ∈ G, x + (B - 1) ≤ X) :
    (∑ x ∈ G, (supportedIndices R (x - 1) B).card) ≤ B * (poolValues R B X).card := by
  calc
    _ = ∑ x ∈ G, ∑ i : Fin B,
        if oddPrimeSupport (x - 1 + i.val) ⊆ primePool R B then (1 : ℕ) else 0 := by
      simp only [supportedIndices, card_eq_sum_ones, sum_filter]
    _ = ∑ i : Fin B, ∑ x ∈ G,
        if oddPrimeSupport (x - 1 + i.val) ⊆ primePool R B then (1 : ℕ) else 0 := sum_comm
    _ = ∑ i : Fin B, (G.filter fun x ↦ oddPrimeSupport (x - 1 + i.val) ⊆ primePool R B).card := by
      simp only [card_eq_sum_ones, sum_filter]
    _ ≤ ∑ _i : Fin B, (poolValues R B X).card := sum_le_sum fun i _ ↦ card_fixed_offset_le hlo hhi i
    _ = _ := by simp

theorem sum_supportedIndices_dyadic {R : Finset ℕ} {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    (∑ x ∈ PaperP1.Model.dyadicBlock N, (supportedIndices R (x - 1) (L + 1)).card) ≤
      (L + 1) * (poolValues R (L + 1) (3 * N)).card := by
  apply sum_supportedIndices_le
  · intro x hx
    have h := (mem_Ico.mp hx).1
    omega
  · intro x hx
    have h := (mem_Ico.mp hx).2
    omega

end PaperP1.WindowPoolCount
