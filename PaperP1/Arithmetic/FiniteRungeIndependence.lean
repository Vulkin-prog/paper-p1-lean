module

public import PaperP1.Arithmetic.EvenIndependentValues
public import PaperP1.Arithmetic.EvenSquareSelection

/-! # Actual bounded-cardinality value sets are even-independent above the explicit Runge scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteRungeIndependence

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

local instance finiteRungePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem combination_selected (S : Finset ℕ) (w : S → F₂) :
    EvenImage.combination (data S) w = ∑ n ∈ selected S w, parityVec n.val := by
  classical
  rw [EvenImage.combination_apply, selected, sum_filter]
  apply sum_congr rfl
  intro n _
  have hbit : w n = 0 ∨ w n = 1 := by generalize w n = z; revert z; decide
  rcases hbit with hz | ho
  · simp only [hz, zero_smul, ne_eq, not_true_eq_false, ite_false]
  · simp only [ho, data, one_smul, ne_eq, one_ne_zero, not_false_eq_true, ite_true]

theorem independent_of_no_even_square (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (hno : ∀ A : Finset ℕ, A ⊆ S → A.Nonempty → Even A.card → ¬ ∃ q : ℕ, A.prod id = q ^ 2) :
    EvenIndependentValues.Independent S := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro w hw
  by_contra hw0
  let A := (selected S w.val).image (fun n : S ↦ n.val)
  have hAS : A ⊆ S := by
    intro n hn
    obtain ⟨m, _hm, rfl⟩ := mem_image.mp hn
    exact m.property
  have hcard : A.card = (selected S w.val).card := card_image_of_injective _ Subtype.val_injective
  have hne : A.Nonempty := by
    by_contra hn
    have hempty : selected S w.val = ∅ := by
      apply card_eq_zero.mp
      rw [← hcard, not_nonempty_iff_eq_empty.mp hn, card_empty]
    apply hw0
    apply Subtype.ext
    funext n
    by_contra hn0
    have hnmem : n ∈ selected S w.val := mem_filter.mpr ⟨mem_univ _, hn0⟩
    rw [hempty] at hnmem
    exact notMem_empty _ hnmem
  have heven : Even A.card := by
    rw [hcard]
    apply (zero_sum_iff_even_selected S w.val).mp
    simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using w.property
  have hsum : ∑ n ∈ A, parityVec n = 0 := by
    rw [show A = (selected S w.val).image (fun n : S ↦ n.val) from rfl,
      sum_image Subtype.val_injective.injOn, ← combination_selected]
    exact hw
  have hsquare := (sum_parityVec_eq_zero_iff_prod_eq_sq A id (fun n hn ↦ (hS n (hAS hn)).ne')).mp hsum
  exact hno A hAS hne heven hsquare

theorem independent_of_growth {S : Finset ℕ} {U R t : ℕ} (hcard : S.card ≤ 2 * t)
    (hlower : ∀ n ∈ S, U ≤ n) (hupper : ∀ n ∈ S, n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * t) < U) :
    EvenIndependentValues.Independent S := by
  apply independent_of_no_even_square S (fun n hn ↦ (by have h := hlower n hn; omega))
  intro A hAS hne heven hsquare
  have hlarge := EvenSquareSelection.cardinal_gt hne heven hsquare
    (fun n hn ↦ hlower n (hAS hn)) (fun n hn ↦ hupper n (hAS hn)) hR hU hgrowth
  have hsmall := (card_le_card hAS).trans hcard
  omega

end PaperP1.FiniteRungeIndependence
