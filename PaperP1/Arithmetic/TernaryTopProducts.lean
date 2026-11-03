module

public import PaperP1.Arithmetic.TernaryPrimeGroups
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-! # The actual maximum product of k distinct active ternary groups -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryTopProducts

open Finset PaperP1.TernaryPrimeGroups

def topProduct (U : Fin 3 → Finset ℕ) (H k : ℕ) : ℕ :=
  ((active U H).powersetCard k).sup fun S ↦ ∏ u ∈ S, group H u

theorem zero_of_fewer (U : Fin 3 → Finset ℕ) (H k : ℕ) (hk : (active U H).card < k) :
    topProduct U H k = 0 := by
  have he : (active U H).powersetCard k = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hS
    have hle := card_le_card hsub
    omega
  simp only [topProduct, he, sup_empty, bot_eq_zero]

theorem selected_le_top (U : Fin 3 → Finset ℕ) (H k : ℕ) (S : Finset (Fin 3 → ℕ))
    (hsub : S ⊆ active U H) (hcard : S.card = k) :
    (∏ u ∈ S, group H u) ≤ topProduct U H k :=
  le_sup (f := fun S ↦ ∏ u ∈ S, group H u) (mem_powersetCard.mpr ⟨hsub, hcard⟩)

theorem attained (U : Fin 3 → Finset ℕ) (H k : ℕ) (hp : 0 < topProduct U H k) :
    ∃ S ⊆ active U H, S.card = k ∧ topProduct U H k = ∏ u ∈ S, group H u := by
  have hne : ((active U H).powersetCard k).Nonempty := by
    by_contra he
    have hz : topProduct U H k = 0 := by
      simp only [topProduct, not_nonempty_iff_eq_empty.mp he, sup_empty, bot_eq_zero]
    omega
  obtain ⟨S, hS, heq⟩ := exists_mem_eq_sup ((active U H).powersetCard k) hne
    (fun S ↦ ∏ u ∈ S, group H u)
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hS
  exact ⟨S, hsub, hcard, heq⟩

theorem real_gt_iff (U : Fin 3 → Finset ℕ) (H k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    T < (topProduct U H k : ℝ) ↔
      ∃ S ⊆ active U H, S.card = k ∧ T < (∏ u ∈ S, group H u : ℕ) := by
  constructor
  · intro hlarge
    have hp : 0 < topProduct U H k := by
      exact_mod_cast lt_of_le_of_lt hT hlarge
    obtain ⟨S, hsub, hcard, hprod⟩ := attained U H k hp
    exact ⟨S, hsub, hcard, by simpa only [hprod] using hlarge⟩
  · rintro ⟨S, hsub, hcard, hlarge⟩
    exact hlarge.trans_le (by exact_mod_cast selected_le_top U H k S hsub hcard)

theorem enumerate_selection (U : Fin 3 → Finset ℕ) (H k : ℕ)
    (S : Finset (Fin 3 → ℕ)) (hsub : S ⊆ active U H) (hcard : S.card = k) :
    ∃ v : Fin k → Fin 3 → ℕ, Function.Injective v ∧ (∀ j, v j ∈ active U H) ∧
      (∏ j, group H (v j)) = ∏ u ∈ S, group H u := by
  let e : Fin k ≃ S := (Finset.equivFinOfCardEq hcard).symm
  let v : Fin k → Fin 3 → ℕ := fun j ↦ (e j).val
  refine ⟨v, ?_, fun j ↦ hsub (e j).property, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · exact (e.prod_comp (fun u : S ↦ group H u.val)).trans (prod_coe_sort S _)

end PaperP1.TernaryTopProducts
