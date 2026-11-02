module

public import PaperP1.Arithmetic.FiniteEvenSquareClasses
public import PaperP1.Algebra.FinitePiExtension

/-! # Full even-selection rank is weaker than private raw values and is invariant under dilation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenIndependentValues

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def Independent (S : Finset ℕ) : Prop := Function.Injective (EvenImage.evenMap (K := F₂) (data S))

theorem of_private (S : Finset ℕ) (hS : Private S) : Independent S :=
  EvenImage.evenMap_injective _ (combination_injective S hS)

theorem Independent.mono {S T : Finset ℕ} (hT : Independent T) (hST : S ⊆ T) : Independent S := by
  let e : S ↪ T := ⟨fun n ↦ ⟨n.val, hST n.property⟩, by
    intro x y hh
    apply Subtype.ext
    exact congrArg (fun n : T ↦ (n : ℕ)) hh⟩
  exact FinitePiExtension.even_injective_of_embedding e (data S) (data T) (fun _ ↦ rfl) hT

theorem rank_iff (S : Finset ℕ) : Independent S ↔ Module.finrank F₂ (space S) = S.card - 1 := by
  constructor
  · intro hh
    rw [space, EvenImage.image, LinearMap.finrank_range_of_inj hh, EvenSupportRank.kernel_sum_finrank,
      Fintype.card_coe]
  · intro hh
    have hdim := (EvenImage.evenMap (K := F₂) (data S)).finrank_range_add_finrank_ker
    rw [EvenSupportRank.kernel_sum_finrank, Fintype.card_coe] at hdim
    change Module.finrank F₂ (space S) + Module.finrank F₂ (LinearMap.ker (EvenImage.evenMap (K := F₂) (data S))) = S.card - 1 at hdim
    have hker : Module.finrank F₂ (LinearMap.ker (EvenImage.evenMap (K := F₂) (data S))) = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

theorem finrank_space {S : Finset ℕ} (hS : Independent S) : Module.finrank F₂ (space S) = S.card - 1 :=
  (rank_iff S).mp hS

theorem dilate_iff {c : ℕ} (hc : 0 < c) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    Independent (dilate c S) ↔ Independent S := by
  rw [rank_iff, rank_iff, FiniteEvenSquareClasses.space_dilate S hc hS]
  rw [dilate, card_image_of_injective _ (mul_right_injective₀ hc.ne')]

theorem pair_iff (a b : ℕ) (hab : a ≠ b) :
    Independent {a, b} ↔ parityVec a ≠ parityVec b := by
  have hspace : space {a, b} = Submodule.span F₂ {parityVec a - parityVec b} := by
    rw [space_eq_span _ b (by simp)]
    simp only [coe_insert, coe_singleton, Set.image_insert_eq, Set.image_singleton, sub_self]
    rw [Set.pair_comm, Submodule.span_insert_zero]
  rw [rank_iff, card_pair hab, hspace]
  constructor
  · intro hh heq
    rw [heq, sub_self, Submodule.span_zero_singleton, finrank_bot] at hh
    norm_num at hh
  · intro hh
    exact finrank_span_singleton (sub_ne_zero.mpr hh)

theorem independent_square_pair : Independent {1, 2} := by
  apply (pair_iff 1 2 (by decide)).2
  intro heq
  have hh := congrArg (fun v : ℕ →₀ F₂ ↦ v 2) heq
  norm_num [Nat.prime_two.factorization] at hh

theorem square_pair_not_private : ¬Private {1, 2} := by
  intro hh
  obtain ⟨p, hp, _⟩ := hh 1 (by simp)
  simp at hp

end PaperP1.EvenIndependentValues
