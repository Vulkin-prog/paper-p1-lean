module

public import PaperP1.Combinatorics.OrderedSubsetWeights
public import PaperP1.Combinatorics.FiniteFamilyEnumeration

/-! # Exact conversion of unordered host budgets to populations of distinct center functions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderedFunctionHosts

open Finset PaperP1.Probability PaperP1.FiniteFamilyEnumeration

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem population_card (G : Finset ℕ) (r : ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ G.powersetCard r) :
    (OrderedSubsetWeights.population G r F).card = r.factorial * F.card := by
  have hh := OrderedSubsetWeights.weighted_sum G r F hF (fun _ ↦ 1)
  simp only [sum_const, nsmul_eq_mul, mul_one] at hh
  exact_mod_cast hh

theorem card_le {r : ℕ} (S : Finset (Fin r → ℕ)) (G : Finset ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ G.powersetCard r)
    (hS : ∀ X ∈ S, Function.Injective X ∧ (∀ i, X i ∈ G) ∧ tupleSet X ∈ F) :
    S.card ≤ r.factorial * F.card := by
  let lift (X : S) : OrderedTuple G r :=
    { toFun := fun i ↦ ⟨X.val i, (hS X.val X.property).2.1 i⟩
      inj' := fun _ _ hh ↦ (hS X.val X.property).1 (congrArg Subtype.val hh) }
  have hvalues (X : S) : tupleValues (lift X) = tupleSet X.val := by
    ext x
    rw [mem_tupleValues]
    simp only [tupleSet, mem_image, mem_univ, true_and]
    rfl
  let f : S → {t : OrderedTuple G r // t ∈ OrderedSubsetWeights.population G r F} := fun X ↦
    ⟨lift X, mem_filter.mpr ⟨mem_univ _, by rw [hvalues]; exact (hS X.val X.property).2.2⟩⟩
  have hfi : Function.Injective f := by
    intro X Y hh
    apply Subtype.ext
    funext i
    have heq := congrArg (fun z : {t : OrderedTuple G r // t ∈ OrderedSubsetWeights.population G r F} ↦
      (z.val i).val) hh
    exact heq
  have hcard := Fintype.card_le_of_injective f hfi
  have hbound : S.card ≤ (OrderedSubsetWeights.population G r F).card := by
    simpa only [Fintype.card_coe] using hcard
  exact hbound.trans_eq (population_card G r F hF)

end PaperP1.OrderedFunctionHosts
