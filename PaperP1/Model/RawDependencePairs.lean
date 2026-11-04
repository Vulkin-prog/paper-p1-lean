module

public import PaperP1.Model.RawValueIndependence

/-! # Actual exceptional pairs for the joint raw-value matrix -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawDependencePairs

open Finset PaperP1.Arithmetic PaperP1.Model

local instance rawDependencePairsDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def badPairs (M N B : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦
    ¬Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin B ↦ p.1 - 1 + i.val) (fun i : Fin B ↦ p.2 - 1 + i.val))

theorem subset_hosts {M N B : ℕ} (hN : 2 ≤ N) (hM : 2 * N + B ≤ M) :
    badPairs M N B ⊆ PaperP1.RawTwoWindowHosts.hosts N B := by
  intro p hp
  obtain ⟨hp, hn⟩ := mem_filter.mp hp
  obtain ⟨hx, hy⟩ := mem_product.mp hp
  have hxx := mem_Ico.mp hx
  have hyy := mem_Ico.mp hy
  refine mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, ?_⟩
  exact PaperP1.RawValueIndependence.joint_non_surjective_related
    (fun i ↦ by omega) (fun i ↦ by omega) (fun i ↦ by omega) (fun i ↦ by omega) hn

theorem card_le_hosts {M N B : ℕ} (hN : 2 ≤ N) (hM : 2 * N + B ≤ M) :
    (badPairs M N B).card ≤ (PaperP1.RawTwoWindowHosts.hosts N B).card :=
  card_le_card (subset_hosts hN hM)

theorem joint_surjective_restrict {M x y B S T : ℕ} (hS : S ≤ B) (hT : T ≤ B)
    (h : Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin B ↦ x - 1 + i.val) (fun i : Fin B ↦ y - 1 + i.val))) :
    Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin S ↦ x - 1 + i.val) (fun i : Fin T ↦ y - 1 + i.val)) := by
  intro b
  let u : Fin B → F₂ := fun i ↦ if hi : i.val < S then b.1 ⟨i.val, hi⟩ else 0
  let v : Fin B → F₂ := fun i ↦ if hi : i.val < T then b.2 ⟨i.val, hi⟩ else 0
  obtain ⟨ω, hω⟩ := h (u, v)
  refine ⟨ω, Prod.ext ?_ ?_⟩
  · funext i
    have hi := congrFun (congrArg Prod.fst hω) (Fin.castLE hS i)
    change valueBit ω (x - 1 + i.val) = u (Fin.castLE hS i) at hi
    exact hi.trans (by simp [u])
  · funext i
    have hi := congrFun (congrArg Prod.snd hω) (Fin.castLE hT i)
    change valueBit ω (y - 1 + i.val) = v (Fin.castLE hT i) at hi
    exact hi.trans (by simp [v])

def rectangularBadPairs (M N S T : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦
    ¬Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin S ↦ p.1 - 1 + i.val) (fun i : Fin T ↦ p.2 - 1 + i.val))

theorem rectangular_subset {M N B S T : ℕ} (hS : S ≤ B) (hT : T ≤ B) :
    rectangularBadPairs M N S T ⊆ badPairs M N B := by
  intro p hp
  obtain ⟨hp, hn⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp, fun h ↦ hn (joint_surjective_restrict hS hT h)⟩

theorem rectangular_card_le_hosts {M N B S T : ℕ} (hN : 2 ≤ N)
    (hM : 2 * N + B ≤ M) (hS : S ≤ B) (hT : T ≤ B) :
    (rectangularBadPairs M N S T).card ≤ (PaperP1.RawTwoWindowHosts.hosts N B).card :=
  (card_le_card (rectangular_subset hS hT)).trans (card_le_hosts hN hM)

end PaperP1.RawDependencePairs
