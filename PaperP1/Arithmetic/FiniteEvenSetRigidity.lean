module

public import PaperP1.Algebra.EvenImageDataRigidity
public import PaperP1.Arithmetic.FiniteEvenSquareClasses
public import PaperP1.Arithmetic.TwoPointSquareClasses
public import PaperP1.Algebra.PlaneNormalRigidity

/-! # Proportional-pair rigidity for arbitrary finite sets of arithmetic values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteEvenSetRigidity

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses PaperP1.TwoPointSquareClasses

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem pair_class_mem {S : Finset ℕ} {n m : ℕ} (hn : n ∈ S) (hm : m ∈ S) :
    parityVec n + parityVec m ∈ space S := by
  have h := EvenImage.difference_mem (K := F₂) (data S) (⟨n, hn⟩ : S) (⟨m, hm⟩ : S)
  simpa only [space, data, sub_eq_add_neg, binary_neg_eq_self] using h

theorem pair_class_ne_zero {S : Finset ℕ} (hinj : Function.Injective (data S))
    {n m : ℕ} (hn : n ∈ S) (hm : m ∈ S) (hnm : n ≠ m) : parityVec n + parityVec m ≠ 0 := by
  intro hz
  have heq : parityVec n = parityVec m :=
    (eq_neg_of_add_eq_zero_left hz).trans (binary_neg_eq_self _)
  have heqSub : (⟨n, hn⟩ : S) = ⟨m, hm⟩ := hinj heq
  exact hnm (congrArg Subtype.val heqSub)

theorem data_injective_of_evenMap (S : Finset ℕ)
    (hinj : Function.Injective (EvenImage.evenMap (K := F₂) (data S))) : Function.Injective (data S) :=
  EvenImageDataRigidity.data_injective (data S) hinj

theorem projection_equal {S T : Finset ℕ} (hinj : Function.Injective (data S))
    (hdirect : Disjoint (space S) (space T)) {n₁ n₂ m₁ m₂ : ℕ}
    (hn₁ : n₁ ∈ S) (hn₂ : n₂ ∈ S) (hm₁ : m₁ ∈ T) (hm₂ : m₂ ∈ T)
    (hn₁pos : 0 < n₁) (hn₂pos : 0 < n₂) (hm₁pos : 0 < m₁) (hm₂pos : 0 < m₂)
    (hcross : n₁ * m₂ = n₂ * m₁) : n₁ = n₂ := by
  by_contra hne
  have heq := parity_pair_eq_of_cross_product hn₁pos.ne' hn₂pos.ne' hm₁pos.ne' hm₂pos.ne' hcross
  have hmemS := pair_class_mem hn₁ hn₂
  have hmemT := pair_class_mem hm₁ hm₂
  rw [← heq] at hmemT
  have hzero := (Submodule.disjoint_def.mp hdirect) _ hmemS hmemT
  exact pair_class_ne_zero hinj hn₁ hn₂ hne hzero

theorem projection_rigid (U : Fin 3 → Finset ℕ) (V : Fin 3 → Fin 3 → ℕ)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    (hmem : ∀ p i, V p i ∈ U i) (hpos : ∀ p i, 0 < V p i) :
    PlaneNormalRigidity.ProjectionRigid (fun p i ↦ (V p i : ℤ)) := by
  intro i j hij p q hcross
  change (V p i : ℤ) * V q j = (V q i : ℤ) * V p j at hcross
  have hNat : V p i * V q j = V q i * V p j := by exact_mod_cast hcross
  exact congrArg (fun n : ℕ ↦ (n : ℤ)) (projection_equal (hinj i) (hdirect hij)
    (hmem p i) (hmem q i) (hmem p j) (hmem q j)
    (hpos p i) (hpos q i) (hpos p j) (hpos q j) hNat)

end PaperP1.FiniteEvenSetRigidity
