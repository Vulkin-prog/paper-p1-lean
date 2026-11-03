module

public import PaperP1.Asymptotics.TwoTargetMixedClassData
public import PaperP1.Asymptotics.CoefficientUnivariateCount
public import PaperP1.Arithmetic.TwoTargetLabelSelection

/-! # Actual pure target classes give two disjoint univariate equations with the same source coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPureClassData

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetClassSourceCover PaperP1.SmallPrimeBudget PaperP1.DisjointRecoverySubspace
  PaperP1.CoefficientSplitRadicalPatterns PaperP1.SplitRadicalPointHeight PaperP1.TwoTargetMixedClassData

local instance pureClassDataPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem univariate_square {s y z L d : ℕ} (x : Fin s → ℕ) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (M : Submodule F₂ (code (starts x y z) L)) (α : Module.Dual F₂ M) (j : Fin 2)
    (hempty : targetOffsets (LabelClassPartition.part (label (starts x y z) M) α) j.rev = ∅)
    (hsquare : IsSquare ((d : ℤ) * targetProduct (starts x y z) M α)) :
    IsSquare ((d : ℤ) * integerProduct
      (targetOffsets (LabelClassPartition.part (label (starts x y z) M) α) j)
      (if j = 0 then (y : ℤ) else z)) := by
  rw [target_product_eq x hy hz M α] at hsquare
  fin_cases j
  · change targetOffsets _ 1 = ∅ at hempty
    change IsSquare ((d : ℤ) * integerProduct
      (targetOffsets (LabelClassPartition.part (label (starts x y z) M) α) 0) (y : ℤ))
    rw [hempty] at hsquare
    simpa only [integerProduct, prod_empty, mul_one] using hsquare
  · change targetOffsets _ 0 = ∅ at hempty
    change IsSquare ((d : ℤ) * integerProduct
      (targetOffsets (LabelClassPartition.part (label (starts x y z) M) α) 1) (z : ℤ))
    rw [hempty] at hsquare
    simpa only [integerProduct, prod_empty, one_mul] using hsquare

theorem exists_system {s y z L t : ℕ} (x : Fin s → ℕ) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (M : Submodule F₂ (code (starts x y z) L)) (Q : Finset ℕ) (j : Fin 2)
    (α : Fin 2 → Module.Dual F₂ M) (hinj : Function.Injective α)
    (hpure : ∀ i : Fin 2,
      (targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j).Nonempty ∧
        targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j.rev = ∅)
    (hsize : ∀ i, (LabelClassPartition.part (label (starts x y z) M) (α i)).card ≤ t - 1)
    (hcoeff : ∀ i, squarefreeKernel (targetProduct (starts x y z) M (α i)) ∈ Q)
    (hsquare : ∀ i, IsSquare (((squarefreeKernel (targetProduct (starts x y z) M (α i)) : ℕ) : ℤ) *
      targetProduct (starts x y z) M (α i))) :
    CoefficientUnivariateCount.HasSystem L (t - 1) Q (if j = 0 then y else z) := by
  classical
  let D := fun i ↦ LabelClassPartition.part (label (starts x y z) M) (α i)
  let q : Pattern 2 := ((fun i ↦ targetOffsets (D i) j, fun _ ↦ ∅),
    fun i ↦ squarefreeKernel (targetProduct (starts x y z) M (α i)))
  have hpool : q ∈ pool 2 L (t - 1) Q := by
    apply (mem_pool _ _ _ _ _).mpr
    refine ⟨?_, ?_, hcoeff⟩
    · intro i
      refine ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (offset_bound (D i) j), ?_⟩
      change (targetOffsets (D i) j).card ≤ t - 1
      rw [target_offsets_card, target_indices_card]
      exact (card_le_card inter_subset_left).trans (hsize i)
    · intro i
      exact ⟨empty_subset _, by simp only [q, card_empty]; omega⟩
  have hdisj : Disjoint (targetOffsets (D 0) j) (targetOffsets (D 1) j) :=
    class_offsets_disjoint _ M (fun h ↦ (by decide : (0 : Fin 2) ≠ 1) (hinj h)) j
  refine ⟨q, hpool, ⟨hdisj, (hpure 0).1, (hpure 1).1⟩, ?_⟩
  intro i
  have h := univariate_square x hy hz M (α i) j (hpure i).2 (hsquare i)
  by_cases hj : j = 0 <;> simpa only [q, coefficient, hj, ite_true, ite_false] using h

theorem uniform_systems (s t : ℕ) (ht : 2 ≤ t) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
        ((boundedCoefficients x L H t N).card : ℝ) ≤ (N : ℝ) ^ ε ∧
        ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
        ∀ M : Submodule F₂ (code (starts x y z) L),
          NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) M (s + 1) t →
        ∀ j : Fin 2, ∀ α : Fin 2 → Module.Dual F₂ M, Function.Injective α → (∀ i, α i ≠ 0) →
          (∀ i : Fin 2,
            (targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j).Nonempty ∧
              targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j.rev = ∅) →
          CoefficientUnivariateCount.HasSystem L (t - 1) (boundedCoefficients x L H t N)
            (if j = 0 then y else z) := by
  obtain ⟨N₀, hN₀, hu⟩ := TwoTargetIntrinsicEnumeration.uniform_enumeration s t ht D C ε hD hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband hHlo hHhi x hx
  obtain ⟨hcard, hclass⟩ := hu N hN L H hband hHlo hHhi x hx
  refine ⟨(show ((boundedCoefficients x L H t N).card : ℝ) ≤
    (TwoTargetCoefficientEnumeration.coefficients x L H t).card by exact_mod_cast bounded_card_le x L H t N).trans hcard, ?_⟩
  intro y z hy hz M hno j α hinj hnonzero hpure
  have hcoeff (i) := hclass y z hy hz M hno (α i) (hnonzero i)
  have hsize (i) := coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code (starts x y z) L)) M
    (s + 1) t (by omega) hno (α i) (hnonzero i)
  have hypos : 1 ≤ y := by have h := (mem_Ico.mp hy).1; omega
  have hzpos : 1 ≤ z := by have h := (mem_Ico.mp hz).1; omega
  exact exists_system x hypos hzpos M _ j α hinj hpure hsize
    (fun i ↦ mem_filter.mpr ⟨(hcoeff i).1, (hcoeff i).2.1, (hcoeff i).2.2.1⟩)
    (fun i ↦ (hcoeff i).2.2.2)

end PaperP1.TwoTargetPureClassData
