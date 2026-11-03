module

public import PaperP1.Asymptotics.TwoTargetIntrinsicEnumeration
public import PaperP1.Asymptotics.CoefficientNonalignedHostCount
public import PaperP1.Arithmetic.TwoTargetClassOffsets

/-! # Actual mixed label classes supply all equations of a common bounded-coefficient pattern -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetMixedClassData

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetClassSourceCover PaperP1.SmallPrimeBudget PaperP1.DisjointRecoverySubspace
  PaperP1.CoefficientSplitRadicalPatterns PaperP1.SplitRadicalPointHeight

local instance mixedClassDataPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def boundedCoefficients {s : ℕ} (x : Fin s → ℕ) (L H t N : ℕ) : Finset ℕ :=
  (TwoTargetCoefficientEnumeration.coefficients x L H t).filter fun d ↦ 0 < d ∧ d ≤ N ^ (2 * (t - 1))

theorem bounded_card_le {s : ℕ} (x : Fin s → ℕ) (L H t N : ℕ) :
    (boundedCoefficients x L H t N).card ≤ (TwoTargetCoefficientEnumeration.coefficients x L H t).card :=
  card_filter_le _ _

theorem bounded_coefficient {s : ℕ} (x : Fin s → ℕ) (L H t N d : ℕ)
    (hd : d ∈ boundedCoefficients x L H t N) : 0 < d ∧ d ≤ N ^ (2 * (t - 1)) :=
  (mem_filter.mp hd).2

theorem exists_pattern {s y z L t k : ℕ} (x : Fin s → ℕ) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (M : Submodule F₂ (code (starts x y z) L)) (Q : Finset ℕ)
    (α : Fin k → Module.Dual F₂ M) (hinj : Function.Injective α)
    (hboth : ∀ i : Fin k, ∀ j : Fin 2,
      (targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j).Nonempty)
    (hsize : ∀ i, (LabelClassPartition.part (label (starts x y z) M) (α i)).card ≤ t - 1)
    (hcoeff : ∀ i, squarefreeKernel (targetProduct (starts x y z) M (α i)) ∈ Q)
    (hsquare : ∀ i, IsSquare (((squarefreeKernel (targetProduct (starts x y z) M (α i)) : ℕ) : ℤ) *
      targetProduct (starts x y z) M (α i))) :
    ∃ q ∈ pool k L (t - 1) Q, CoefficientNonalignedHostCount.Valid (t - 1) q ∧
      ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) (y : ℤ) *
        integerProduct (q.1.2 i) (z : ℤ) := by
  classical
  let D := fun i ↦ LabelClassPartition.part (label (starts x y z) M) (α i)
  let q : Pattern k := ((fun i ↦ targetOffsets (D i) 0, fun i ↦ targetOffsets (D i) 1),
    fun i ↦ squarefreeKernel (targetProduct (starts x y z) M (α i)))
  have htotal (i) : (targetOffsets (D i) 0).card + (targetOffsets (D i) 1).card ≤ t - 1 :=
    (total_card_le (D i)).trans (hsize i)
  have hpool : q ∈ pool k L (t - 1) Q := by
    apply (mem_pool _ _ _ _ _).mpr
    refine ⟨?_, ?_, hcoeff⟩
    · intro i
      exact ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (offset_bound (D i) 0),
        (Nat.le_add_right _ _).trans (htotal i)⟩
    · intro i
      exact ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (offset_bound (D i) 1),
        (Nat.le_add_left _ _).trans (htotal i)⟩
  have hdisj (j : Fin 2) : Pairwise fun i n : Fin k ↦ Disjoint (targetOffsets (D i) j) (targetOffsets (D n) j) :=
    fun _ _ hne ↦ class_offsets_disjoint _ M (fun h ↦ hne (hinj h)) j
  refine ⟨q, hpool, ⟨hdisj 0, hdisj 1, fun i ↦ hboth i 0, fun i ↦ hboth i 1, htotal⟩, ?_⟩
  choose w hw using (fun i ↦ square_roots x hy hz M (α i) (hsquare i))
  exact ⟨w, hw⟩

theorem uniform_patterns (s t : ℕ) (ht : 2 ≤ t) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
        ((boundedCoefficients x L H t N).card : ℝ) ≤ (N : ℝ) ^ ε ∧
        ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
        ∀ M : Submodule F₂ (code (starts x y z) L),
          NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) M (s + 1) t →
        ∀ k : ℕ, ∀ α : Fin k → Module.Dual F₂ M, Function.Injective α → (∀ i, α i ≠ 0) →
          (∀ i : Fin k, ∀ j : Fin 2,
            (targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j).Nonempty) →
          ∃ q ∈ pool k L (t - 1) (boundedCoefficients x L H t N),
            CoefficientNonalignedHostCount.Valid (t - 1) q ∧
            ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) (y : ℤ) *
              integerProduct (q.1.2 i) (z : ℤ) := by
  obtain ⟨N₀, hN₀, hu⟩ := TwoTargetIntrinsicEnumeration.uniform_enumeration s t ht D C ε hD hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband hHlo hHhi x hx
  obtain ⟨hcard, hclass⟩ := hu N hN L H hband hHlo hHhi x hx
  refine ⟨(show ((boundedCoefficients x L H t N).card : ℝ) ≤
    (TwoTargetCoefficientEnumeration.coefficients x L H t).card by exact_mod_cast bounded_card_le x L H t N).trans hcard, ?_⟩
  intro y z hy hz M hno k α hinj hnonzero hboth
  have hcoeff (i) := hclass y z hy hz M hno (α i) (hnonzero i)
  have hsize (i) := coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code (starts x y z) L)) M
    (s + 1) t (by omega) hno (α i) (hnonzero i)
  have hypos : 1 ≤ y := by have h := (mem_Ico.mp hy).1; omega
  have hzpos : 1 ≤ z := by have h := (mem_Ico.mp hz).1; omega
  exact exists_pattern x hypos hzpos M _ α hinj hboth hsize
    (fun i ↦ mem_filter.mpr ⟨(hcoeff i).1, (hcoeff i).2.1, (hcoeff i).2.2.1⟩)
    (fun i ↦ (hcoeff i).2.2.2)

end PaperP1.TwoTargetMixedClassData
