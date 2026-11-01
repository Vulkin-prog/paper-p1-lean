module

public import PaperP1.Arithmetic.SeveralAnchorConfigurations
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-! # An actual tuple relation with a large selected kernel has a marked anchor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeKernelTuples

open Finset PaperP1.Arithmetic PaperP1.LargeOddKernel

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def atAnchor (m N B : ℕ) (T : ℝ) (a : Fin (m + 1)) : Finset (Fin (m + 1) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (m + 1) ↦ Finset.Ico N (2 * N)).filter fun g ↦
    ∃ i : Fin B, ∃ w : Fin (m + 1) → Fin B → F₂,
      w a i ≠ 0 ∧ T < (largeOddKernel B (g a - 1 + i.val) : ℝ) ∧
        (∑ k, ∑ j, w k j • parityVec (g k - 1 + j.val)) = 0

def tuples (m N B : ℕ) (T : ℝ) : Finset (Fin (m + 1) → ℕ) :=
  univ.biUnion (atAnchor m N B T)

def encode {m : ℕ} (a : Fin (m + 1)) (g : Fin (m + 1) → ℕ) : ℕ × (Fin m → ℕ) :=
  (g a, fun k ↦ g (a.succAbove k))

theorem encode_injective {m : ℕ} (a : Fin (m + 1)) : Function.Injective (encode a) := by
  intro g h heq
  funext k
  rcases Fin.eq_self_or_eq_succAbove a k with rfl | ⟨j, rfl⟩
  · exact congrArg Prod.fst heq
  · exact congrFun (congrArg Prod.snd heq) j

theorem encode_mem {m N B : ℕ} (T : ℝ) (a : Fin (m + 1))
    {g : Fin (m + 1) → ℕ} (hg : g ∈ atAnchor m N B T a) :
    encode a g ∈ PaperP1.SeveralAnchorConfigurations.configurations (ι := Fin m) N B T := by
  obtain ⟨hblock, i, w, hwi, hT, hrel⟩ := mem_filter.mp hg
  have hblock' := Fintype.mem_piFinset.mp hblock
  have hothers : (fun k : Fin m ↦ g (a.succAbove k)) ∈
      Fintype.piFinset (fun _ : Fin m ↦ Finset.Ico N (2 * N)) :=
    Fintype.mem_piFinset.mpr (fun k ↦ hblock' (a.succAbove k))
  refine mem_filter.mpr ⟨mem_product.mpr ⟨hblock' a, hothers⟩, i, hT,
    (w a), (fun k ↦ w (a.succAbove k)), hwi, ?_⟩
  rw [Fin.sum_univ_succAbove _ a] at hrel
  exact hrel

theorem anchor_card_le {m N B : ℕ} (T : ℝ) (a : Fin (m + 1)) :
    (atAnchor m N B T a).card ≤
      (PaperP1.SeveralAnchorConfigurations.configurations (ι := Fin m) N B T).card := by
  apply card_le_card_of_injOn (encode a)
  · intro g hg
    exact encode_mem T a hg
  · exact (encode_injective a).injOn

theorem tuples_card (m N B : ℕ) (T : ℝ) :
    (tuples m N B T).card ≤ (m + 1) *
      (PaperP1.SeveralAnchorConfigurations.configurations (ι := Fin m) N B T).card := by
  calc
    _ ≤ ∑ a : Fin (m + 1), (atAnchor m N B T a).card := card_biUnion_le
    _ ≤ ∑ _a : Fin (m + 1),
        (PaperP1.SeveralAnchorConfigurations.configurations (ι := Fin m) N B T).card :=
      sum_le_sum (fun a _ ↦ anchor_card_le T a)
    _ = _ := by simp

theorem mem_tuples {m N B : ℕ} (T : ℝ) (g : Fin (m + 1) → ℕ) :
    g ∈ tuples m N B T ↔
      (∀ k, g k ∈ Finset.Ico N (2 * N)) ∧
        ∃ w : Fin (m + 1) → Fin B → F₂,
          (∑ k, ∑ j, w k j • parityVec (g k - 1 + j.val)) = 0 ∧
            ∃ a : Fin (m + 1), ∃ i : Fin B, w a i ≠ 0 ∧
              T < (largeOddKernel B (g a - 1 + i.val) : ℝ) := by
  constructor
  · intro hg
    obtain ⟨a, _, ha⟩ := mem_biUnion.mp hg
    obtain ⟨hblock, i, w, hwi, hT, hrel⟩ := mem_filter.mp ha
    exact ⟨Fintype.mem_piFinset.mp hblock, w, hrel, a, i, hwi, hT⟩
  · rintro ⟨hblock, w, hrel, a, i, hwi, hT⟩
    exact mem_biUnion.mpr ⟨a, mem_univ _, mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr hblock, i, w, hwi, hT, hrel⟩⟩

end PaperP1.LargeKernelTuples
