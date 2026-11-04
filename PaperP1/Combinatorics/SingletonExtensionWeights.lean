module

public import PaperP1.Combinatorics.DistinguishedPairWeights

/-! # Exact union fibers for an actually distinguished fresh singleton extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SingletonExtensionWeights

open Finset

variable {ι : Type*} [DecidableEq ι]

def join (p : Finset ι × ι) : Finset ι := p.1 ∪ {p.2}

theorem fiber_card (P : Finset (Finset ι × ι)) (I : Finset ι)
    (hfresh : ∀ p ∈ P, p.2 ∉ p.1) : (P.filter fun p ↦ join p = I).card ≤ I.card := by
  classical
  let PI := P.filter fun p ↦ join p = I
  have herase (p : Finset ι × ι) (hp : p ∈ PI) : (join p).erase p.2 = p.1 := by
    rw [join, erase_union_distrib, erase_singleton, union_empty,
      erase_eq_of_notMem (hfresh p (mem_filter.mp hp).1)]
  have hinj : Set.InjOn Prod.snd (PI : Set (Finset ι × ι)) := by
    intro p hp q hq heq
    apply Prod.ext _ heq
    calc
      p.1 = I.erase p.2 := by rw [← (mem_filter.mp hp).2, herase p hp]
      _ = I.erase q.2 := by rw [heq]
      _ = q.1 := by rw [← (mem_filter.mp hq).2, herase q hq]
  have hsub : PI.image Prod.snd ⊆ I := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
    rw [← (mem_filter.mp hp).2]
    simp [join]
  exact (card_image_of_injOn hinj).symm.trans_le (card_le_card hsub)

theorem weighted_bound (P : Finset (Finset ι × ι)) (F : Finset (Finset ι)) (r : ℕ)
    (hfresh : ∀ p ∈ P, p.2 ∉ p.1) (hmap : ∀ p ∈ P, join p ∈ F)
    (hcard : ∀ I ∈ F, I.card = r) (w : Finset ι → ℝ) (hw : ∀ I, 0 ≤ w I) :
    (∑ p ∈ P, w (join p)) ≤ (r : ℝ) * ∑ I ∈ F, w I := by
  have hsplit := sum_fiberwise_of_maps_to (s := P) (t := F) (g := join) hmap (fun p ↦ w (join p))
  rw [← hsplit, mul_sum]
  apply sum_le_sum
  intro I hI
  calc
    _ = ((P.filter fun p ↦ join p = I).card : ℝ) * w I := by
      calc
        _ = ∑ _p ∈ P.filter (fun p ↦ join p = I), w I :=
          sum_congr rfl (fun p hp ↦ congrArg w (mem_filter.mp hp).2)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (fiber_card P I hfresh).trans_eq (hcard I hI)) (hw I)

end PaperP1.SingletonExtensionWeights
