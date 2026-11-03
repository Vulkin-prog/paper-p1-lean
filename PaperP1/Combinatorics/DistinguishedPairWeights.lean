module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Basic.Real.Basic

/-! # An actually distinguished disjoint source pair costs at most one factor two per original vertex -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DistinguishedPairWeights

open Finset

variable {ι : Type*} [DecidableEq ι]

def join (p : Finset ι × Finset ι) : Finset ι := p.1 ∪ p.2

theorem fiber_card (P : Finset (Finset ι × Finset ι)) (I : Finset ι)
    (hdis : ∀ p ∈ P, Disjoint p.1 p.2) :
    (P.filter fun p ↦ join p = I).card ≤ 2 ^ I.card := by
  classical
  let PI := P.filter fun p ↦ join p = I
  have hinj : Set.InjOn Prod.fst (PI : Set (Finset ι × Finset ι)) := by
    intro p hp q hq heq
    apply Prod.ext heq
    have hpI := (mem_filter.mp hp).2
    have hqI := (mem_filter.mp hq).2
    calc
      p.2 = join p \ p.1 := (union_sdiff_cancel_left (hdis p (mem_filter.mp hp).1)).symm
      _ = I \ p.1 := by rw [hpI]
      _ = I \ q.1 := by rw [heq]
      _ = q.2 := by rw [← hqI]; exact union_sdiff_cancel_left (hdis q (mem_filter.mp hq).1)
  have hsub : PI.image Prod.fst ⊆ I.powerset := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := mem_image.mp he
    apply mem_powerset.mpr
    have hpI := (mem_filter.mp hp).2
    rw [← hpI]
    exact subset_union_left
  calc
    _ = (PI.image Prod.fst).card := (card_image_of_injOn hinj).symm
    _ ≤ I.powerset.card := card_le_card hsub
    _ = _ := card_powerset I

theorem weighted_bound (P : Finset (Finset ι × Finset ι)) (u : ℝ) (hu : 0 ≤ u)
    (w : Finset ι → ℝ) (hw : ∀ I, 0 ≤ w I) (hdis : ∀ p ∈ P, Disjoint p.1 p.2) :
    (∑ p ∈ P, u ^ (join p).card * w (join p)) ≤
      ∑ I ∈ P.image join, (2 * u) ^ I.card * w I := by
  classical
  have hsplit := sum_fiberwise_of_maps_to (s := P) (t := P.image join) (g := join)
    (fun p hp ↦ mem_image.mpr ⟨p, hp, rfl⟩) (fun p ↦ u ^ (join p).card * w (join p))
  rw [← hsplit]
  apply sum_le_sum
  intro I _hI
  calc
    _ = ((P.filter fun p ↦ join p = I).card : ℝ) * (u ^ I.card * w I) := by
      calc
        _ = ∑ _p ∈ P.filter (fun p ↦ join p = I), u ^ I.card * w I :=
          sum_congr rfl (fun p hp ↦ by rw [(mem_filter.mp hp).2])
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ I.card : ℝ) * (u ^ I.card * w I) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast fiber_card P I hdis) (mul_nonneg (pow_nonneg hu _) (hw I))
    _ = _ := by rw [mul_pow]; ring

end PaperP1.DistinguishedPairWeights
