module

public import PaperP1.Combinatorics.DisjointSubsetIncidence
public import PaperP1.Algebra.SubsetPowerSums

/-! # Cardinality convolution of exact uncentered and centered finite data -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.CenteredCardConvolution

open Finset PaperP1.SubsetPowerSums

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

theorem convolution (G : Finset ι) (p : ι → R) (q c : Finset ι → R)
    (hq : ∀ I ⊆ G, q I = ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x) (r : ℕ) :
    (∑ I ∈ G.powersetCard r, q I) =
      ∑ s ∈ range (r + 1), ∑ D ∈ G.powersetCard s, c D * elementary p (G \ D) (r - s) := by
  classical
  calc
    _ = ∑ I ∈ G.powersetCard r, ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x :=
      sum_congr rfl (fun I hI ↦ hq I (mem_powersetCard.mp hI).1)
    _ = ∑ I ∈ G.powersetCard r, ∑ s ∈ range (r + 1),
        ∑ D ∈ I.powersetCard s, c D * ∏ x ∈ I \ D, p x := by
      apply sum_congr rfl
      intro I hI
      have hc := (mem_powersetCard.mp hI).2
      have hs (D : Finset ι) (hD : D ∈ I.powerset) : D.card ∈ range (r + 1) :=
        mem_range.mpr (by have h := card_le_card (mem_powerset.mp hD); omega)
      rw [← sum_fiberwise_of_maps_to (s := I.powerset) (t := range (r + 1)) (g := Finset.card) hs]
      apply sum_congr rfl
      intro s _
      congr 1
      ext D
      simp only [mem_filter, mem_powerset, mem_powersetCard]
    _ = ∑ s ∈ range (r + 1), ∑ I ∈ G.powersetCard r,
        ∑ D ∈ I.powersetCard s, c D * ∏ x ∈ I \ D, p x := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro s hs
      have hsr : s + (r - s) = r := by have h := mem_range.mp hs; omega
      have hsplit := DisjointSubsetIncidence.split_sum G s (r - s)
        (fun D E ↦ c D * ∏ x ∈ E, p x)
      rw [hsr] at hsplit
      rw [hsplit]
      apply sum_congr rfl
      intro D _
      rw [← mul_sum]
      rfl

theorem zero_layer (G : Finset ι) (p : ι → R) (c : Finset ι → R) (h0 : c ∅ = 1) (r : ℕ) :
    (∑ D ∈ G.powersetCard 0, c D * elementary p (G \ D) r) = elementary p G r := by
  simp only [powersetCard_zero, sum_singleton, h0, sdiff_empty, one_mul]

theorem one_layer (G : Finset ι) (p : ι → R) (c : Finset ι → R)
    (h1 : ∀ x, c {x} = 0) (r : ℕ) :
    (∑ D ∈ G.powersetCard 1, c D * elementary p (G \ D) r) = 0 := by
  rw [SubsetSums.one]
  simp only [h1, zero_mul, sum_const_zero]

theorem two (G : Finset ι) (p : ι → R) (q c : Finset ι → R)
    (hq : ∀ I ⊆ G, q I = ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x)
    (h0 : c ∅ = 1) (h1 : ∀ x, c {x} = 0) :
    (∑ I ∈ G.powersetCard 2, q I) = elementary p G 2 + ∑ I ∈ G.powersetCard 2, c I := by
  have h := convolution G p q c hq 2
  simp only [sum_range_succ, sum_range_zero, Nat.reduceSub, zero_add] at h
  simpa only [zero_layer G p c h0, one_layer G p c h1, elementary_zero, mul_one, add_zero] using h

theorem three (G : Finset ι) (p : ι → R) (q c : Finset ι → R)
    (hq : ∀ I ⊆ G, q I = ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x)
    (h0 : c ∅ = 1) (h1 : ∀ x, c {x} = 0) :
    (∑ I ∈ G.powersetCard 3, q I) = elementary p G 3 +
      (∑ I ∈ G.powersetCard 2, c I * ∑ x ∈ G \ I, p x) + ∑ I ∈ G.powersetCard 3, c I := by
  have h := convolution G p q c hq 3
  simp only [sum_range_succ, sum_range_zero, Nat.reduceSub, zero_add] at h
  simpa only [zero_layer G p c h0, one_layer G p c h1, elementary_zero, elementary_one, mul_one, add_zero] using h

theorem four (G : Finset ι) (p : ι → R) (q c : Finset ι → R)
    (hq : ∀ I ⊆ G, q I = ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x)
    (h0 : c ∅ = 1) (h1 : ∀ x, c {x} = 0) :
    (∑ I ∈ G.powersetCard 4, q I) = elementary p G 4 +
      (∑ I ∈ G.powersetCard 2, c I * elementary p (G \ I) 2) +
      (∑ I ∈ G.powersetCard 3, c I * ∑ x ∈ G \ I, p x) + ∑ I ∈ G.powersetCard 4, c I := by
  have h := convolution G p q c hq 4
  simp only [sum_range_succ, sum_range_zero, Nat.reduceSub, zero_add] at h
  simpa only [zero_layer G p c h0, one_layer G p c h1, elementary_zero, elementary_one, mul_one, add_zero] using h

end PaperP1.CenteredCardConvolution
