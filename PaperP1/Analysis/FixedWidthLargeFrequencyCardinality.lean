module

public import PaperP1.Analysis.NarrowPrimeBands
public import PaperP1.Analysis.FixedOrderPrimeMoment


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedWidthLargeFrequencyCardinality
open Finset Filter PaperP1
open scoped Classical

theorem index_card_bound (H N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ N) (hLog : 1 ≤ Real.log (N : ℝ)) :
    ((NarrowPrimeBands.indices H P).card : ℝ) ≤ ((H : ℝ)+1)*Real.log (N : ℝ) := by
  have hc := NarrowPrimeBands.indices_card_bound H P (N : ℝ) (fun p hp ↦ ⟨(hP p hp).1.one_le,(hP p hp).2⟩)
  have hcR : ((NarrowPrimeBands.indices H P).card : ℝ) ≤ (⌊(H : ℝ)*Real.log (N : ℝ)⌋₊ : ℝ)+1 := by exact_mod_cast hc
  have hFloor := Nat.floor_le (show 0 ≤ (H : ℝ)*Real.log (N : ℝ) by positivity)
  nlinarith only [hcR,hFloor,hLog]

theorem all_blocks_bound {ι : Type*} (H N : ℕ) (hH : 4 ≤ H) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ N)
    (hLog : 1 ≤ Real.log (N : ℝ))
    (hFactor : ((H : ℝ)+1)*FixedOrderPrimeMoment.constant H ≤ Real.log (N : ℝ))
    (hGeometry : ∀ j ∈ NarrowPrimeBands.indices H P,
      (H : ℝ) ≤ NarrowPrimeBands.anchor H j ∧ (N : ℝ) ≤ (NarrowPrimeBands.anchor H j)^H)
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (R : Finset ι) (τ : ι → ℝ) (T : ℝ) (hT : 0 < T) (hTN : T ≤ N)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (hLarge : ∀ r ∈ R, ∃ j ∈ NarrowPrimeBands.indices H P,
      1/(Real.log (N : ℝ))^100 ≤ ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r)‖) :
    (R.card : ℝ) ≤ (Real.log (N : ℝ))^(200*H+2) := by
  let z := Real.log (N : ℝ)
  let J := NarrowPrimeBands.indices H P
  let S (j : ℕ) := R.filter (fun r ↦ 1/z^100 ≤ ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r)‖)
  have hz : 0 < z := by dsimp only [z]; linarith only [hLog]
  have hCover : R ⊆ J.biUnion S := by
    intro r hr
    obtain ⟨j,hj,hBig⟩ := hLarge r hr
    exact mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨hr,hBig⟩⟩
  have hCard : (R.card : ℝ) ≤ ∑ j ∈ J, ((S j).card : ℝ) := by
    have hh := (card_le_card hCover).trans card_biUnion_le
    exact_mod_cast hh
  have hEach : ∀ j ∈ J, ((S j).card : ℝ) ≤ FixedOrderPrimeMoment.constant H*z^(200*H) := by
    intro j hj
    exact FixedOrderPrimeMoment.threshold_bound H j hH (hGeometry j hj).1 P (fun p hp ↦ (hP p hp).1)
      f hf (S j) τ T z hT hz (hTN.trans (hGeometry j hj).2)
      (fun r hr ↦ htau r (mem_filter.mp hr).1)
      (fun r hr s hs hne ↦ hsep r (mem_filter.mp hr).1 s (mem_filter.mp hs).1 hne)
      (fun r hr ↦ (mem_filter.mp hr).2)
  have hJ : (J.card : ℝ) ≤ ((H : ℝ)+1)*z := index_card_bound H N P hP hLog
  have hC := FixedOrderPrimeMoment.constant_pos H
  calc
    _ ≤ ∑ j ∈ J, ((S j).card : ℝ) := hCard
    _ ≤ ∑ _j ∈ J, FixedOrderPrimeMoment.constant H*z^(200*H) := sum_le_sum hEach
    _ = (J.card : ℝ)*(FixedOrderPrimeMoment.constant H*z^(200*H)) := by simp
    _ ≤ (((H : ℝ)+1)*z)*(FixedOrderPrimeMoment.constant H*z^(200*H)) :=
      mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = (((H : ℝ)+1)*FixedOrderPrimeMoment.constant H)*z^(200*H+1) := by rw [pow_succ]; ring
    _ ≤ z*z^(200*H+1) := mul_le_mul_of_nonneg_right hFactor (pow_nonneg hz.le _)
    _ = _ := by rw [show 200*H+2=(200*H+1)+1 by omega,pow_succ]; ring
end PaperP1.FixedWidthLargeFrequencyCardinality
