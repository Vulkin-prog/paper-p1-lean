module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SeparatedPositiveBudget
open Finset
open scoped Classical

theorem floor_injective {ι : Type*} (S : Finset ι) (δ : ι → ℝ)
    (hδ : ∀ i ∈ S, 0 ≤ δ i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |δ i-δ j|) :
    Set.InjOn (fun i ↦ ⌊δ i⌋₊) (↑S) := by
  intro i hi j hj he
  by_contra hne
  have hs := hsep i hi j hj hne
  have hi1 := Nat.floor_le (hδ i hi)
  have hj1 := Nat.floor_le (hδ j hj)
  have hi2 := Nat.lt_floor_add_one (δ i)
  have hj2 := Nat.lt_floor_add_one (δ j)
  have heR : (⌊δ i⌋₊ : ℝ)=(⌊δ j⌋₊ : ℝ) := by exact_mod_cast he
  have hsmall : |δ i-δ j| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
  linarith

theorem floor_image_subset {ι : Type*} (S : Finset ι) (δ : ι → ℝ) (A : ℝ)
    (hδ : ∀ i ∈ S, 1 ≤ δ i ∧ δ i ≤ A) :
    S.image (fun i ↦ ⌊δ i⌋₊) ⊆ Icc 1 ⌊A⌋₊ := by
  intro k hk
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
  refine mem_Icc.mpr ⟨?_,Nat.floor_mono (hδ i hi).2⟩
  exact (Nat.le_floor_iff (by linarith [(hδ i hi).1] : 0 ≤ δ i)).mpr (by simpa only [Nat.cast_one] using (hδ i hi).1)

theorem card_bound {ι : Type*} (S : Finset ι) (δ : ι → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hδ : ∀ i ∈ S, 1 ≤ δ i ∧ δ i ≤ A)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |δ i-δ j|) :
    (S.card : ℝ) ≤ A := by
  have hi := floor_injective S δ (fun i hi ↦ by linarith [(hδ i hi).1]) hsep
  have hc := card_le_card (floor_image_subset S δ A hδ)
  rw [card_image_of_injOn hi] at hc
  have hnat : S.card ≤ ⌊A⌋₊ := by simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hc
  exact (by exact_mod_cast hnat : (S.card : ℝ) ≤ (⌊A⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))

theorem reciprocal_finite_bound {ι : Type*} (S : Finset ι) (δ : ι → ℝ) (A : ℝ)
    (hδ : ∀ i ∈ S, 1 ≤ δ i ∧ δ i ≤ A)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |δ i-δ j|) :
    (∑ i ∈ S, 1/δ i) ≤ ∑ k ∈ Icc 1 ⌊A⌋₊, 1/(k : ℝ) := by
  have hi := floor_injective S δ (fun i hi ↦ by linarith [(hδ i hi).1]) hsep
  calc
    _ ≤ ∑ i ∈ S, 1/(⌊δ i⌋₊ : ℝ) := by
      apply sum_le_sum
      intro i hi
      have hfloor : 1 ≤ ⌊δ i⌋₊ :=
        (Nat.le_floor_iff (by linarith [(hδ i hi).1] : 0 ≤ δ i)).mpr (by simpa only [Nat.cast_one] using (hδ i hi).1)
      have hpos : (0 : ℝ) < ⌊δ i⌋₊ := by exact_mod_cast (show 0 < ⌊δ i⌋₊ by omega)
      exact one_div_le_one_div_of_le hpos (Nat.floor_le (by linarith [(hδ i hi).1]))
    _ = ∑ k ∈ S.image (fun i ↦ ⌊δ i⌋₊), 1/(k : ℝ) := by
      rw [sum_image (fun i hi' j hj he ↦ hi hi' hj he)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (floor_image_subset S δ A hδ)
      (fun k _hk _hnot ↦ by positivity)

theorem reciprocal_bound {ι : Type*} (S : Finset ι) (δ : ι → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hδ : ∀ i ∈ S, 1 ≤ δ i ∧ δ i ≤ A)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |δ i-δ j|) :
    (∑ i ∈ S, 1/δ i) ≤ 1+Real.log A := by
  have hAnn : 0 ≤ A := by linarith
  have hfloor : 1 ≤ ⌊A⌋₊ := (Nat.le_floor_iff hAnn).mpr (by simpa only [Nat.cast_one] using hA)
  have hpos : (0 : ℝ) < ⌊A⌋₊ := by exact_mod_cast (show 0 < ⌊A⌋₊ by omega)
  calc
    _ ≤ ∑ k ∈ Icc 1 ⌊A⌋₊, 1/(k : ℝ) := reciprocal_finite_bound S δ A hδ hsep
    _ ≤ 1+Real.log (⌊A⌋₊ : ℝ) := by
      simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using harmonic_le_one_add_log ⌊A⌋₊
    _ ≤ _ := add_le_add le_rfl (Real.log_le_log hpos (Nat.floor_le hAnn))
end PaperP1.SeparatedPositiveBudget
