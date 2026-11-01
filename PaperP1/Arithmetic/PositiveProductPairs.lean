module

public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Floor.Ring

/-! # Uniform counting of actual positive pairs with a bounded product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveProductPairs

open Finset

theorem positive_values_count (S : Finset ℕ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hS : ∀ m ∈ S, 0 < m ∧ (m : ℝ) ≤ Q) : (S.card : ℝ) ≤ Q := by
  have hsub : S ⊆ Icc 1 ⌊Q⌋₊ := by
    intro m hm
    exact mem_Icc.mpr ⟨(hS m hm).1, Nat.le_floor (hS m hm).2⟩
  calc
    _ ≤ ((Icc 1 ⌊Q⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = (⌊Q⌋₊ : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ Q := Nat.floor_le hQ

theorem product_fibre_count (R : Finset (ℕ × ℕ)) (m : ℕ)
    (hR : ∀ z ∈ R, 0 < z.1 ∧ 0 < z.2 ∧ z.1 * z.2 = m) :
    R.card ≤ m.divisors.card := by
  have hinj : Set.InjOn (fun z : ℕ × ℕ ↦ z.1) R := by
    intro z hz w hw heq
    have hzdata := hR z hz
    have hwdata := hR w hw
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left hzdata.1
    simpa only [heq] using hzdata.2.2.trans hwdata.2.2.symm
  rw [← card_image_of_injOn hinj]
  apply card_le_card
  intro u hu
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
  have hd := hR z hz
  exact Nat.mem_divisors.mpr ⟨⟨z.2, hd.2.2.symm⟩,
    by rw [← hd.2.2]; exact (Nat.mul_pos hd.1 hd.2.1).ne'⟩

theorem uniform_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Q : ℝ, 0 ≤ Q → ∀ R : Finset (ℕ × ℕ),
      (∀ z ∈ R, 0 < z.1 ∧ 0 < z.2 ∧ z.1 * z.2 ≤ N ^ K ∧ (z.1 * z.2 : ℕ) ≤ Q) →
      (R.card : ℝ) ≤ Q * (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := PaperP1.DivisorSubpolynomial.card_divisors_le_rpow_eventually K ε hε
  refine ⟨N₀, ?_⟩
  intro N hN Q hQ R hR
  let product : ℕ × ℕ → ℕ := fun z ↦ z.1 * z.2
  have himage : ((R.image product).card : ℝ) ≤ Q := by
    apply positive_values_count _ Q hQ
    intro m hm
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hm
    exact ⟨Nat.mul_pos (hR z hz).1 (hR z hz).2.1, (hR z hz).2.2.2⟩
  have hfib : ∀ m ∈ R.image product,
      ((R.filter fun z ↦ product z = m).card : ℝ) ≤ (N : ℝ) ^ ε := by
    intro m hm
    have hcard := product_fibre_count (R.filter fun z ↦ product z = m) m (by
      intro z hz
      have hd := mem_filter.mp hz
      exact ⟨(hR z hd.1).1, (hR z hd.1).2.1, hd.2⟩)
    have hmheight : m ≤ N ^ K := by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hm
      exact (hR z hz).2.2.1
    exact (show ((R.filter fun z ↦ product z = m).card : ℝ) ≤ m.divisors.card by
      exact_mod_cast hcard).trans (hN₀ N hN m hmheight)
  have hcover : ∀ z ∈ R, ∃ m ∈ R.image product, z ∈ R.filter fun z ↦ product z = m := by
    intro z hz
    exact ⟨product z, mem_image_of_mem _ hz, mem_filter.mpr ⟨hz, rfl⟩⟩
  exact (PaperP1.FiniteCoverCount.cardinal_le R (R.image product)
    (fun m ↦ R.filter fun z ↦ product z = m) ((N : ℝ) ^ ε) hcover hfib).trans
    (mul_le_mul_of_nonneg_right himage (Real.rpow_nonneg (Nat.cast_nonneg N) ε))

end PaperP1.PositiveProductPairs
