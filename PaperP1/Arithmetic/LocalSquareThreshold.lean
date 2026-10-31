module

public import PaperP1.Arithmetic.SplitProductBound

/-! # Companion T9.1: a local square threshold

The exact degree-uniform algebraic split-product bound gives the stronger
threshold (64B)^m, hence (B+1)^(5m) for B≥2. The original exponent 12m
is an immediate corollary. Offsets form an actual finite subset of integers.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalSquareThreshold

open Finset

theorem split_product_finset_bound {B x : ℕ} (hB : 1 ≤ B)
    (I : Finset ℤ) (hIpos : 0 < I.card) (hIeven : Even I.card)
    (hI : ∀ a ∈ I, |a| ≤ (B : ℤ)) (hx : 2 * B ≤ x)
    (y : ℤ) (hprod : (∏ a ∈ I, ((x : ℤ) + a)) = y ^ 2) :
    x ≤ (64 * B) ^ I.card := by
  classical
  obtain ⟨k, hk⟩ := hIeven
  have hcard : I.card = 2 * k := by omega
  have hkpos : 1 ≤ k := by omega
  let e : Fin (2 * k) ≃ I := (finCongr hcard.symm).trans I.equivFin.symm
  let γ : Fin (2 * k) → ℤ := fun i ↦ (e i).val
  have hγ : ∀ i, |γ i| ≤ (B : ℤ) := fun i ↦ hI _ (e i).property
  have hγinj : Function.Injective γ := by
    intro i j heq
    exact e.injective (Subtype.ext heq)
  have hprod' : (∏ i, ((x : ℤ) + γ i)) = y ^ 2 := by
    calc
      _ = ∏ a : I, ((x : ℤ) + a.val) := e.prod_comp (fun a : I ↦ (x : ℤ) + a.val)
      _ = ∏ a ∈ I, ((x : ℤ) + a) := prod_coe_sort _ _
      _ = _ := hprod
  have hbound := SplitProductBound.uniform_split_product hkpos hB hx γ hγ hγinj y hprod'
  simpa only [hcard] using hbound

theorem local_square_threshold_sharp {B x : ℕ} (hB : 1 ≤ B)
    (I : Finset ℤ) (hIpos : 0 < I.card) (hIeven : Even I.card)
    (hI : ∀ a ∈ I, |a| ≤ (B : ℤ)) (hx : (64 * B) ^ I.card < x) :
    ¬IsSquare (∏ a ∈ I, ((x : ℤ) + a)) := by
  intro hsquare
  obtain ⟨y, hy⟩ := hsquare
  have hpow : 64 * B ≤ (64 * B) ^ I.card := Nat.le_self_pow (by omega) _
  have hbase : 2 * B ≤ x := by omega
  have hprod : (∏ a ∈ I, ((x : ℤ) + a)) = y ^ 2 := by simpa only [pow_two] using hy
  exact (not_le_of_gt hx) (split_product_finset_bound hB I hIpos hIeven hI hbase y hprod)

theorem sixtyfour_mul_le_fifth_power {B : ℕ} (hB : 2 ≤ B) :
    64 * B ≤ (B + 1) ^ 5 := by
  have hfour : 64 ≤ (B + 1) ^ 4 := (by norm_num : 64 ≤ 3 ^ 4).trans
    (Nat.pow_le_pow_left (by omega : 3 ≤ B + 1) 4)
  calc
    _ ≤ (B + 1) ^ 4 * (B + 1) := Nat.mul_le_mul hfour (by omega)
    _ = _ := (pow_succ _ _).symm

theorem local_square_threshold_power_five {B x : ℕ} (hB : 2 ≤ B)
    (I : Finset ℤ) (hIpos : 0 < I.card) (hIeven : Even I.card)
    (hI : ∀ a ∈ I, |a| ≤ (B : ℤ)) (hx : (B + 1) ^ (5 * I.card) < x) :
    ¬IsSquare (∏ a ∈ I, ((x : ℤ) + a)) := by
  apply local_square_threshold_sharp (by omega) I hIpos hIeven hI
  apply lt_of_le_of_lt _ hx
  calc
    _ ≤ ((B + 1) ^ 5) ^ I.card := Nat.pow_le_pow_left (sixtyfour_mul_le_fifth_power hB) _
    _ = _ := (pow_mul _ _ _).symm

/-- The literal companion T9.1 bound, with the original exponent 12m. -/
theorem companion_T9_1 {B x : ℕ} (hB : 2 ≤ B)
    (I : Finset ℤ) (hIpos : 0 < I.card) (hIeven : Even I.card)
    (hI : I ⊆ Icc (-(B : ℤ)) B) (hx : (B + 1) ^ (12 * I.card) < x) :
    ¬IsSquare (∏ a ∈ I, ((x : ℤ) + a)) := by
  apply local_square_threshold_power_five hB I hIpos hIeven
    (fun a ha ↦ abs_le.mpr (mem_Icc.mp (hI ha)))
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by omega : 0 < B + 1)
    (by omega : 5 * I.card ≤ 12 * I.card)) hx

end PaperP1.LocalSquareThreshold
