module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Int.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Counting indexed coprime composite divisors, including point multiplicities

The index set, rather than the image of the divisor function, is counted.
Thus every later use retains multiplicities of coincident offset points.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoprimeDivisorCardinality

open Finset

theorem product_dvd {ι : Type*} (S : Finset ι) (g : ι → ℕ) (n : ℤ)
    (hcop : (S : Set ι).Pairwise (fun i j ↦ (g i).Coprime (g j)))
    (hdiv : ∀ i ∈ S, (g i : ℤ) ∣ n) : (∏ i ∈ S, g i) ∣ n.natAbs := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp (hcop hi hj hij)
  · intro i hi
    exact Int.natCast_dvd.mp (hdiv i hi)

theorem card_bound {ι : Type*} (S : Finset ι) (g : ι → ℕ) (n : ℤ)
    (N τ β : ℝ) (hN : 1 < N) (hτ : 0 < τ) (hn : n ≠ 0)
    (hcop : (S : Set ι).Pairwise (fun i j ↦ (g i).Coprime (g j)))
    (hdiv : ∀ i ∈ S, (g i : ℤ) ∣ n) (hlarge : ∀ i ∈ S, N ^ τ ≤ (g i : ℝ))
    (hheight : (n.natAbs : ℝ) ≤ N ^ β) : (S.card : ℝ) ≤ β / τ := by
  have hprod : (((∏ i ∈ S, g i) : ℕ) : ℝ) ≤ N ^ β := by
    have hp := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (product_dvd S g n hcop hdiv)
    exact (by exact_mod_cast hp : (((∏ i ∈ S, g i) : ℕ) : ℝ) ≤ n.natAbs).trans hheight
  have hlo : N ^ (τ * (S.card : ℝ)) ≤ (((∏ i ∈ S, g i) : ℕ) : ℝ) := by
    calc
      _ = (N ^ τ) ^ S.card := Real.rpow_mul_natCast (by linarith) _ _
      _ = ∏ _i ∈ S, N ^ τ := by rw [prod_const]
      _ ≤ ∏ i ∈ S, (g i : ℝ) :=
        prod_le_prod₀ (fun _ _ ↦ Real.rpow_nonneg (by linarith) _) hlarge
      _ = _ := by rw [Nat.cast_prod]
  have he := (Real.rpow_le_rpow_left_iff hN).mp (hlo.trans hprod)
  exact (le_div_iff₀ hτ).mpr (by simpa only [mul_comm] using he)

theorem line_divisor {ι : Type*} (x y a b c : ℤ) (s t : ι → ℤ) (g : ι → ℕ) (i : ι)
    (hs : (g i : ℤ) ∣ x + s i) (ht : (g i : ℤ) ∣ y + t i)
    (hline : a * s i + b * t i = c) : (g i : ℤ) ∣ a * x + b * y + c := by
  have he : a * x + b * y + c = a * (x + s i) + b * (y + t i) := by rw [← hline]; ring
  rw [he]
  exact (dvd_mul_of_dvd_right hs _).add (dvd_mul_of_dvd_right ht _)

theorem line_card_bound {ι : Type*} (S : Finset ι) (g : ι → ℕ)
    (x y a b c : ℤ) (s t : ι → ℤ) (N τ β : ℝ) (hN : 1 < N) (hτ : 0 < τ)
    (hne : a * x + b * y + c ≠ 0)
    (hcop : (S : Set ι).Pairwise (fun i j ↦ (g i).Coprime (g j)))
    (hs : ∀ i ∈ S, (g i : ℤ) ∣ x + s i) (ht : ∀ i ∈ S, (g i : ℤ) ∣ y + t i)
    (hline : ∀ i ∈ S, a * s i + b * t i = c)
    (hlarge : ∀ i ∈ S, N ^ τ ≤ (g i : ℝ))
    (hheight : ((a * x + b * y + c).natAbs : ℝ) ≤ N ^ β) :
    (S.card : ℝ) ≤ β / τ :=
  card_bound S g _ N τ β hN hτ hne hcop
    (fun i hi ↦ line_divisor x y a b c s t g i (hs i hi) (ht i hi) (hline i hi)) hlarge hheight

end PaperP1.CoprimeDivisorCardinality
