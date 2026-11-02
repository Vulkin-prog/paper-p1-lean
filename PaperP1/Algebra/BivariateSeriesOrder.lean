module

public import PaperP1.Algebra.IteratedPowerSeriesEquiv
public import PaperP1.Arithmetic.BiquadraticFormalNumerator
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! # Total order and exact division of actual iterated bivariate formal power series -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateSeriesOrder

open Finsupp PaperP1.BiquadraticFormalNumerator

abbrev MultiSeries := MvPowerSeries (Option Unit) ℚ

def toMultivariate : Series →+* MultiSeries :=
  (IteratedPowerSeriesEquiv.equiv (σ := Unit) (R := ℚ)).symm.toRingHom

def exponent (a b : ℕ) : Option Unit →₀ ℕ := (single () a).optionElim b

@[simp]
theorem exponent_inner (a b : ℕ) : exponent a b (some ()) = a := by simp [exponent]

@[simp]
theorem exponent_outer (a b : ℕ) : exponent a b none = b := by simp [exponent]

theorem exponent_degree (d : Option Unit →₀ ℕ) : d.degree = d (some ()) + d none := by
  rw [degree_eq_sum, Fintype.sum_option, Fintype.sum_unique, add_comm]

theorem coefficient_toMultivariate (f : Series) (d : Option Unit →₀ ℕ) :
    MvPowerSeries.coeff d (toMultivariate f) = coefficient (d (some ())) (d none) f := by
  change MvPowerSeries.coeff d.some (PowerSeries.coeff (d none) f) = _
  have hs : d.some = single () (d (some ())) := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  rw [hs]
  rfl

def totalOrder (f : Series) : ℕ∞ := (toMultivariate f).order

theorem coefficient_order_le (f : Series) (a b : ℕ) (h : coefficient a b f ≠ 0) :
    totalOrder f ≤ (a + b : ℕ) := by
  have hc : MvPowerSeries.coeff (exponent a b) (toMultivariate f) ≠ 0 := by
    simpa only [coefficient_toMultivariate, exponent_inner, exponent_outer] using h
  have ho := MvPowerSeries.order_le hc
  simpa only [totalOrder, exponent_degree, exponent_inner, exponent_outer] using ho

theorem nat_le_totalOrder (f : Series) (n : ℕ)
    (h : ∀ a b, a + b < n → coefficient a b f = 0) : (n : ℕ∞) ≤ totalOrder f := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  rw [coefficient_toMultivariate]
  exact h _ _ (by rwa [exponent_degree] at hd)

theorem coefficient_zero_of_lt (f : Series) (a b : ℕ) (h : (a + b : ℕ) < totalOrder f) :
    coefficient a b f = 0 := by
  have hd : ((exponent a b).degree : ℕ∞) < (toMultivariate f).order := by
    simpa only [exponent_degree, exponent_inner, exponent_outer, totalOrder] using h
  simpa only [coefficient_toMultivariate, exponent_inner, exponent_outer] using
    MvPowerSeries.coeff_of_lt_order hd

theorem totalOrder_mul (f g : Series) : totalOrder (f * g) = totalOrder f + totalOrder g := by
  simpa only [totalOrder, map_mul] using MvPowerSeries.order_mul (toMultivariate f) (toMultivariate g)

theorem quotient_vanishing (D g : Series) (δ n : ℕ) (hD : totalOrder D = (δ : ℕ∞))
    (hprod : ∀ a b, a + b < n → coefficient a b (D * g) = 0) :
    ∀ a b, a + b < n - δ → coefficient a b g = 0 := by
  have hfull := nat_le_totalOrder (D * g) n hprod
  intro a b hab
  by_contra hc
  have hg := coefficient_order_le g a b hc
  have hprod_le : totalOrder (D * g) ≤ ((δ + (a + b) : ℕ) : ℕ∞) := by
    rw [totalOrder_mul, hD]
    simpa only [Nat.cast_add] using add_le_add (le_rfl : (δ : ℕ∞) ≤ δ) hg
  have hsmall : δ + (a + b) < n := by omega
  have hcast : ((δ + (a + b) : ℕ) : ℕ∞) < n := by exact_mod_cast hsmall
  exact (not_lt_of_ge hfull) (hprod_le.trans_lt hcast)

end PaperP1.BivariateSeriesOrder
