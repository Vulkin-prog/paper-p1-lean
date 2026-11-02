module

public import PaperP1.Algebra.BivariateSeriesOrder
public import PaperP1.Algebra.BivariateTotalDegree

/-! # The reciprocal polynomial has total formal order equal to its pole weight minus its total degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateReciprocalSeries

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree
  PaperP1.BivariateSeriesOrder PaperP1.BiquadraticFormalNumerator

def reversedExponent (a b : ℕ) (i : Fin (a + 1) × Fin (b + 1)) : Option Unit →₀ ℕ :=
  exponent (a - i.1.val) (b - i.2.val)

def reciprocalMulti (P : ℤ[X][X]) (a b : ℕ) : MultiSeries :=
  ∑ i : Fin (a + 1) × Fin (b + 1),
    MvPowerSeries.monomial (reversedExponent a b i) ((P.coeff i.2.val).coeff i.1.val : ℚ)

def reciprocal (P : ℤ[X][X]) (a b : ℕ) : Series :=
  (IteratedPowerSeriesEquiv.equiv (σ := Unit) (R := ℚ)) (reciprocalMulti P a b)

theorem reversedExponent_injective (a b : ℕ) : Function.Injective (reversedExponent a b) := by
  intro i j h
  have hx := congrArg (fun d : Option Unit →₀ ℕ ↦ d (some ())) h
  have hy := congrArg (fun d : Option Unit →₀ ℕ ↦ d none) h
  simp only [reversedExponent, exponent_inner, exponent_outer] at hx hy
  apply Prod.ext
  · apply Fin.ext
    have hi := i.1.isLt
    have hj := j.1.isLt
    omega
  · apply Fin.ext
    have hi := i.2.isLt
    have hj := j.2.isLt
    omega

theorem coefficient_reciprocalMulti (P : ℤ[X][X]) (a b : ℕ) (i : Fin (a + 1) × Fin (b + 1)) :
    MvPowerSeries.coeff (reversedExponent a b i) (reciprocalMulti P a b) =
      ((P.coeff i.2.val).coeff i.1.val : ℚ) := by
  unfold reciprocalMulti
  rw [map_sum, sum_eq_single i]
  · exact MvPowerSeries.coeff_monomial_same _ _
  · intro j _ hji
    have hrev : reversedExponent a b i ≠ reversedExponent a b j :=
      fun h ↦ hji ((reversedExponent_injective a b h).symm)
    rw [MvPowerSeries.coeff_monomial, ite_eq_right hrev]
  · intro hi
    exact False.elim (hi (mem_univ i))

theorem reciprocal_order_lower (P : ℤ[X][X]) (a b : ℕ) :
    ((a + b - totalDegree P : ℕ) : ℕ∞) ≤ (reciprocalMulti P a b).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  unfold reciprocalMulti
  rw [map_sum]
  apply sum_eq_zero
  intro i _
  rw [MvPowerSeries.coeff_monomial]
  split_ifs with h
  · subst d
    by_cases hc : (P.coeff i.2.val).coeff i.1.val = 0
    · simp only [hc, Int.cast_zero]
    · have hdegree := coefficient_degree_le P i.1.val i.2.val hc
      have hi := i.1.isLt
      have hj := i.2.isLt
      simp only [reversedExponent, exponent_degree, exponent_inner, exponent_outer] at hd
      exfalso
      omega
  · rfl

theorem reciprocal_order (P : ℤ[X][X]) (a b : ℕ) (hP : P ≠ 0)
    (hx : degreeX P ≤ a) (hy : degreeY P ≤ b) :
    (reciprocalMulti P a b).order = ((a + b - totalDegree P : ℕ) : ℕ∞) := by
  obtain ⟨x, y, hc, he⟩ := exists_coefficient_degree P hP
  have hrow : P.coeff y ≠ 0 := fun h ↦ hc (by rw [h, coeff_zero])
  have hxa : x ≤ a := (le_natDegree_of_ne_zero hc).trans ((natDegree_coeff_le_degreeX P y).trans hx)
  have hyb : y ≤ b := (le_natDegree_of_ne_zero hrow).trans hy
  let i : Fin (a + 1) × Fin (b + 1) := (⟨x, by omega⟩, ⟨y, by omega⟩)
  have hn : MvPowerSeries.coeff (reversedExponent a b i) (reciprocalMulti P a b) ≠ 0 := by
    rw [coefficient_reciprocalMulti]
    exact_mod_cast hc
  have hdegree : (reversedExponent a b i).degree = a + b - totalDegree P := by
    simp only [reversedExponent, exponent_degree, exponent_inner, exponent_outer]
    change (a - x) + (b - y) = a + b - totalDegree P
    omega
  have hupper := MvPowerSeries.order_le hn
  rw [hdegree] at hupper
  exact le_antisymm hupper (reciprocal_order_lower P a b)

theorem toMultivariate_reciprocal (P : ℤ[X][X]) (a b : ℕ) :
    toMultivariate (reciprocal P a b) = reciprocalMulti P a b :=
  (IteratedPowerSeriesEquiv.equiv (σ := Unit) (R := ℚ)).symm_apply_apply _

theorem totalOrder_reciprocal (P : ℤ[X][X]) (a b : ℕ) (hP : P ≠ 0)
    (hx : degreeX P ≤ a) (hy : degreeY P ≤ b) :
    totalOrder (reciprocal P a b) = ((a + b - totalDegree P : ℕ) : ℕ∞) := by
  rw [totalOrder, toMultivariate_reciprocal]
  exact reciprocal_order P a b hP hx hy

theorem coefficient_reciprocal (P : ℤ[X][X]) (a b : ℕ) (i : Fin (a + 1) × Fin (b + 1)) :
    coefficient (a - i.1.val) (b - i.2.val) (reciprocal P a b) =
      ((P.coeff i.2.val).coeff i.1.val : ℚ) := by
  have h := coefficient_reciprocalMulti P a b i
  rw [← toMultivariate_reciprocal P a b, coefficient_toMultivariate] at h
  simpa only [reversedExponent, exponent_inner, exponent_outer] using h

theorem reciprocal_zero (a b : ℕ) : reciprocal 0 a b = 0 := by
  simp [reciprocal, reciprocalMulti]

end PaperP1.BivariateReciprocalSeries
