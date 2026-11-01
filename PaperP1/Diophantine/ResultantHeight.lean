module

public import PaperP1.Diophantine.ResultantDivisibility
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.Tactic.Positivity

/-! # Explicit coefficient-uniform heights of the actual two chart resultants -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ResultantHeight

open Polynomial

theorem sylvester_entry_bound (f g : ℤ[X]) (m n H : ℕ)
    (hf : ∀ k, (f.coeff k).natAbs ≤ H) (hg : ∀ k, (g.coeff k).natAbs ≤ H)
    (i j : Fin (m + n)) : |Polynomial.sylvester f g m n i j| ≤ (H : ℤ) := by
  have hfc (k : ℕ) : |f.coeff k| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hf k
  have hgc (k : ℕ) : |g.coeff k| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hg k
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hgc _
    · simp
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hfc _
    · simp

theorem resultant_bound (f g : ℤ[X]) (m n H : ℕ)
    (hf : ∀ k, (f.coeff k).natAbs ≤ H) (hg : ∀ k, (g.coeff k).natAbs ≤ H) :
    (f.resultant g m n).natAbs ≤ (m + n).factorial * H ^ (m + n) := by
  have h := Matrix.det_le (A := Polynomial.sylvester f g m n)
    (abv := AbsoluteValue.abs) (x := (H : ℤ))
    (fun i j ↦ sylvester_entry_bound f g m n H hf hg i j)
  have hcast : ((f.resultant g m n).natAbs : ℤ) ≤
      (((m + n).factorial * H ^ (m + n) : ℕ) : ℤ) := by
    simpa only [Polynomial.resultant, AbsoluteValue.abs_apply, Fintype.card_fin,
      nsmul_eq_mul, Int.abs_eq_natAbs, Nat.cast_mul, Nat.cast_pow] using h
  exact_mod_cast hcast

theorem reflected_coeff_bound (f : ℤ[X]) (d H : ℕ) (hf : ∀ k, (f.coeff k).natAbs ≤ H) :
    ∀ k, ((f.reflect d).coeff k).natAbs ≤ H := by
  intro k
  rw [Polynomial.coeff_reflect]
  exact hf _

theorem chart_product_bound (f g : ℤ[X]) (d H : ℕ)
    (hf : ∀ k, (f.coeff k).natAbs ≤ H) (hg : ∀ k, (g.coeff k).natAbs ≤ H) :
    (f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d).natAbs ≤
      ((d + d).factorial * H ^ (d + d)) ^ 2 := by
  rw [Int.natAbs_mul, pow_two]
  exact Nat.mul_le_mul (resultant_bound f g d d H hf hg)
    (resultant_bound (f.reflect d) (g.reflect d) d d H
      (reflected_coeff_bound f d H hf) (reflected_coeff_bound g d H hg))

def productExponent (d k : ℕ) : ℕ := 2 * k * (d + d) + 1

theorem polynomial_product_height (d k : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X],
      (∀ j, (f.coeff j).natAbs ≤ N ^ k) → (∀ j, (g.coeff j).natAbs ≤ N ^ k) →
        (f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d).natAbs ≤ N ^ productExponent d k := by
  refine ⟨max 1 ((d + d).factorial ^ 2), ?_⟩
  intro N hN f g hf hg
  have hconstant : (d + d).factorial ^ 2 ≤ N := by omega
  calc
    _ ≤ ((d + d).factorial * (N ^ k) ^ (d + d)) ^ 2 := chart_product_bound f g d (N ^ k) hf hg
    _ = (d + d).factorial ^ 2 * N ^ (2 * k * (d + d)) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      congr 2
      ring
    _ ≤ N * N ^ (2 * k * (d + d)) := Nat.mul_le_mul_right _ hconstant
    _ = _ := by unfold productExponent; rw [pow_succ']

theorem coefficient_uniform_denominator_count (d k : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X], f.natDegree ≤ d → g.natDegree ≤ d →
      f.resultant g d d ≠ 0 → (f.reflect d).resultant (g.reflect d) d d ≠ 0 →
      (∀ j, (f.coeff j).natAbs ≤ N ^ k) → (∀ j, (g.coeff j).natAbs ≤ N ^ k) →
        ∀ S : Finset ℤ,
          (∀ q ∈ S, q ≠ 0 ∧ ∃ a b : ℤ, a.natAbs.Coprime b.natAbs ∧
            q ∣ MvPolynomial.eval ![a, b] (f.homogenize d) ∧
            q ∣ MvPolynomial.eval ![a, b] (g.homogenize d)) → (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nh, hNh⟩ := polynomial_product_height d k
  obtain ⟨Nd, hNd⟩ := PaperP1.ResultantDivisibility.polynomial_height_denominator_count (productExponent d k) ε hε
  refine ⟨max Nh Nd, ?_⟩
  intro N hN f g hf hg hR hR' hfc hgc S hS
  exact hNd N (by omega) f g d hd hf hg hR hR' (hNh N (by omega) f g hfc hgc) S hS

end PaperP1.ResultantHeight
