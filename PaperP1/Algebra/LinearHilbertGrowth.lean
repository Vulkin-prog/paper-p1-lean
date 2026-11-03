module

public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Linarith

/-! # A bounded-error linear Hilbert slope is an actual, unique numerical invariant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHilbertGrowth

open Polynomial
open Filter

def HasSlope (h : ℕ → ℚ) (a : ℚ) : Prop :=
  ∃ C : ℚ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |h n - a * (n : ℚ)| ≤ C

theorem unique {h : ℕ → ℚ} {a b : ℚ} (ha : HasSlope h a) (hb : HasSlope h b) : a = b := by
  obtain ⟨C, N, hN⟩ := ha
  obtain ⟨D, M, hM⟩ := hb
  suffices ∀ {a b : ℚ}, a < b →
      (∃ C : ℚ, ∃ N : ℕ, ∀ n, N ≤ n → |h n - a * (n : ℚ)| ≤ C) →
      (∃ D : ℚ, ∃ M : ℕ, ∀ n, M ≤ n → |h n - b * (n : ℚ)| ≤ D) → False by
    rcases lt_trichotomy a b with hab | hab | hab
    · exact False.elim (this hab ⟨C, N, hN⟩ ⟨D, M, hM⟩)
    · exact hab
    · exact False.elim (this hab ⟨D, M, hM⟩ ⟨C, N, hN⟩)
  intro a b hab ha hb
  obtain ⟨C, N, hN⟩ := ha
  obtain ⟨D, M, hM⟩ := hb
  obtain ⟨k, hk⟩ := exists_nat_gt ((C + D) / (b - a))
  let n := max (max N M) k
  have hnN : N ≤ n := (le_max_left N M).trans (le_max_left _ _)
  have hnM : M ≤ n := (le_max_right N M).trans (le_max_left _ _)
  have hkn : (k : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr (le_max_right _ _)
  have hbig : C + D < (n : ℚ) * (b - a) := (div_lt_iff₀ (sub_pos.mpr hab)).mp (hk.trans_le hkn)
  have h1 := (abs_le.mp (hN n hnN)).2
  have h2 := (abs_le.mp (hM n hnM)).1
  nlinarith

theorem polynomial_affine {p : ℚ[X]} {a : ℚ}
    (hp : HasSlope (fun n : ℕ ↦ p.eval (n : ℚ)) a) :
    ∃ b : ℚ, p = C a * X + C b := by
  obtain ⟨C₀, N, hN⟩ := hp
  let q := p - C a * X
  have hdeg : q.degree ≤ 0 := by
    by_contra h
    have ht := (Polynomial.abs_tendsto_atTop q (lt_of_not_ge h)).comp
      (tendsto_natCast_atTop_atTop (R := ℚ))
    have hb : ∀ᶠ n : ℕ in atTop, |q.eval (n : ℚ)| ≤ C₀ := by
      apply eventually_atTop.mpr
      refine ⟨N, fun n hn ↦ ?_⟩
      simpa only [q, eval_sub, eval_mul, eval_C, eval_X] using hN n hn
    obtain ⟨n, hle, hgt⟩ := (hb.and (ht.eventually_gt_atTop C₀)).exists
    exact (not_lt_of_ge hle) hgt
  refine ⟨q.coeff 0, ?_⟩
  have he : p - C a * X = C (q.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

def function (G : ℕ → Submodule F A) (n : ℕ) : ℚ := (Module.finrank F (G n) : ℚ)

theorem of_affine_polynomial {G : ℕ → Submodule F A} {a b : ℚ}
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G (C a * X + C b)) :
    HasSlope (function G) a := by
  obtain ⟨N, hN⟩ := hp
  refine ⟨|b|, N, fun n hn ↦ ?_⟩
  have he := hN n hn
  simp only [eval_add, eval_mul, eval_C, eval_X] at he
  have hsub : function G n - a * (n : ℚ) = b := by unfold function; linarith
  rw [hsub]

theorem of_polynomial_degree_le_one {G : ℕ → Submodule F A} {p : ℚ[X]}
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G p) (hdeg : p.natDegree ≤ 1) :
    HasSlope (function G) (p.coeff 1) := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg] at hp
  exact of_affine_polynomial hp

theorem hilbert_polynomial_affine {G : ℕ → Submodule F A} {p : ℚ[X]} {a : ℚ}
    (ha : HasSlope (function G) a) (hp : GradedHilbertPolynomial.IsHilbertPolynomial G p) :
    ∃ b : ℚ, p = C a * X + C b := by
  obtain ⟨C₀, N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hp
  apply polynomial_affine
  refine ⟨C₀, max N M, fun n hn ↦ ?_⟩
  change |p.eval (n : ℚ) - a * (n : ℚ)| ≤ C₀
  rw [hM n ((le_max_right N M).trans hn)]
  exact hN n ((le_max_left N M).trans hn)

theorem coefficient_eq {G : ℕ → Submodule F A} {p : ℚ[X]} {a : ℚ}
    (ha : HasSlope (function G) a) (hp : GradedHilbertPolynomial.IsHilbertPolynomial G p) :
    p.coeff 1 = a := by
  obtain ⟨b, rfl⟩ := hilbert_polynomial_affine ha hp
  simp

theorem polynomial_natDegree_le_one {G : ℕ → Submodule F A} {p : ℚ[X]} {a : ℚ}
    (ha : HasSlope (function G) a) (hp : GradedHilbertPolynomial.IsHilbertPolynomial G p) :
    p.natDegree ≤ 1 := by
  obtain ⟨b, rfl⟩ := hilbert_polynomial_affine ha hp
  compute_degree

end PaperP1.LinearHilbertGrowth
