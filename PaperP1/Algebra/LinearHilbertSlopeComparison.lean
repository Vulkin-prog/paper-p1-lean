module

public import PaperP1.Algebra.LinearHilbertGrowth
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Injective homogeneous-piece maps bound actual Hilbert slopes after degree rescaling -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHilbertSlopeComparison

open Polynomial PaperP1.LinearHilbertGrowth

theorem slope_le {h g : ℕ → ℚ} {a b : ℚ} (ha : HasSlope h a) (hb : HasSlope g b)
    (D : ℕ) (hD : 0 < D) (K : ℕ) (hcompare : ∀ n, K ≤ n → h n ≤ g (n * D)) : a ≤ b * (D : ℚ) := by
  obtain ⟨C, N, hN⟩ := ha
  obtain ⟨C', M, hM⟩ := hb
  by_contra hnot
  have hgap : 0 < a - b * (D : ℚ) := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨k, hk⟩ := exists_nat_gt ((C + C') / (a - b * (D : ℚ)))
  let n := max (max (max N M) K) k
  have hnN : N ≤ n := (le_max_left N M).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hnM : M ≤ n := (le_max_right N M).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hnK : K ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  have hkn : (k : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr (le_max_right _ _)
  have hbig : C + C' < (n : ℚ) * (a - b * (D : ℚ)) :=
    (div_lt_iff₀ hgap).mp (hk.trans_le hkn)
  have hlow := (abs_le.mp (hN n hnN)).1
  have hupp := (abs_le.mp (hM (n * D) (hnM.trans (Nat.le_mul_of_pos_right n hD)))).2
  have hcomp := hcompare n hnK
  rw [Nat.cast_mul] at hupp
  nlinarith

variable {F A B : Type*} [Field F] [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]

theorem piece_finrank_le (G : ℕ → Submodule F A) (H : ℕ → Submodule F B)
    (D n : ℕ) (f : A →ₗ[F] B) (hf : Function.Injective f)
    (hmem : ∀ n, ∀ x ∈ G n, f x ∈ H (n * D)) [Module.Finite F (H (n * D))] :
    Module.finrank F (G n) ≤ Module.finrank F (H (n * D)) := by
  let φ : G n →ₗ[F] H (n * D) := (f.comp (G n).subtype).codRestrict (H (n * D))
    (fun x ↦ hmem n x.val x.property)
  apply LinearMap.finrank_le_finrank_of_injective (f := φ)
  intro x y hxy
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val hxy

theorem slope_le_of_injective (G : ℕ → Submodule F A) (H : ℕ → Submodule F B)
    [∀ n, Module.Finite F (H n)] (a b : ℚ) (ha : HasSlope (function G) a) (hb : HasSlope (function H) b)
    (D : ℕ) (hD : 0 < D) (f : A →ₗ[F] B) (hf : Function.Injective f)
    (hmem : ∀ n, ∀ x ∈ G n, f x ∈ H (n * D)) : a ≤ b * (D : ℚ) := by
  apply slope_le ha hb D hD 0
  intro n _
  change (Module.finrank F (G n) : ℚ) ≤ (Module.finrank F (H (n * D)) : ℚ)
  exact_mod_cast piece_finrank_le G H D n f hf hmem

theorem multiplicity_eq_slope (G : ℕ → Submodule F A)
    (hG : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial G p)
    (a : ℚ) (ha : 0 < a) (hslope : HasSlope (function G) a) :
    GradedHilbertPolynomial.multiplicity G hG = a := by
  obtain ⟨b, hp⟩ := hilbert_polynomial_affine hslope hG.choose_spec
  rw [GradedHilbertPolynomial.multiplicity, GradedHilbertPolynomial.polynomial, hp]
  have hdegree : (C a * X + C b).natDegree = 1 := by
    compute_degree
    exact ha.ne'
  rw [hdegree, Nat.factorial_one, Nat.cast_one, one_mul]
  rw [Polynomial.leadingCoeff, hdegree]
  simp

end PaperP1.LinearHilbertSlopeComparison
