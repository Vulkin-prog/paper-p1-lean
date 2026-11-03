module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # Veronese generation for the actual weights 1 and D

The proof splits exponent vectors into pieces of weight D. It applies
through every algebra map, and hence to every homogeneous quotient.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedVeroneseGeneration

open Finset

theorem weight_eq_degree {σ : Type*} (w : σ → ℕ) (d : σ →₀ ℕ)
    (hw : ∀ i ∈ d.support, w i = 1) : Finsupp.weight w d = d.degree := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply]
  apply sum_congr rfl
  intro i hi
  rw [hw i hi, smul_eq_mul, mul_one]

theorem exists_weight_piece {σ : Type*} (w : σ → ℕ) (D : ℕ)
    (hw : ∀ i, w i = 1 ∨ w i = D) (d : σ →₀ ℕ) (hd : D ≤ Finsupp.weight w d) :
    ∃ g ≤ d, Finsupp.weight w g = D := by
  classical
  by_cases hlarge : ∃ i ∈ d.support, w i = D
  · obtain ⟨i, hi, hwi⟩ := hlarge
    refine ⟨Finsupp.single i 1, Finsupp.single_le_iff.mpr ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    · rw [Finsupp.weight_single, hwi, one_smul]
  · have hsmall : ∀ i ∈ d.support, w i = 1 := by
      intro i hi
      exact (hw i).resolve_right (fun hwi ↦ hlarge ⟨i, hi, hwi⟩)
    obtain ⟨g, hgd, hg⟩ := Finsupp.exists_le_degree_eq d D (by rwa [← weight_eq_degree w d hsmall])
    exact ⟨g, hgd, (weight_eq_degree w g (fun i hi ↦ hsmall i (Finsupp.support_mono hgd hi))).trans hg⟩

theorem weight_nonzero {σ : Type*} (w : σ → ℕ) (D : ℕ) (hD : 0 < D)
    (hw : ∀ i, w i = 1 ∨ w i = D) : ∀ i, w i ≠ 0 := by
  intro i
  rcases hw i with hi | hi <;> omega

theorem monomial_image_mem {F σ A : Type*} [CommRing F] [CommRing A] [Algebra F A]
    (w : σ → ℕ) (D : ℕ) (hD : 0 < D) (hw : ∀ i, w i = 1 ∨ w i = D)
    (φ : MvPolynomial σ F →ₐ[F] A) (S : Subalgebra F A)
    (hS : ∀ p, MvPolynomial.IsWeightedHomogeneous w p D → φ p ∈ S)
    (n : ℕ) (d : σ →₀ ℕ) (hd : Finsupp.weight w d = n * D) (c : F) :
    φ (MvPolynomial.monomial d c) ∈ S := by
  induction n generalizing d with
  | zero =>
    have := Finsupp.nonTorsionWeight_of ℕ w (weight_nonzero w D hD hw)
    have hd0 : d = 0 := (Finsupp.weight_eq_zero_iff_eq_zero w).mp (by simpa only [zero_mul] using hd)
    subst d
    change φ (algebraMap F (MvPolynomial σ F) c) ∈ S
    rw [φ.commutes]
    exact S.algebraMap_mem c
  | succ n ih =>
    obtain ⟨g, hgd, hg⟩ := exists_weight_piece w D hw d (by rw [hd, Nat.succ_mul]; omega)
    obtain ⟨r, hdr⟩ := le_iff_exists_add.mp hgd
    have hr : Finsupp.weight w r = n * D := by
      rw [hdr, map_add, hg, Nat.succ_mul] at hd
      omega
    have hp := S.mul_mem (hS (MvPolynomial.monomial g 1)
      (MvPolynomial.isWeightedHomogeneous_monomial w g 1 hg)) (ih r hr)
    rw [← map_mul, MvPolynomial.monomial_mul_monomial, one_mul, ← hdr] at hp
    exact hp

theorem homogeneous_image_mem {F σ A : Type*} [CommRing F] [CommRing A] [Algebra F A]
    (w : σ → ℕ) (D : ℕ) (hD : 0 < D) (hw : ∀ i, w i = 1 ∨ w i = D)
    (φ : MvPolynomial σ F →ₐ[F] A) (S : Subalgebra F A)
    (hS : ∀ p, MvPolynomial.IsWeightedHomogeneous w p D → φ p ∈ S)
    (n : ℕ) (p : MvPolynomial σ F) (hp : MvPolynomial.IsWeightedHomogeneous w p (n * D)) :
    φ p ∈ S := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using S.zero_mem
  | add p q hp hq ihp ihq => simpa only [map_add] using S.add_mem ihp ihq
  | monomial d c hd => exact monomial_image_mem w D hD hw φ S hS n d hd c

def degreeImage {F σ A : Type*} [CommRing F] [CommRing A] [Algebra F A]
    (w : σ → ℕ) (φ : MvPolynomial σ F →ₐ[F] A) (d : ℕ) : Set A :=
  {x | ∃ p, MvPolynomial.IsWeightedHomogeneous w p d ∧ φ p = x}

def veroneseAlgebra {F σ A : Type*} [CommRing F] [CommRing A] [Algebra F A]
    (w : σ → ℕ) (φ : MvPolynomial σ F →ₐ[F] A) (D : ℕ) : Subalgebra F A :=
  Algebra.adjoin F {x | ∃ n, x ∈ degreeImage w φ (n * D)}

theorem veronese_generated {F σ A : Type*} [CommRing F] [CommRing A] [Algebra F A]
    (w : σ → ℕ) (D : ℕ) (hD : 0 < D) (hw : ∀ i, w i = 1 ∨ w i = D)
    (φ : MvPolynomial σ F →ₐ[F] A) :
    veroneseAlgebra w φ D = Algebra.adjoin F (degreeImage w φ D) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨n, p, hp, rfl⟩
    exact homogeneous_image_mem w D hD hw φ (Algebra.adjoin F (degreeImage w φ D))
      (fun q hq ↦ Algebra.subset_adjoin ⟨q, hq, rfl⟩) n p hp
  · apply Algebra.adjoin_le
    intro x hx
    exact Algebra.subset_adjoin ⟨1, by simpa only [one_mul] using hx⟩

end PaperP1.WeightedVeroneseGeneration
