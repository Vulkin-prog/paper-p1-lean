module

public import PaperP1.Algebra.GradedLinearHilbertSection

/-! # A genuine regular homogeneous equation gives the section dimension without a domain assumption -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularGradedHilbertSection

open Polynomial HomogeneousPrincipalQuotient

theorem mulMap_injective {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (G : ℕ → Submodule F A) [GradedAlgebra G] {e : ℕ} {f : A} (hf : f ∈ G e)
    (hregular : Function.Injective (fun a : A ↦ a * f)) (n : ℕ) :
    Function.Injective (mulMap G hf n) := by
  intro x y h
  apply Subtype.ext
  exact hregular (congrArg Subtype.val h)

theorem finrank_add {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (G : ℕ → Submodule F A) [GradedAlgebra G] {e : ℕ} {f : A} (hf : f ∈ G e)
    (hregular : Function.Injective (fun a : A ↦ a * f)) (n : ℕ) [Module.Finite F (G (n + e))] :
    Module.finrank F (piece G f (n + e)) + Module.finrank F (G n) = Module.finrank F (G (n + e)) := by
  have hdim := (LinearMap.ker (quotientMap G f (n + e))).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq ((quotientMap G f (n + e)).quotKerEquivOfSurjective
    (quotientMap_surjective G f (n + e)))] at hdim
  have hr : Module.finrank F (LinearMap.ker (quotientMap G f (n + e))) = Module.finrank F (G n) := by
    rw [← range_mulMap G hf n]
    exact (LinearEquiv.ofInjective (mulMap G hf n) (mulMap_injective G hf hregular n)).finrank_eq.symm
  rw [hr] at hdim
  exact hdim

theorem eventual_dimension {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (G : ℕ → Submodule F A) [GradedAlgebra G] (d : ℕ) (hd : 0 < d) (b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G (C (d : ℚ) * X + C b))
    {e : ℕ} {f : A} (hf : f ∈ G e) (hregular : Function.Injective (fun a : A ↦ a * f)) :
    ∃ N : ℕ, ∀ n ≥ N, Module.finrank F (piece G f (n + e)) = e * d := by
  obtain ⟨N₀, hN₀⟩ := hp
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  obtain ⟨M, hM⟩ := exists_nat_gt (-b / (d : ℚ))
  have hMb : 0 < (d : ℚ) * (M : ℚ) + b := by
    have hh := (div_lt_iff₀ hdQ).mp hM
    nlinarith only [hh]
  refine ⟨max N₀ M, ?_⟩
  intro n hn
  have hnN : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have h₀ := hN₀ n hnN
  have h₁ := hN₀ (n + e) (by omega)
  simp only [eval_add, eval_mul, eval_C, eval_X, Nat.cast_add] at h₀ h₁
  have hnmQ : (M : ℚ) ≤ (n : ℚ) := by exact_mod_cast hnM
  have hposQ : (0 : ℚ) < (Module.finrank F (G (n + e)) : ℚ) := by
    have heQ : (0 : ℚ) ≤ e := Nat.cast_nonneg _
    nlinarith only [h₁, hMb, hnmQ, hdQ, heQ]
  let : Module.Finite F (G (n + e)) := Module.finite_of_finrank_pos (by exact_mod_cast hposQ)
  have hdim := finrank_add G hf hregular n
  have hdimQ : (Module.finrank F (piece G f (n + e)) : ℚ) +
      (Module.finrank F (G n) : ℚ) = (Module.finrank F (G (n + e)) : ℚ) := by
    exact_mod_cast hdim
  have heq : (Module.finrank F (piece G f (n + e)) : ℚ) = ((e * d : ℕ) : ℚ) := by
    push_cast
    nlinarith only [h₀, h₁, hdimQ]
  exact_mod_cast heq

end PaperP1.RegularGradedHilbertSection
