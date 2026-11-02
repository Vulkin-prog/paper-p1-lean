module

public import PaperP1.Model.InfiniteRademacher
public import PaperP1.Arithmetic.FiniteEvenSquareClasses
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Arbitrary bits on an actual private set of integer values have prime-sign witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateValuePrescriptions

open Finset PaperP1.Arithmetic PaperP1.Model.InfiniteRademacher

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def sampleOf (f : (ℕ →₀ F₂) →ₗ[F₂] F₂) : InfiniteSample :=
  fun k ↦ f (Finsupp.single (Nat.nth Nat.Prime k) 1)

theorem value_of_functional (f : (ℕ →₀ F₂) →ₗ[F₂] F₂) (n : ℕ) :
    infiniteValueBit (sampleOf f) n = f (parityVec n) := by
  have hprime (p : ℕ) (hp : p ∈ (parityVec n).support) : p.Prime := by
    have hne := Finsupp.mem_support_iff.mp hp
    by_contra hn
    rw [parityVec_apply, Nat.factorization_eq_zero_of_not_prime _ hn, Nat.cast_zero] at hne
    exact hne rfl
  calc
    _ = ∑ p ∈ (parityVec n).support, f (Finsupp.single p (parityVec n p)) := by
      unfold infiniteValueBit Finsupp.sum
      apply sum_congr rfl
      intro p hp
      have hindex : Nat.nth Nat.Prime (Nat.primeCounting' p) = p := Nat.nth_count (hprime p hp)
      have hsingle : Finsupp.single p (parityVec n p) = (parityVec n p) • Finsupp.single p 1 := by
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      change f (Finsupp.single (Nat.nth Nat.Prime (Nat.primeCounting' p)) 1) * parityVec n p = _
      rw [hindex, hsingle, map_smul, smul_eq_mul, mul_comm]
    _ = f (∑ p ∈ (parityVec n).support, Finsupp.single p (parityVec n p)) := by rw [map_sum]
    _ = _ := by congr 1; exact Finsupp.sum_single _

def evaluation (S : Finset ℕ) (b : S → F₂) : (S → F₂) →ₗ[F₂] F₂ :=
  ∑ n : S, (b n) • (LinearMap.proj n : (S → F₂) →ₗ[F₂] F₂)

theorem evaluation_single (S : Finset ℕ) (b : S → F₂) (n : S) :
    evaluation S b (Pi.single n 1) = b n := by
  classical
  simp [evaluation, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, Pi.single_apply]

theorem prescribe (S : Finset ℕ) (hS : FiniteEvenSquareClasses.Private S) (b : S → F₂) :
    ∃ ω : InfiniteSample, ∀ n : S, infiniteValueBit ω n.val = b n := by
  classical
  let f := EvenImage.combination (K := F₂) (FiniteEvenSquareClasses.data S)
  have hfi : Function.Injective f := FiniteEvenSquareClasses.combination_injective S hS
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hfi)
  let h : (ℕ →₀ F₂) →ₗ[F₂] F₂ := (evaluation S b).comp g
  refine ⟨sampleOf h, fun n ↦ ?_⟩
  have hsingle : f (Pi.single n 1) = parityVec n.val := by
    simp only [f, EvenImage.combination, Fintype.linearCombination_apply_single, one_smul,
      FiniteEvenSquareClasses.data]
  have hgpoint : g (parityVec n.val) = Pi.single n 1 := by
    rw [← hsingle]
    exact congrArg (fun u : (S → F₂) →ₗ[F₂] (S → F₂) ↦ u (Pi.single n 1)) hg
  rw [value_of_functional]
  change evaluation S b (g (parityVec n.val)) = b n
  rw [hgpoint, evaluation_single]

end PaperP1.PrivateValuePrescriptions
