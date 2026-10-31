module

public import PaperP1.Model.FiniteRademacher
public import PaperP1.Probability.InfiniteCylinderTransfer

/-!
# Prime-exponent parity vectors as actual characters

The finite prime cylinder pairs a parity vector with its assigned prime bits.
This pairing is injective on vectors supported on primes at most the cutoff.
Consequently it loses no square-class relation among supported window vertices.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic

namespace PaperP1.Model

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def parityFunctional (M : ℕ) (c : ℕ →₀ F₂) : SampleSpace M →ₗ[F₂] F₂ where
  toFun := fun ω => ∑ p : PrimeUpTo M, ω p * c p.1
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, mul_assoc]

def parityPairing (M : ℕ) : (ℕ →₀ F₂) →ₗ[F₂] (SampleSpace M →ₗ[F₂] F₂) where
  toFun := parityFunctional M
  map_add' := by intros; ext ω; simp [parityFunctional, mul_add, Finset.sum_add_distrib]
  map_smul' := by intros; ext ω; simp [parityFunctional, Finset.mul_sum, mul_left_comm]

@[simp]
theorem parityPairing_apply (M : ℕ) (c : ℕ →₀ F₂) (ω : SampleSpace M) :
    parityPairing M c ω = ∑ p : PrimeUpTo M, ω p * c p.1 := rfl

@[simp]
theorem parityPairing_parityVec (M n : ℕ) : parityPairing M (parityVec n) = valueLinear M n := by
  ext ω
  rfl

/-- The ambient subspace of square-class vectors represented by the cylinder. -/
def boundedPrimeParity (M : ℕ) : Submodule F₂ (ℕ →₀ F₂) where
  carrier := {c | ∀ p, ¬(p.Prime ∧ p ≤ M) → c p = 0}
  zero_mem' := by simp
  add_mem' := by intro c d hc hd p hp; simp [hc p hp, hd p hp]
  smul_mem' := by intro a c hc p hp; simp [hc p hp]

theorem parityVec_mem_boundedPrimeParity {M n : ℕ} (hn : n ≤ M) :
    parityVec n ∈ boundedPrimeParity M := by
  intro p hp
  by_contra h
  have hs : p ∈ (parityVec n).support := Finsupp.mem_support_iff.mpr h
  have hf : p ∈ n.primeFactors := Finsupp.support_mapRange hs
  exact hp ⟨Nat.prime_of_mem_primeFactors hf, (Nat.le_of_mem_primeFactors hf).trans hn⟩

theorem parityPairing_eq_zero_iff_of_bounded (M : ℕ) (c : ℕ →₀ F₂)
    (hc : c ∈ boundedPrimeParity M) : parityPairing M c = 0 ↔ c = 0 := by
  constructor
  · intro h
    ext p
    by_cases hp : p.Prime ∧ p ≤ M
    · let q : PrimeUpTo M := ⟨⟨p, Nat.lt_succ_of_le hp.2⟩, hp.1⟩
      let ωq : SampleSpace M := Pi.single q 1
      have he := DFunLike.congr_fun h ωq
      have hs : (∑ r : PrimeUpTo M, ωq r * c r.1) = c p := by
        rw [Finset.sum_eq_single q]
        · change ωq q * c p = c p
          rw [show ωq q = 1 from Pi.single_eq_same q 1, one_mul]
        · intro r _ hr
          simp only [ωq, Pi.single_eq_of_ne hr, zero_mul]
        · simp
      change (∑ r : PrimeUpTo M, ωq r * c r.1) = 0 at he
      exact hs.symm.trans he
    · exact hc p hp
  · rintro rfl
    exact map_zero _

theorem parityPairing_injOn_bounded (M : ℕ) :
    Set.InjOn (parityPairing M) (boundedPrimeParity M) := by
  intro c hc d hd h
  apply sub_eq_zero.mp
  apply (parityPairing_eq_zero_iff_of_bounded M (c - d)
    ((boundedPrimeParity M).sub_mem hc hd)).mp
  rw [map_sub, h, sub_self]

end PaperP1.Model
