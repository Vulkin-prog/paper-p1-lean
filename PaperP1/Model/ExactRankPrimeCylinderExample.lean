module

public import PaperP1.Model.RankChargedPrimeCylinder

/-! # Exact rank of the retained forcing example N=18, q=3

The five retained starts observe precisely the integers 21,...,35. Their
homogeneous equations kill all prime bits except 19: the values
27,32,30,28,22,26,34,23,29,31 successively determine the ten other bits.
Evaluation at the unused prime is therefore injective on the kernel, and
its nonzero basis sample proves that the kernel has dimension one.
Rank-nullity gives rank 10 and the compatible forcing fiber has exactly
two samples and mass 2^-10.

This is the finite optional refinement S07 of the independent manuscript
review. No general rank formula, new asymptotic threshold or improvement
to the already proved moment lower bound is asserted. The frozen version
1.8 sources retain their valid rank<=10 formulation.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.ExactRankPrimeCylinderExample

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.Affine
  PaperP1.RankChargedPrimeCylinder PaperP1.LocalDefectBound

local instance primeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

local notation "p2" => (⟨⟨2, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p3" => (⟨⟨3, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p5" => (⟨⟨5, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p7" => (⟨⟨7, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p11" => (⟨⟨11, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p13" => (⟨⟨13, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p17" => (⟨⟨17, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p23" => (⟨⟨23, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p29" => (⟨⟨29, by decide⟩, by decide⟩ : PrimeUpTo 36)
local notation "p31" => (⟨⟨31, by decide⟩, by decide⟩ : PrimeUpTo 36)

theorem prime_value {M : ℕ} (σ : SampleSpace M) (p : PrimeUpTo M) :
    valueBit σ p.val.val = σ p := by
  classical
  rw [valueBit, Fintype.sum_eq_single p]
  · simp [parityVec_apply, p.property.factorization]
  · intro q hqp
    have hval : q.val.val ≠ p.val.val := by
      intro h
      exact hqp (Subtype.ext (Fin.ext h))
    simp [parityVec_apply, p.property.factorization, hval]

theorem square_value {M : ℕ} (σ : SampleSpace M) (a : ℕ) :
    valueBit σ (a^2) = 0 := by
  simp [valueBit, parityVec_pow_two]

theorem starts_example :
    ValuationPrimeCylinder.starts 18 3 = {22,25,28,31,34} := by
  rw [ValuationPrimeCylinder.starts, retained_parameters_example]
  decide +kernel

theorem kernel_forced_bits (σ : SampleSpace 36)
    (hσ : σ ∈ LinearMap.ker (system 36 (ValuationPrimeCylinder.starts 18 3) 2)) :
    ∀ p : PrimeUpTo 36, p ≠ unusedPrimeExample → σ p = 0 := by
  let G : Finset ℕ := {22,25,28,31,34}
  have hG : ValuationPrimeCylinder.starts 18 3 = G := starts_example
  have hker : σ ∈ LinearMap.ker (system 36 G 2) := hG ▸ hσ
  have hsys := LinearMap.mem_ker.mp hker
  have prev (x : ℕ) (hx : x ∈ G) :
      valueBit σ (x-1) = 0 := congrFun hsys (⟨x,hx⟩,none)
  have word (x : ℕ) (hx : x ∈ G)
      (j : ℕ) (hj : j<2) : valueBit σ (x+j) = 0 :=
    congrFun hsys (⟨x,hx⟩,some ⟨j,hj⟩)
  have h3 : σ p3 = 0 := by
    have h := prev 28 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide)
    rw [show (28-1 : ℕ) = 3^2*3 by decide] at h
    rw [valueBit_mul σ (by decide) (by decide), square_value, zero_add,
      prime_value σ p3] at h
    exact h
  have h2 : σ p2 = 0 := by
    have h := word 31 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide) 1 (by decide)
    rw [show (31+1 : ℕ) = 4^2*2 by decide] at h
    rw [valueBit_mul σ (by decide) (by decide), square_value, zero_add,
      prime_value σ p2] at h
    exact h
  have h5 : σ p5 = 0 := by
    have h := prev 31 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide)
    rw [show (31-1 : ℕ) = (2*3)*5 by decide] at h
    rw [valueBit_mul σ (by decide) (by decide),
      valueBit_mul σ (by decide) (by decide), prime_value σ p2,
      prime_value σ p3, prime_value σ p5, h2, h3, zero_add, zero_add] at h
    exact h
  have h7 : σ p7 = 0 := by
    have h := word 28 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide) 0 (by decide)
    rw [show (28+0 : ℕ) = 2^2*7 by decide] at h
    rw [valueBit_mul σ (by decide) (by decide), square_value, zero_add,
      prime_value σ p7] at h
    exact h
  have h11 : σ p11 = 0 := by
    have h := word 22 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide) 0 (by decide)
    rw [show (22+0 : ℕ) = 2*11 by decide] at h
    rw [valueBit_mul σ (by decide) (by decide), prime_value σ p2,
      prime_value σ p11, h2, zero_add] at h
    exact h
  have h13 : σ p13 = 0 := by
    have h := word 25 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide) 1 (by decide)
    rw [show (25+1 : ℕ) = 2*13 by decide] at h
    rw [valueBit_mul σ (by decide) (by decide), prime_value σ p2,
      prime_value σ p13, h2, zero_add] at h
    exact h
  have h17 : σ p17 = 0 := by
    have h := word 34 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide) 0 (by decide)
    rw [show (34+0 : ℕ) = 2*17 by decide] at h
    rw [valueBit_mul σ (by decide) (by decide), prime_value σ p2,
      prime_value σ p17, h2, zero_add] at h
    exact h
  have h23 : σ p23 = 0 := by
    have h := word 22 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide) 1 (by decide)
    rw [show (22+1 : ℕ) = 23 by decide, prime_value σ p23] at h
    exact h
  have h29 : σ p29 = 0 := by
    have h := word 28 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide) 1 (by decide)
    rw [show (28+1 : ℕ) = 29 by decide, prime_value σ p29] at h
    exact h
  have h31 : σ p31 = 0 := by
    have h := word 31 (by change _ ∈ ({22,25,28,31,34} : Finset ℕ); decide) 0 (by decide)
    rw [show (31+0 : ℕ) = 31 by decide, prime_value σ p31] at h
    exact h
  have hprimes : ∀ p : PrimeUpTo 36,
      p.val.val ∈ ({2,3,5,7,11,13,17,19,23,29,31} : Finset ℕ) := by
    decide +kernel
  intro p hnot
  have hp := hprimes p
  simp only [mem_insert, mem_singleton] at hp
  have transport (q : PrimeUpTo 36) (hv : p.val.val = q.val.val)
      (hz : σ q = 0) : σ p = 0 :=
    (congrArg σ (Subtype.ext (Fin.ext hv))).trans hz
  rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp
  all_goals first
    | exact transport p2 hp h2
    | exact transport p3 hp h3
    | exact transport p5 hp h5
    | exact transport p7 hp h7
    | exact transport p11 hp h11
    | exact transport p13 hp h13
    | exact transport p17 hp h17
    | exact transport p23 hp h23
    | exact transport p29 hp h29
    | exact transport p31 hp h31
    | exact False.elim (hnot (Subtype.ext (Fin.ext hp)))

theorem kernel_dimension :
    Module.finrank F₂ (LinearMap.ker (system 36 (ValuationPrimeCylinder.starts 18 3) 2)) = 1 := by
  let K := LinearMap.ker (system 36 (ValuationPrimeCylinder.starts 18 3) 2)
  let ev : K →ₗ[F₂] F₂ := (LinearMap.proj unusedPrimeExample).comp K.subtype
  have hi : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro σ hσ
    apply Subtype.ext
    funext p
    by_cases hp : p = unusedPrimeExample
    · subst p
      exact hσ
    · exact kernel_forced_bits σ.val σ.property p hp
  have hle := LinearMap.finrank_le_finrank_of_injective hi
  have hpos : 0 < Module.finrank F₂ K := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨OneNegativePrime.sample unusedPrimeExample,
      unused_prime_in_ker unusedPrimeExample unused_prime_example⟩, ?_⟩
    intro hzero
    exact sample_ne_zero unusedPrimeExample (congrArg Subtype.val hzero)
  simp only [Module.finrank_self] at hle
  change Module.finrank F₂ K = 1
  omega

theorem exact_rank : retainedRank 18 3 = 10 := by
  have hdim := (system 36 (ValuationPrimeCylinder.starts 18 3) 2).finrank_range_add_finrank_ker
  rw [kernel_dimension, Module.finrank_fintype_fun_eq_card,
    PrimeCylinderSize.prime_card] at hdim
  have hp : primeCount 36 = 11 := prime_count_example
  change rank 36 (ValuationPrimeCylinder.starts 18 3) 2 + 1 = primeCount 36 at hdim
  change rank 36 (ValuationPrimeCylinder.starts 18 3) 2 = 10
  omega

theorem exact_forcing_probability :
    uniformSolutionMass (system 36 (ValuationPrimeCylinder.starts 18 3) 2)
      (rhs (ValuationPrimeCylinder.starts 18 3) 2) = (1024 : ℝ)⁻¹ := by
  have h := retained_forcing_mass (by decide : Nat.Prime 3) (by decide : 3≤18)
  rw [exact_rank] at h
  norm_num at h ⊢
  exact h

theorem forcing_solution_count :
    Nat.card (Solution (system 36 (ValuationPrimeCylinder.starts 18 3) 2)
      (rhs (ValuationPrimeCylinder.starts 18 3) 2)) = 2 := by
  have h := card_solution_eq_pow_finrank_of_compatible
    (system 36 (ValuationPrimeCylinder.starts 18 3) 2)
    (rhs (ValuationPrimeCylinder.starts 18 3) 2)
    (retained_compatible (by decide : Nat.Prime 3) (by decide : 3≤18))
  simpa only [← Nat.card_eq_fintype_card, kernel_dimension, pow_one] using h

end PaperP1.ExactRankPrimeCylinderExample
