module

public import PaperP1.Affine.Characters
public import PaperP1.Affine.RealProbability
public import PaperP1.Affine.Relations
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Full-support centered Fourier expansion on effective dual spaces

Each block is an actual dual subspace, with a compatible affine prescription
given by a local solution. All marginals retain their individual effective
dimensions. The product expansion removes the zero frequency separately in
every block, without imposing independence on the blocks.

The finite sum splitting and character-product induction follow the elementary
patterns in PaperCPrel8/CenteredAffineBlocks.lean at Paper C commit
b9fa9ba490f201b408a302a86f1594ee620b228b (Apache-2.0). The development here uses
effective spaces and their actual marginals rather than nominal row counts.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Affine

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V]

def effectiveIndicator (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a v : V) : ℝ :=
  if effectiveEvent S a v then 1 else 0

def effectiveRate (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] : ℝ :=
  (Fintype.card S : ℝ)⁻¹

def nonzeroCharacterTerm (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂))
    (a : V) (s : S) (v : V) : ℝ :=
  if s = 0 then 0 else realCharacter s.val a * realCharacter s.val v

theorem centered_effective_indicator
    (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] (a v : V) :
    effectiveIndicator S a v - effectiveRate S =
      effectiveRate S * ∑ s : S, nonzeroCharacterTerm S a s v := by
  classical
  let f : S → ℝ := fun s => realCharacter s.val a * realCharacter s.val v
  have hzero : f 0 = 1 := by simp [f]
  have hsum : (∑ s, f s) = 1 + ∑ s, nonzeroCharacterTerm S a s v := by
    calc
      _ = ∑ s, ((if s = 0 then f s else 0) + (if s = 0 then 0 else f s)) := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases h : s = 0 <;> simp [h]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hzero]
        rfl
  have hi := effective_indicator_expansion S a v
  change effectiveIndicator S a v = effectiveRate S * ∑ s, f s at hi
  rw [hsum] at hi
  rw [hi]
  ring1

variable [Fintype ι] [DecidableEq ι]

theorem realCharacter_sum (f : ι → V →ₗ[𝔽₂] 𝔽₂) (v : V) :
    (∏ i, realCharacter (f i) v) = realCharacter (∑ i, f i) v := by
  have h (I : Finset ι) :
      (∏ i ∈ I, realCharacter (f i) v) = realCharacter (∑ i ∈ I, f i) v := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, realCharacter_add]
  exact h Finset.univ

variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

def affineTupleSign (a : ι → V) (s : (i : ι) → S i) : ℝ :=
  ∏ i, realCharacter (s i).val (a i)

omit [∀ i, Fintype (S i)] in
theorem effective_block_product (a : ι → V) (s : (i : ι) → S i) (v : V) :
    (∏ i, nonzeroCharacterTerm (S i) (a i) (s i) v) =
      if HasFullSupport S s then
        affineTupleSign S a s * realCharacter (relationAddition S s) v else 0 := by
  classical
  by_cases hs : HasFullSupport S s
  · rw [ite_eq_left hs]
    simp only [HasFullSupport] at hs
    simp only [nonzeroCharacterTerm, hs, ite_false, Finset.prod_mul_distrib,
      realCharacter_sum, affineTupleSign, relationAddition_apply]
  · rw [ite_eq_right hs]
    obtain ⟨i, hi⟩ : ∃ i, s i = 0 := by simpa [HasFullSupport] using hs
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [nonzeroCharacterTerm, hi])

theorem effective_centered_product (a : ι → V) (v : V) :
    (∏ i, (effectiveIndicator (S i) (a i) v - effectiveRate (S i))) =
      (∏ i, effectiveRate (S i)) *
        ∑ s : (i : ι) → S i,
          if HasFullSupport S s then
            affineTupleSign S a s * realCharacter (relationAddition S s) v else 0 := by
  simp_rw [centered_effective_indicator]
  rw [Finset.prod_mul_distrib, Fintype.prod_sum]
  simp_rw [effective_block_product]

theorem effective_full_support_formula [Fintype V] (a : ι → V) :
    finiteExpectation (uniformFiniteProbability V).weight
        (fun v => ∏ i, (effectiveIndicator (S i) (a i) v - effectiveRate (S i))) =
      (∏ i, effectiveRate (S i)) *
        ∑ s : (i : ι) → S i,
          if IsFullSupportRelation S s then affineTupleSign S a s else 0 := by
  classical
  simp_rw [effective_centered_product]
  rw [finiteExpectation_const_mul, finiteExpectation_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : HasFullSupport S s
  · simp_rw [ite_eq_left hs]
    rw [finiteExpectation_const_mul, uniform_character_expectation]
    simp only [IsFullSupportRelation, hs, true_and]
    split_ifs <;> simp
  · simp [hs, IsFullSupportRelation, finiteExpectation]

end PaperP1.Affine
