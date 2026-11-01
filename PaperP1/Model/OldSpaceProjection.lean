module

public import PaperP1.Model.ParityCharacters
public import PaperP1.Affine.ProjectionHolder
public import PaperP1.Algebra.FiniteSetValueSpan
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The actual old square-class span and its finite-cylinder character image -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OldSpaceProjection

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def oldSpace (O : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  PaperP1.FiniteSetValueSpan.span (K := F₂) parityVec O

instance oldSpace_finiteDimensional (O : Finset ℕ) : FiniteDimensional F₂ (oldSpace O) := by
  unfold oldSpace
  infer_instance

def characterSpace (M : ℕ) (O : Finset ℕ) : Submodule F₂ (SampleSpace M →ₗ[F₂] F₂) :=
  (oldSpace O).map (parityPairing M)

instance characterSpace_finite (M : ℕ) (O : Finset ℕ) : Finite (characterSpace M O) := by
  let _ : Finite (SampleSpace M →ₗ[F₂] F₂) :=
    Finite.of_injective (fun f : SampleSpace M →ₗ[F₂] F₂ ↦ (f : SampleSpace M → F₂)) DFunLike.coe_injective
  exact Finite.of_injective (fun u : characterSpace M O ↦ u.val) Subtype.val_injective

instance characterSpace_fintype (M : ℕ) (O : Finset ℕ) : Fintype (characterSpace M O) := Fintype.ofFinite _

theorem oldSpace_rank_le (O : Finset ℕ) : Module.finrank F₂ (oldSpace O) ≤ O.card :=
  PaperP1.FiniteSetValueSpan.rank_le_card parityVec O

theorem characterSpace_rank_le (M : ℕ) (O : Finset ℕ) :
    Module.finrank F₂ (characterSpace M O) ≤ O.card :=
  (Submodule.finrank_map_le (parityPairing M) (oldSpace O)).trans (oldSpace_rank_le O)

theorem characterSpace_card_le (M : ℕ) (O : Finset ℕ) :
    Fintype.card (characterSpace M O) ≤ 2 ^ O.card := by
  rw [card_eq_two_pow_finrank]
  exact Nat.pow_le_pow_right (by norm_num) (characterSpace_rank_le M O)

theorem oldSpace_le_bounded (M : ℕ) (O : Finset ℕ) (hO : ∀ n ∈ O, n ≤ M) :
    oldSpace O ≤ boundedPrimeParity M := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, hn, rfl⟩
  exact parityVec_mem_boundedPrimeParity (hO n hn)

theorem mem_characterSpace_iff (M : ℕ) (O : Finset ℕ) (hO : ∀ n ∈ O, n ≤ M)
    (w : ℕ →₀ F₂) (hw : w ∈ boundedPrimeParity M) :
    parityPairing M w ∈ characterSpace M O ↔ w ∈ oldSpace O := by
  constructor
  · intro h
    obtain ⟨u, hu, heq⟩ := Submodule.mem_map.mp h
    have huw := parityPairing_injOn_bounded M (oldSpace_le_bounded M O hO hu) hw heq
    exact huw ▸ hu
  · intro h
    exact Submodule.mem_map.mpr ⟨w, h, rfl⟩

theorem sum_valueLinear_mem_iff {ι : Type*} [Fintype ι]
    (M : ℕ) (O : Finset ℕ) (hO : ∀ n ∈ O, n ≤ M) (X : ι → ℕ) (hX : ∀ i, X i ≤ M) :
    (∑ i, valueLinear M (X i)) ∈ characterSpace M O ↔
      (∑ i, parityVec (X i)) ∈ oldSpace O := by
  have hmap : parityPairing M (∑ i, parityVec (X i)) = ∑ i, valueLinear M (X i) := by
    rw [map_sum]
    simp only [parityPairing_parityVec]
  rw [← hmap]
  apply mem_characterSpace_iff M O hO
  exact Submodule.sum_mem _ fun i _ ↦ parityVec_mem_boundedPrimeParity (hX i)

end PaperP1.OldSpaceProjection
