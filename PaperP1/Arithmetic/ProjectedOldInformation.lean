module

public import PaperP1.Arithmetic.MaskedParityRank

/-! # Old even values and any discarded prime bits give the same finite rank upper bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectedOldInformation

open Finset PaperP1.Arithmetic PaperP1.MaskedParityRank

local instance projectedOldPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def primeSpan (Q : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  Submodule.span F₂ ((fun p ↦ Finsupp.single p (1 : F₂)) '' (Q : Set ℕ))

instance primeSpan_finite (Q : Finset ℕ) : FiniteDimensional F₂ (primeSpan Q) :=
  FiniteDimensional.span_of_finite _ (Q.finite_toSet.image _)

theorem primeSpan_empty : primeSpan ∅ = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, _⟩
    simp at hp
  · exact bot_le

theorem project_single_zero {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) :
    project P (Finsupp.single p (1 : F₂)) = 0 := by
  funext q
  by_cases hq : q ∈ P
  · simp only [project, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hq, Pi.zero_apply]
  · have hqp : q ≠ p := fun heq ↦ hq (heq ▸ hp)
    simp only [project, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hq, Finsupp.single_eq_of_ne hqp,
      Pi.zero_apply]

theorem primeSpan_le_project_kernel {P Q : Finset ℕ} (hQP : Q ⊆ P) : primeSpan Q ≤ LinearMap.ker (project P) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  exact LinearMap.mem_ker.mpr (project_single_zero (hQP hp))

theorem old_even_le_projected_span (P S : Finset ℕ) :
    FiniteEvenSquareClasses.space S ≤
      (FiniteSetValueSpan.span (K := F₂) (data P) S).comap (project P) := by
  intro v hv
  have hmap : project P v ∈ (FiniteEvenSquareClasses.space S).map (project P) := ⟨v, hv, rfl⟩
  rw [← evenSpace_eq_map] at hmap
  exact FiniteSetValueSpan.evenSpace_le_span (K := F₂) (data P) S hmap

theorem old_information_le_projected_span {P Q : Finset ℕ} (hQP : Q ⊆ P) (S : Finset ℕ) :
    FiniteEvenSquareClasses.space S ⊔ primeSpan Q ≤
      (FiniteSetValueSpan.span (K := F₂) (data P) S).comap (project P) := by
  apply sup_le (old_even_le_projected_span P S)
  intro v hv
  have hzero := LinearMap.mem_ker.mp (primeSpan_le_project_kernel hQP hv)
  change project P v ∈ FiniteSetValueSpan.span (K := F₂) (data P) S
  rw [hzero]
  exact Submodule.zero_mem _

theorem relative_kernel_le_masked {P Q : Finset ℕ} (hQP : Q ⊆ P) (S T : Finset ℕ) :
    (FiniteEvenSquareClasses.space S ⊔ primeSpan Q).comap
      (EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data T)) ≤
      MaskedParityRank.relativeKernel P S T := by
  intro w hw
  have hproject := old_information_le_projected_span hQP S hw
  change (EvenImage.evenMap (K := F₂) (FiniteSetValueSpan.data (data P) T)) w ∈
    FiniteSetValueSpan.span (K := F₂) (data P) S
  change project P (EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data T) w) ∈
    FiniteSetValueSpan.span (K := F₂) (data P) S at hproject
  have hmap := EvenImageMap.evenMap_map (project P) (FiniteEvenSquareClasses.data T)
  change EvenImage.evenMap (K := F₂) (FiniteSetValueSpan.data (data P) T) =
    (project P).comp (EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data T)) at hmap
  rw [hmap]
  exact hproject

theorem matches_add_residual {P Q : Finset ℕ} (hQP : Q ⊆ P) (S T : Finset ℕ) :
    Module.finrank F₂ ((FiniteEvenSquareClasses.space S ⊔ primeSpan Q).comap
      (EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data T))) ≤
      (S ∩ T).card + Module.finrank F₂ (CoverGraphResolution.rowSolutions (PrimeRowComponents.rows (S ∪ T) P)) :=
  (Submodule.finrank_mono (relative_kernel_le_masked hQP S T)).trans (MaskedParityRank.matches_add_residual P S T)

end PaperP1.ProjectedOldInformation
