module

public import PaperP1.Algebra.EvenImage

/-! # Full and zero-sum images of an arbitrary map on actual finite sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSetValueSpan

open Finset

variable {K V E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]

def data (f : V → E) (S : Finset V) : S → E := fun v ↦ f v.val

def span (f : V → E) (S : Finset V) : Submodule K E := Submodule.span K (f '' (S : Set V))

def fullMap (f : V → E) (S : Finset V) : (S → K) →ₗ[K] E := EvenImage.combination (data f S)

def valueKernel (f : V → E) (S : Finset V) : Submodule K (S → K) := LinearMap.ker (fullMap (K := K) f S)

def evenSpace (f : V → E) (S : Finset V) : Submodule K E := EvenImage.image (data f S)

instance span_finite (f : V → E) (S : Finset V) : FiniteDimensional K (span (K := K) f S) :=
  FiniteDimensional.span_of_finite _ (S.finite_toSet.image f)

instance evenSpace_finite (f : V → E) (S : Finset V) : FiniteDimensional K (evenSpace (K := K) f S) := by
  change FiniteDimensional K (LinearMap.range (EvenImage.evenMap (K := K) (data f S)))
  infer_instance

theorem span_eq_range (f : V → E) (S : Finset V) : span (K := K) f S = LinearMap.range (fullMap (K := K) f S) := by
  rw [span, fullMap, EvenImage.combination, Fintype.range_linearCombination]
  congr 1
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v.val, v.property, rfl⟩

theorem rank_add_kernel (f : V → E) (S : Finset V) :
    Module.finrank K (span (K := K) f S) + Module.finrank K (valueKernel (K := K) f S) = S.card := by
  have h := (fullMap (K := K) f S).finrank_range_add_finrank_ker
  rw [← span_eq_range, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  exact h

theorem rank_le_card (f : V → E) (S : Finset V) : Module.finrank K (span (K := K) f S) ≤ S.card := by
  have h := rank_add_kernel (K := K) f S
  omega

variable [DecidableEq V]

theorem span_union (f : V → E) (S T : Finset V) :
    span (K := K) f (S ∪ T) = span (K := K) f S ⊔ span (K := K) f T := by
  rw [span, coe_union, Set.image_union, Submodule.span_union]
  rfl

omit [DecidableEq V] in
theorem evenSpace_le_span (f : V → E) (S : Finset V) : evenSpace (K := K) f S ≤ span (K := K) f S := by
  intro z hz
  obtain ⟨w, _, hw⟩ := (EvenImage.mem_image_iff (K := K) (data f S) z).mp hz
  rw [span_eq_range]
  exact ⟨w, hw⟩

omit [DecidableEq V] in
theorem evenSpace_empty (f : V → E) : evenSpace (K := K) f ∅ = ⊥ := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w, _, hw⟩ := (EvenImage.mem_image_iff (K := K) (data f ∅) z).mp hz
    rw [EvenImage.combination_apply] at hw
    simpa using hw.symm
  · exact bot_le

omit [DecidableEq V] in
theorem span_le_even_sup_anchor (f : V → E) (S : Finset V) (a : V) (ha : a ∈ S) :
    span (K := K) f S ≤ evenSpace (K := K) f S ⊔ span (K := K) f {a} := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  have hdiff : f v - f a ∈ evenSpace (K := K) f S :=
    EvenImage.difference_mem (K := K) (data f S) (⟨v, hv⟩ : S) (⟨a, ha⟩ : S)
  have hanchor : f a ∈ span (K := K) f {a} := Submodule.subset_span ⟨a, mem_singleton_self a, rfl⟩
  exact Submodule.mem_sup.mpr ⟨f v - f a, hdiff, f a, hanchor, sub_add_cancel _ _⟩

theorem full_union_rank_le_old_even_add_one (f : V → E) (S T : Finset V) :
    Module.finrank K (span (K := K) f (S ∪ T)) ≤
      Module.finrank K ↥(span (K := K) f S ⊔ evenSpace (K := K) f T) + 1 := by
  by_cases hT : T.Nonempty
  · obtain ⟨a, ha⟩ := hT
    let J := span (K := K) f S ⊔ evenSpace (K := K) f T
    have hcover : span (K := K) f (S ∪ T) ≤ J ⊔ span (K := K) f {a} := by
      rw [span_union]
      apply sup_le
      · exact le_sup_of_le_left le_sup_left
      · exact (span_le_even_sup_anchor (K := K) f T a ha).trans (sup_le_sup le_sup_right le_rfl)
    have hmono := Submodule.finrank_mono hcover
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq J (span (K := K) f {a})
    have hanchor := rank_le_card (K := K) f {a}
    rw [card_singleton] at hanchor
    change Module.finrank K (span (K := K) f (S ∪ T)) ≤ Module.finrank K J + 1
    omega
  · have hempty := not_nonempty_iff_eq_empty.mp hT
    subst T
    rw [union_empty, evenSpace_empty, sup_bot_eq]
    omega

end PaperP1.FiniteSetValueSpan
