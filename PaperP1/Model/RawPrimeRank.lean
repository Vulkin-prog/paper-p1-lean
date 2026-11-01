module

public import PaperP1.Arithmetic.OldValuePrimeBudget
public import PaperP1.Affine.StartCharacterSpace
public import PaperP1.Algebra.SubspaceFamilyRank

/-! # Actual run-character ranks are bounded by their actual raw prime support -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawPrimeRank

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine
  PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget
  PaperP1.SubspaceFamilyRank

local instance rawPrimeRankTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def coordinates (R : Finset ℕ) : oldSpan R →ₗ[F₂] (oldPrimes R → F₂) where
  toFun v p := v.val p.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinates_injective (R : Finset ℕ) : Function.Injective (coordinates R) := by
  intro v w h
  apply Subtype.ext
  ext p
  by_cases hp : p ∈ oldPrimes R
  · exact congrFun h (⟨p, hp⟩ : oldPrimes R)
  · rw [oldSpan_coordinate_zero hp v.property, oldSpan_coordinate_zero hp w.property]

theorem oldSpan_rank_le (R : Finset ℕ) : Module.finrank F₂ (oldSpan R) ≤ (oldPrimes R).card := by
  have h := LinearMap.finrank_le_finrank_of_injective (coordinates_injective R)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h

theorem squareClass_le_raw {A : Finset ℕ} {x L : ℕ} (hx : x ∈ A) (hxpos : 0 < x) :
    squareClassSpace x L ≤ oldSpan (rawValues A L) := by
  rintro c ⟨w, rfl⟩
  change vertexParityMap x L w.val ∈ oldSpan (rawValues A L)
  rw [vertexParityMap_apply]
  apply Submodule.sum_mem
  intro v _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨startCompleteVertexLabel x L v, ?_, rfl⟩
  apply mem_biUnion.mpr
  refine ⟨x, hx, mem_Ico.mpr ?_⟩
  exact (exists_vertex_iff_in_window hxpos).mp ⟨v, rfl⟩

theorem rowSpace_le_raw {A : Finset ℕ} {M x L : ℕ} (hx : x ∈ A) (hxpos : 0 < x) :
    effectiveRowSpace (startSystem M x L) ≤
      (oldSpan (rawValues A L)).map (parityPairing M) := by
  rw [effectiveRowSpace_eq_map_squareClassSpace]
  exact Submodule.map_mono (squareClass_le_raw hx hxpos)

theorem family_rank_le (M L : ℕ) (A : Finset ℕ) (hA : ∀ x ∈ A, 0 < x) :
    rank (fun x ↦ effectiveRowSpace (startSystem M x L)) A ≤
      (oldPrimes (rawValues A L)).card := by
  have hspan : span (fun x ↦ effectiveRowSpace (startSystem M x L)) A ≤
      (oldSpan (rawValues A L)).map (parityPairing M) := by
    refine iSup_le fun x ↦ ?_
    exact rowSpace_le_raw x.property (hA x.val x.property)
  calc
    _ ≤ Module.finrank F₂ ((oldSpan (rawValues A L)).map (parityPairing M)) :=
      Submodule.finrank_mono hspan
    _ ≤ Module.finrank F₂ (oldSpan (rawValues A L)) := Submodule.finrank_map_le _ _
    _ ≤ _ := oldSpan_rank_le _

end PaperP1.RawPrimeRank
