module

public import PaperP1.Affine.TwoTargetPrimitiveCut
public import PaperP1.Arithmetic.TwoTargetAdmissibleDensePairs
public import PaperP1.Model.PrimitiveWindowMass
public import PaperP1.Combinatorics.TwoTargetFamilyCover

/-! # Exact effective two-target data and heterogeneous weight for an actual primitive extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPrimitiveData

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections PaperP1.SubspaceFamilyRank PaperP1.FiniteFamilyEnumeration

local instance primitiveDataPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

def sourceSpace (E : Finset ℕ) (L : ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  span (fun x ↦ squareClassSpace x L) E

theorem source_enumeration {s : ℕ} (E : Finset ℕ) (L : ℕ) (hcard : E.card = s) :
    sourceSpace E L = ⨆ i, squareClassSpace (centres E hcard i) L := by
  apply le_antisymm
  · apply iSup_le
    intro v
    obtain ⟨i, hi⟩ := (enumeration E hcard).surjective v
    have hv : v.val = centres E hcard i := congrArg Subtype.val hi.symm
    rw [hv]
    exact le_iSup (fun i ↦ squareClassSpace (centres E hcard i) L) i
  · apply iSup_le
    intro i
    exact local_le_span (fun x ↦ squareClassSpace x L) E (enumeration E hcard i).property

theorem primitive_data {s y z L : ℕ} (E : Finset ℕ) (hcard : E.card = s) (hne : E.Nonempty)
    (hy : y ∉ E) (hz : z ∉ E) (hyz : y ≠ z)
    (hprim : ConnectedWindowFamilies.Primitive L (TwoTargetFamilyCover.family E (y, z))) :
    Disjoint (sourceSpace E L) (squareClassSpace y L) ∧
      Disjoint (sourceSpace E L) (squareClassSpace z L) ∧
      Disjoint (squareClassSpace y L) (squareClassSpace z L) ∧
      relativeNullityOn (fun x ↦ squareClassSpace x L) (TwoTargetFamilyCover.family E (y, z)) =
        Module.finrank F₂ (Kernel y z L (sourceSpace E L)) := by
  obtain ⟨hWY, hWZ, hYZ, hnull⟩ := TwoTargetPrimitiveCut.primitive_data
    (fun x ↦ squareClassSpace x L) E y z hy hz hyz hne hprim.2
  have hdeficit : relativeNullityOn (fun x ↦ squareClassSpace x L) (TwoTargetFamilyCover.family E (y, z)) =
      TwoTargetDensePairs.deficit (sourceSpace E L) y z L := hnull
  rw [TwoTargetDensePairs.deficit_eq_kernel (centres E hcard) L (sourceSpace E L)
    (source_enumeration E L hcard).le] at hdeficit
  exact ⟨hWY, hWZ, hYZ, hdeficit⟩

theorem weight_factor {s y z L : ℕ} (E : Finset ℕ) (hcard : E.card = s) (hne : E.Nonempty)
    (hy : y ∉ E) (hz : z ∉ E) (hyz : y ≠ z)
    (hprim : ConnectedWindowFamilies.Primitive L (TwoTargetFamilyCover.family E (y, z))) :
    PrimitiveWindowMass.weight L (TwoTargetFamilyCover.family E (y, z)) =
      (∏ x ∈ E, infiniteMarginal x L) *
        (infiniteMarginal y L * infiniteMarginal z L *
          (2 ^ Module.finrank F₂ (Kernel y z L (sourceSpace E L)) : ℝ)) := by
  have hnull := (primitive_data E hcard hne hy hz hyz hprim).2.2.2
  unfold PrimitiveWindowMass.weight
  rw [hnull]
  change (∏ x ∈ insert y (insert z E), infiniteMarginal x L) * _ = _
  rw [prod_insert (by simp only [mem_insert, not_or]; exact ⟨hyz, hy⟩), prod_insert hz]
  ring

theorem source_product_cap (E : Finset ℕ) (L : ℕ) (B : ℝ)
    (hcap : ∀ x ∈ E, infiniteMarginal x L ≤ B) :
    (∏ x ∈ E, infiniteMarginal x L) ≤ B ^ E.card := by
  calc
    _ ≤ ∏ _x ∈ E, B := prod_le_prod₀
      (fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) hcap
    _ = _ := by simp

end PaperP1.TwoTargetPrimitiveData
