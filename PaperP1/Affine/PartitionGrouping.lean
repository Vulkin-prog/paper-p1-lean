module

public import PaperP1.Affine.RelationPartitions

/-!
# Regrouping effective coefficients by finite partition parts

The regrouping is a linear equivalence. Its inverse uses the unique part of
each index. Sums over all effective coefficients are preserved exactly.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance partitionGroupingPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) (P : Finpartition (Finset.univ : Finset ι))

def groupCoefficients : ((i : ι) → S i) →ₗ[𝔽₂] ((C : P.parts) → (i : C.val) → S i.val) where
  toFun := fun s _C i => s i.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def ungroupCoefficients : ((C : P.parts) → (i : C.val) → S i.val) →ₗ[𝔽₂] ((i : ι) → S i) where
  toFun := fun w i =>
    w ⟨P.part i, P.part_mem.mpr (Finset.mem_univ i)⟩ ⟨i, P.mem_part (Finset.mem_univ i)⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem ungroup_groupCoefficients (s : (i : ι) → S i) :
    ungroupCoefficients S P (groupCoefficients S P s) = s := rfl

theorem group_ungroupCoefficients (w : (C : P.parts) → (i : C.val) → S i.val) :
    groupCoefficients S P (ungroupCoefficients S P w) = w := by
  funext C i
  rcases C with ⟨C, hC⟩
  rcases i with ⟨i, hi⟩
  have hpart := P.part_eq_of_mem hC hi
  subst C
  rfl

def groupCoefficientsEquiv : ((i : ι) → S i) ≃ₗ[𝔽₂] ((C : P.parts) → (i : C.val) → S i.val) :=
  LinearEquiv.ofBijective (groupCoefficients S P) ⟨by
    intro s t h
    have hh := congrArg (ungroupCoefficients S P) h
    simpa only [ungroup_groupCoefficients] using hh,
    fun w => ⟨ungroupCoefficients S P w, group_ungroupCoefficients S P w⟩⟩

omit [Module 𝔽₂ U] in
theorem partition_sum (f : ι → U) : (∑ C : P.parts, ∑ i ∈ C.val, f i) = ∑ i, f i := by
  have hsum : (∑ C : P.parts, ∑ i ∈ C.val, f i) = ∑ C ∈ P.parts, ∑ i ∈ C, f i := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach P.parts (fun C : Finset ι => ∑ i ∈ C, f i)
  rw [hsum]
  rw [← Finset.sum_biUnion (by
    intro C hC D hD hne
    exact P.disjoint hC hD hne)]
  change (∑ i ∈ P.parts.biUnion id, f i) = _
  rw [P.biUnion_parts]

theorem groupCoefficients_part_sum (s : (i : ι) → S i) (C : P.parts) :
    relationAddition (fun i : C.val => S i.val) (groupCoefficients S P s C) =
      ∑ i ∈ C.val, (s i).val := by
  change (∑ i : C.val, (s i.val).val) = _
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach C.val (fun i => (s i).val)

theorem groupCoefficients_total_sum (s : (i : ι) → S i) :
    (∑ C : P.parts,
      relationAddition (fun i : C.val => S i.val) (groupCoefficients S P s C)) =
      relationAddition S s := by
  simp_rw [groupCoefficients_part_sum]
  exact partition_sum P (fun i => (s i).val)

theorem partition_prod {R : Type*} [CommMonoid R] (f : ι → R) :
    (∏ C : P.parts, ∏ i ∈ C.val, f i) = ∏ i, f i := by
  have hprod : (∏ C : P.parts, ∏ i ∈ C.val, f i) = ∏ C ∈ P.parts, ∏ i ∈ C, f i := by
    rw [Finset.univ_eq_attach]
    exact Finset.prod_attach P.parts (fun C : Finset ι => ∏ i ∈ C, f i)
  rw [hprod, ← Finset.prod_biUnion (by
    intro C hC D hD hne
    exact P.disjoint hC hD hne)]
  change (∏ i ∈ P.parts.biUnion id, f i) = _
  rw [P.biUnion_parts]

theorem partition_prod_subtype {R : Type*} [CommMonoid R] (f : ι → R) :
    (∏ C : P.parts, ∏ i : C.val, f i.val) = ∏ i, f i := by
  calc
    _ = ∏ C : P.parts, ∏ i ∈ C.val, f i := by
      apply Finset.prod_congr rfl
      intro C _
      rw [Finset.univ_eq_attach]
      exact Finset.prod_attach C.val f
    _ = _ := partition_prod P f

end PaperP1.Affine
