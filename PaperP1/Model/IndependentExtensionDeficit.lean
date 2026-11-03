module

public import PaperP1.Arithmetic.IntersectionExceptional
public import PaperP1.Affine.CompressedBlocks
public import PaperP1.Model.MissingBlockProbabilities

/-! # Literal all-cardinality independent extensions have unordered exceptional seeds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentExtensionDeficit

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance independentExtensionDeficitPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def Direct (W : Submodule F₂ (ℕ →₀ F₂)) (L : ℕ) (A : Finset ℕ) : Prop :=
  Function.Injective (relationAddition (fun i : MinimalRelativeRelations.indices A ↦
    MinimalRelativeRelations.augmented W (fun x ↦ squareClassSpace x L) i.val))

def families (G : Finset ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun A ↦ ¬ Direct W L A

def deficit (G S : Finset ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (L : ℕ) (u : ℝ) : ℝ :=
  ∑ A ∈ families (G \ S) W L, u ^ A.card * ∏ x ∈ A, infiniteMarginal x L

theorem mem_families (G : Finset ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (L : ℕ) (A : Finset ℕ) :
    A ∈ families G W L ↔ A ⊆ G ∧ ¬ Direct W L A := by
  classical
  simp only [families, mem_filter, mem_powerset]

theorem direct_iff_nullity (W : Submodule F₂ (ℕ →₀ F₂)) [Fintype W] (L : ℕ) (A : Finset ℕ) :
    Direct W L A ↔ MinimalRelativeRelations.nullity W (fun x ↦ squareClassSpace x L) A = 0 := by
  let : ∀ i, Fintype (MinimalRelativeRelations.augmented W (fun x ↦ squareClassSpace x L) i) := fun i ↦ by
    cases i with
    | none => exact inferInstanceAs (Fintype W)
    | some x => exact inferInstanceAs (Fintype (squareClassSpace x L))
  exact CompressedBlocks.direct_family_iff_zero_nullity
    (MinimalRelativeRelations.augmented W (fun x ↦ squareClassSpace x L)) (MinimalRelativeRelations.indices A)

theorem deficit_eq_product_weights (G S : Finset ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (L : ℕ) (u : ℝ) :
    deficit G S W L u = ∑ A ∈ families (G \ S) W L, ∏ x ∈ A, u * infiniteMarginal x L := by
  unfold deficit
  apply sum_congr rfl
  intro A _
  rw [prod_mul_distrib, prod_const]

theorem exists_exceptional_seed {N L : ℕ} (hN : 2 ≤ N) (G S : Finset ℕ)
    (hG : G ⊆ dyadicBlock N) (hS : S ⊆ dyadicBlock N)
    (W : Submodule F₂ (ℕ →₀ F₂))
    (hW : W ≤ ConditionalWindowRank.oldSpan (OldValuePrimeBudget.rawValues S L))
    (U : Finset ℕ) (hU : U ∈ families G W L) :
    ∃ A ⊆ U, ∃ x ∈ U, x ∉ A ∧
      x ∈ BranchingExceptional.badStarts N L (OldValuePrimeBudget.rawValues (S ∪ A) L) := by
  classical
  let : Fintype (ConditionalWindowRank.oldSpan (OldValuePrimeBudget.rawValues S L)) :=
    IntersectionExceptional.oldSpanFintype _
  let : Fintype W := Fintype.ofInjective (Submodule.inclusion hW) (Submodule.inclusion_injective hW)
  obtain ⟨hUG, hnot⟩ := (mem_families G W L U).mp hU
  have hpos : 0 < MinimalRelativeRelations.nullity W (fun x ↦ squareClassSpace x L) U :=
    Nat.pos_of_ne_zero (fun hz ↦ hnot ((direct_iff_nullity W L U).mpr hz))
  obtain ⟨J, hJU, hJne, hJpos, hproper⟩ :=
    MinimalRelativeRelations.exists_minimal W (fun x ↦ squareClassSpace x L) U hpos
  obtain ⟨v, hvne, hvsum⟩ :=
    MinimalRelativeRelations.exists_relation W (fun x ↦ squareClassSpace x L) J hJpos hproper
  obtain ⟨x, hxJ⟩ := hJne
  let j : J := ⟨x, hxJ⟩
  let A := J.erase x
  let R := OldValuePrimeBudget.rawValues (S ∪ A) L
  have hpositive : ∀ y ∈ S ∪ A, 0 < y := by
    intro y hy
    have hyN : y ∈ dyadicBlock N := by
      rcases mem_union.mp hy with hy | hy
      · exact hS hy
      · exact hG (hUG (hJU (erase_subset x J hy)))
    have h := (mem_Ico.mp hyN).1
    omega
  have hsource : W ≤ ConditionalWindowRank.oldSpan R :=
    hW.trans (IntersectionExceptional.oldSpan_mono (by
      intro n hn
      obtain ⟨y, hy, hn⟩ := mem_biUnion.mp hn
      exact mem_biUnion.mpr ⟨y, mem_union_left _ hy, hn⟩))
  have hrest : (∑ i : {i : J // i ≠ j}, (v i.val).val) ∈ ConditionalWindowRank.oldSpan R := by
    apply Submodule.sum_mem
    intro i _
    have hi : i.val.val ∈ A := mem_erase.mpr ⟨(fun heq ↦ i.property (Subtype.ext heq)), i.val.property⟩
    exact (SubspaceFamilyRank.local_le_span (fun y ↦ squareClassSpace y L) (S ∪ A)
      (mem_union_right _ hi)).trans (IntersectionExceptional.span_le_raw (S ∪ A) L hpositive) (v i.val).property
  have hsum := Fintype.sum_eq_add_sum_subtype_ne (fun i : J ↦ (v i).val) j
  have hintersection : (v j).val ∈ ConditionalWindowRank.oldSpan R := by
    have heq : (v j).val = (∑ i : J, (v i).val) - ∑ i : {i : J // i ≠ j}, (v i.val).val := by
      rw [hsum]
      abel
    rw [heq]
    exact Submodule.sub_mem _ (hsource hvsum) hrest
  refine ⟨A, (erase_subset x J).trans hJU, x, hJU hxJ, notMem_erase x J, ?_⟩
  exact IntersectionExceptional.of_intersection hN (hG (hUG (hJU hxJ)))
    (fun hz ↦ hvne j (Subtype.ext hz)) (v j).property hintersection

end PaperP1.IndependentExtensionDeficit
