module

public import PaperP1.Model.PairCompressedPrimitivePopulation
public import PaperP1.Model.PairPrimitiveCompression
public import PaperP1.Affine.InjectiveNullityTransport

/-! # Unordered primitive compressed families enter the actual indexed population

The map enumerates only original target windows. Its injectivity is proved
by recovering their actual finite set; no choice of relation is counted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairCompressedPrimitiveTransport

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.SubspaceFamilyRank
  PaperP1.PairCompressedPrimitiveFamilies PaperP1.PairCompressedPrimitivePopulation
  PaperP1.FiniteFamilyEnumeration

local instance (P : Prop) : Decidable P := Classical.propDecidable P

local instance augmentedFintype (W : Submodule F₂ (ℕ →₀ F₂)) [Fintype W] (L : ℕ)
    (i : Option ℕ) : Fintype (MinimalRelativeRelations.augmented W (fun x ↦ squareClassSpace x L) i) := by
  cases i with
  | none => exact inferInstanceAs (Fintype W)
  | some x => exact inferInstanceAs (Fintype (squareClassSpace x L))

theorem indexed_primitive {t L : ℕ} (xy : ℕ × ℕ) (z : Fin t → ℕ)
    (hz : Function.Injective z)
    (hp : PairPrimitiveCompression.Primitive L {xy.1, xy.2} (tupleSet z)) :
    PairCompressedPrimitiveFamilies.Primitive xy L z := by
  let W := FixedPairExtensions.sourceSpace {xy.1, xy.2} L
  let S := MinimalRelativeRelations.augmented W (fun x ↦ squareClassSpace x L)
  let : Fintype W := MinimalRelativeRelations.spanFintype (fun x ↦ squareClassSpace x L) {xy.1, xy.2}
  let f : Fin (t + 1) → Option ℕ := Fin.cons none (fun i ↦ some (z i))
  have hf : Function.Injective f := Fin.cons_injective_of_injective
    (by rintro ⟨i, hi⟩; cases hi)
    (fun i j hij ↦ hz (Option.some.inj hij))
  have himage : univ.image f = MinimalRelativeRelations.indices (tupleSet z) := by
    ext x
    cases x <;> simp [f, MinimalRelativeRelations.indices, tupleSet, Fin.exists_fin_succ]
  have hspaces : (fun i ↦ S (f i)) = spaces xy L z := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact PaperP1.RetainedNullity.span_pair (fun x ↦ squareClassSpace x L) xy.1 xy.2
    · rfl
  have hnull (A : Finset (Fin (t + 1))) :
      relativeNullityOn (spaces xy L z) A = relativeNullityOn S (A.image f) := by
    rw [← hspaces]
    exact InjectiveNullityTransport.nullity_image S f hf A
  have hprim := (PairPrimitiveCompression.primitive_iff_augmented L {xy.1, xy.2} (tupleSet z) hp.1).mp hp
  refine ⟨?_, ?_⟩
  · change 0 < relativeNullityOn (spaces xy L z) univ
    rw [hnull, himage]
    exact hprim.1
  · intro J hJ
    rw [hnull]
    apply hprim.2
    rw [← himage]
    exact InjectiveNullityTransport.image_ssubset f hf hJ

theorem finite_mass_bound {N a b L t : ℕ} (P : Finset ((ℕ × ℕ) × Finset ℕ))
    (hP : ∀ p ∈ P, p.1 ∈ PaperP1.FixedChannelSourceGeometry.unitSources N a b L ∧
      p.2 ⊆ RegularStarts.regularStarts N L ∧ p.2.card = t ∧
      PairPrimitiveCompression.Primitive L {p.1.1, p.1.2} p.2) :
    (∑ p ∈ P, HomogeneousRunMass.probability L ({p.1.1, p.1.2} ∪ p.2)) ≤ mass N a b L t := by
  classical
  let f := fun p : P ↦ (p.val.1, centres p.val.2 (hP p.val p.property).2.2.1)
  have hset (p : P) : tupleSet (f p).2 = p.val.2 := centres_tupleSet _ _
  have hinj : Function.Injective f := by
    intro p q heq
    have hroot : p.val.1 = q.val.1 :=
      congrArg (fun u : (ℕ × ℕ) × (Fin t → ℕ) ↦ u.1) heq
    apply Subtype.ext
    exact Prod.ext hroot
      ((hset p).symm.trans ((congrArg (fun u : (ℕ × ℕ) × (Fin t → ℕ) ↦ tupleSet u.2) heq).trans (hset q)))
  have hmem (p : P) : f p ∈ points N a b L t := by
    have hd := hP p.val p.property
    apply mem_points.mpr
    refine ⟨hd.1, centres_mem _ _ _ hd.2.1, centres_injective _ _, ?_⟩
    apply indexed_primitive _ _ (centres_injective _ _)
    rw [hset]
    exact hd.2.2.2
  have hfamily (p : P) : family (f p).1 (f p).2 = {p.val.1.1, p.val.1.2} ∪ p.val.2 := by
    change {p.val.1.1, p.val.1.2} ∪ tupleSet (f p).2 = _
    rw [hset]
  have heq : (∑ q ∈ univ.image f, HomogeneousRunMass.probability L (family q.1 q.2)) =
      ∑ p ∈ P, HomogeneousRunMass.probability L ({p.1.1, p.1.2} ∪ p.2) := by
    rw [sum_image hinj.injOn]
    simp only [hfamily]
    exact sum_coe_sort P (fun p : (ℕ × ℕ) × Finset ℕ ↦
      HomogeneousRunMass.probability L ({p.1.1, p.1.2} ∪ p.2))
  rw [← heq]
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨p, _, rfl⟩ := mem_image.mp hq
    exact hmem p
  · intro q _ _
    exact (HomogeneousRunMass.probability_pos L _).le

end PaperP1.PairCompressedPrimitiveTransport
