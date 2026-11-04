module

public import PaperP1.Model.EffectiveCompressedPrimitivePopulation
public import PaperP1.Model.PairCompressedPrimitiveTransport

/-! # Exact unordered transport with arbitrary effective dyadic targets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveCompressedPrimitiveTransport

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.PairCompressedPrimitiveFamilies PaperP1.EffectiveCompressedPrimitivePopulation
  PaperP1.FiniteFamilyEnumeration

theorem finite_mass_bound {N a b L t : ℕ} (P : Finset ((ℕ × ℕ) × Finset ℕ))
    (hP : ∀ p ∈ P, p.1 ∈ PaperP1.FixedChannelSourceGeometry.unitSources N a b L ∧
      p.2 ⊆ dyadicBlock N ∧ p.2.card = t ∧
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
    apply PairCompressedPrimitiveTransport.indexed_primitive _ _ (centres_injective _ _)
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

end PaperP1.EffectiveCompressedPrimitiveTransport
