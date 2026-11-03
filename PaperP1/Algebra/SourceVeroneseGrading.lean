module

public import PaperP1.Algebra.GradedVeroneseGrading
public import PaperP1.Algebra.HomogeneousSplitRadicalVeronese
public import PaperP1.Algebra.HomogeneousSplitRadicalFiniteVeronese
public import PaperP1.Algebra.StandardBaseVeronese

/-! # The actual standard base and source Veronese algebras are graded and generated in degree one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseGrading

open Finset PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalVeronese PaperP1.HomogeneousSplitRadicalFiniteVeronese
  PaperP1.StandardBaseVeronese

attribute [local instance] MvPolynomial.gradedAlgebra

def nativePiece (F : Type*) [Field F] (D n : ℕ) : Submodule F (nativeVeronese F D) :=
  (MvPolynomial.homogeneousSubmodule (Fin 3) F (n * D)).comap (nativeVeronese F D).val.toLinearMap

@[instance_reducible] def nativeGrading (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) :
    GradedAlgebra (nativePiece F D) :=
  GradedVeroneseGrading.grading (MvPolynomial.homogeneousSubmodule (Fin 3) F) D hD

theorem native_generated_degree_one (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) :
    Algebra.adjoin F (nativePiece F D 1 : Set (nativeVeronese F D)) = ⊤ := by
  apply GradedVeroneseGrading.adjoin_piece_one_eq_top
  rw [← nativeVeronese, nativeVeronese_eq_adjoin F D hD, adjoin_monomials_eq]
  congr 1

def sourcePiece {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (n : ℕ) :
    Submodule F (veronese c D I J) :=
  (HomogeneousSplitRadicalGrading.piece c D I J (n * D)).comap (veronese c D I J).val.toLinearMap

@[instance_reducible] def sourceGrading {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D) :
    GradedAlgebra (sourcePiece c D I J) := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  exact GradedVeroneseGrading.grading (HomogeneousSplitRadicalGrading.piece c D I J) D hD

def sourceGenerator {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
    (p : SplitWeightedDegreeGenerators.generators F ι D) : veronese c D I J := by
  refine ⟨quotientMap c D I J p, ?_⟩
  rw [veronese_eq_image]
  have hp : MvPolynomial.IsWeightedHomogeneous (weight ι D) (p : WeightedPolynomial F ι) (1 * D) := by
    simpa only [one_mul] using SplitWeightedDegreeGenerators.generator_homogeneous D p.property
  exact Algebra.subset_adjoin ⟨1, p, hp, rfl⟩

theorem sourceGenerator_mem_one {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (p : SplitWeightedDegreeGenerators.generators F ι D) :
    sourceGenerator c D I J p ∈ sourcePiece c D I J 1 := by
  change quotientMap c D I J (p : WeightedPolynomial F ι) ∈ HomogeneousSplitRadicalGrading.piece c D I J (1 * D)
  rw [one_mul]
  exact Submodule.mem_map.mpr ⟨p, SplitWeightedDegreeGenerators.generator_homogeneous D p.property, rfl⟩

theorem source_radical_mem_one {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (i : ι) :
    radical c D I J i ∈ sourcePiece c D I J 1 := by
  change quotientMap c D I J (MvPolynomial.X (Sum.inr i)) ∈ HomogeneousSplitRadicalGrading.piece c D I J (1 * D)
  rw [one_mul]
  exact Submodule.mem_map.mpr ⟨MvPolynomial.X (Sum.inr i), radical_variable_homogeneous F ι D i, rfl⟩

theorem source_generated_degree_one {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D) :
    Algebra.adjoin F (sourcePiece c D I J 1 : Set (veronese c D I J)) = ⊤ := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  exact GradedVeroneseGrading.adjoin_piece_one_eq_top (HomogeneousSplitRadicalGrading.piece c D I J) D
    (generated_in_degreeD c D hD I J)

theorem source_piece_zero_iff {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (hD : 0 < D) (I J : ι → Finset ℤ) (x : veronese c D I J) :
    x ∈ sourcePiece c D I J 0 ↔ ∃ a : F, algebraMap F (veronese c D I J) a = x := by
  change (x : CoordinateRing c D I J) ∈ HomogeneousSplitRadicalGrading.piece c D I J (0 * D) ↔ _
  rw [zero_mul, HomogeneousSplitRadicalGrading.piece_zero_iff c D hD I J]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩

end PaperP1.SourceVeroneseGrading
