module

public import PaperP1.Algebra.HomogeneousSplitRadicalVeronese
public import PaperP1.Algebra.SplitBaseVeronese
public import PaperP1.Algebra.FiniteQuadraticSubalgebra

/-! # The actual source Veronese inclusion over its pure base algebra is finite -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalFiniteVeronese

open Finset PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalVeronese PaperP1.HomogeneousSplitRadicalPolynomials

def quotientMap {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    WeightedPolynomial F ι →ₐ[F] CoordinateRing c D I J := Ideal.Quotient.mkₐ F (relationIdeal c D I J)

def base {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    Subalgebra F (CoordinateRing c D I J) := SplitBaseVeronese.baseAlgebra D (quotientMap c D I J)

theorem base_le_veronese {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) : base c D I J ≤ veronese c D I J := by
  apply Algebra.adjoin_le
  rintro _ ⟨p, hp, rfl⟩
  rw [veronese_eq_image]
  exact Algebra.subset_adjoin ⟨1, p, by simpa only [one_mul] using
    SplitWeightedDegreeGenerators.generator_homogeneous D (Or.inl hp), rfl⟩

theorem radical_mem_veronese {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (i : ι) :
    quotientMap c D I J (MvPolynomial.X (Sum.inr i)) ∈ veronese c D I J := by
  rw [veronese_eq_image]
  have hp : MvPolynomial.IsWeightedHomogeneous (weight ι D)
      (MvPolynomial.X (Sum.inr i) : WeightedPolynomial F ι) (1 * D) := by
    simpa only [one_mul] using (radical_variable_homogeneous F ι D i)
  exact Algebra.subset_adjoin ⟨1, MvPolynomial.X (Sum.inr i), hp, rfl⟩

def radical {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (i : ι) :
    veronese c D I J := ⟨quotientMap c D I J (MvPolynomial.X (Sum.inr i)), radical_mem_veronese c D I J i⟩

def baseMap {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    base c D I J →+* veronese c D I J := (Subalgebra.inclusion (base_le_veronese c D I J)).toRingHom

theorem radical_square {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (i : ι) :
    (radical c D I J i : CoordinateRing c D I J) ^ 2 =
      quotientMap c D I J (MvPolynomial.rename Sum.inl
        (nativeRadicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))) := by
  have hh : quotientMap c D I J (relation (c i) D (I i) (J i) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  change quotientMap c D I J (MvPolynomial.X (Sum.inr i)) ^ 2 = _
  simpa only [relation, map_sub, map_pow, sub_eq_zero] using hh

theorem relative_generators {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (hD : 0 < D) (I J : ι → Finset ℤ) :
    veronese c D I J = Algebra.adjoin F ((base c D I J : Set (CoordinateRing c D I J)) ∪
      Set.range (fun i ↦ (radical c D I J i : CoordinateRing c D I J))) := by
  apply le_antisymm
  · apply (generated_by_source_generators c D hD I J).le.trans
    apply Algebra.adjoin_le
    rintro _ ⟨p, hp, rfl⟩
    rcases hp with hp | ⟨i, rfl⟩
    · exact Algebra.subset_adjoin (Or.inl (Algebra.subset_adjoin ⟨p, hp, rfl⟩))
    · exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  · apply Algebra.adjoin_le
    rintro _ (hp | ⟨i, rfl⟩)
    · exact base_le_veronese c D I J hp
    · exact (radical c D I J i).property

theorem baseMap_finite {F ι : Type*} [Field F] [Finite ι]
    (c : ι → F) (D : ℕ) (hD : 0 < D) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) : (baseMap c D I J).Finite := by
  apply FiniteQuadraticSubalgebra.finite_inclusion (base c D I J) (veronese c D I J)
    (base_le_veronese c D I J) (radical c D I J) (relative_generators c D hD I J)
  intro i
  rw [radical_square]
  exact SplitBaseVeronese.radicand_image_mem D hD (quotientMap c D I J) (c i) (I i) (J i) (hdeg i)

end PaperP1.HomogeneousSplitRadicalFiniteVeronese
