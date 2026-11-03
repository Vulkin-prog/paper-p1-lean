module

public import PaperP1.Algebra.SplitBaseVeronese
public import PaperP1.Algebra.GradedVeroneseAlgebra

/-! # The pure base algebra is the literal image of the standard three-variable Veronese algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StandardBaseVeronese

open Finset PaperP1.HomogeneousSplitRadicalRelations PaperP1.SplitWeightedDegreeGenerators

def nativeMonomials (F : Type*) [Field F] (D : ℕ) : Set (MvPolynomial (Fin 3) F) :=
  {p | ∃ d : Fin 3 →₀ ℕ, d.degree = D ∧ MvPolynomial.monomial d 1 = p}

attribute [local instance] MvPolynomial.gradedAlgebra

def nativeVeronese (F : Type*) [Field F] (D : ℕ) : Subalgebra F (MvPolynomial (Fin 3) F) :=
  GradedVeroneseAlgebra.veronese (MvPolynomial.homogeneousSubmodule (Fin 3) F) D

theorem baseMonomials_eq_image (F ι : Type*) [Field F] (D : ℕ) :
    baseMonomials F ι D = (MvPolynomial.rename Sum.inl) '' nativeMonomials F D := by
  classical
  ext p
  constructor
  · rintro ⟨d, hd, hpure, rfl⟩
    let g := Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn
    have hmap : g.mapDomain Sum.inl = d := Finsupp.mapDomain_comapDomain Sum.inl Sum.inl_injective d (by
      intro j hj
      cases j with
      | inl j => exact ⟨j, rfl⟩
      | inr i => exact False.elim ((Finsupp.mem_support_iff.mp hj) (hpure i)))
    have hg : g.degree = D := by
      rw [← Finsupp.degree_mapDomain Sum.inl g, hmap]
      exact hd
    refine ⟨MvPolynomial.monomial g 1, ⟨g, hg, rfl⟩, ?_⟩
    rw [MvPolynomial.rename_monomial, hmap]
  · rintro ⟨p, ⟨d, hd, rfl⟩, rfl⟩
    exact SplitBaseVeronese.rename_monomial_mem F ι D d hd

theorem homogeneous_mem_adjoin_monomials (F : Type*) [Field F] (D : ℕ)
    (p : MvPolynomial (Fin 3) F) (hp : p.IsHomogeneous D) :
    p ∈ Algebra.adjoin F (nativeMonomials F D) := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact (Algebra.adjoin F (nativeMonomials F D)).zero_mem
  | add p q hp hq ihp ihq => exact (Algebra.adjoin F (nativeMonomials F D)).add_mem ihp ihq
  | monomial d c hd =>
    apply coefficient_monomial_mem (AlgHom.id F (MvPolynomial (Fin 3) F)) _ d c
    apply Algebra.subset_adjoin
    refine ⟨d, ?_, rfl⟩
    rw [Finsupp.degree_eq_weight_one]
    exact hd

theorem adjoin_monomials_eq (F : Type*) [Field F] (D : ℕ) :
    Algebra.adjoin F (nativeMonomials F D) = Algebra.adjoin F {p : MvPolynomial (Fin 3) F | p.IsHomogeneous D} := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨d, hd, rfl⟩
    exact Algebra.subset_adjoin (MvPolynomial.isHomogeneous_monomial 1 hd)
  · exact Algebra.adjoin_le (homogeneous_mem_adjoin_monomials F D)

theorem degreeImage_id (F : Type*) [Field F] (d : ℕ) :
    WeightedVeroneseGeneration.degreeImage (1 : Fin 3 → ℕ) (AlgHom.id F (MvPolynomial (Fin 3) F)) d =
      {p : MvPolynomial (Fin 3) F | p.IsHomogeneous d} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem nativeVeronese_eq_adjoin (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) :
    nativeVeronese F D = Algebra.adjoin F (nativeMonomials F D) := by
  rw [nativeVeronese, GradedVeroneseAlgebra.veronese_eq_adjoin, adjoin_monomials_eq]
  have hh := WeightedVeroneseGeneration.veronese_generated (1 : Fin 3 → ℕ) D hD
    (fun _ ↦ Or.inl rfl) (AlgHom.id F (MvPolynomial (Fin 3) F))
  simpa only [WeightedVeroneseGeneration.veroneseAlgebra, degreeImage_id,
    MvPolynomial.mem_homogeneousSubmodule, Set.mem_ofPred_eq] using hh

theorem baseAlgebra_eq_map {F ι A : Type*} [Field F] [CommRing A] [Algebra F A]
    (D : ℕ) (hD : 0 < D) (φ : WeightedPolynomial F ι →ₐ[F] A) :
    SplitBaseVeronese.baseAlgebra D φ =
      (nativeVeronese F D).map (φ.comp (MvPolynomial.rename Sum.inl)) := by
  rw [SplitBaseVeronese.baseAlgebra, baseMonomials_eq_image, Set.image_image,
    nativeVeronese_eq_adjoin F D hD, ← Algebra.adjoin_image]
  rfl

end PaperP1.StandardBaseVeronese
