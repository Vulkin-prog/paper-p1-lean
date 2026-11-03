module

public import PaperP1.Algebra.SplitWeightedDegreeGenerators
public import PaperP1.Algebra.HomogeneousSplitRadicalPolynomials

/-! # Every actual homogenized radicand belongs to the pure base Veronese algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitBaseVeronese

open Finset PaperP1.HomogeneousSplitRadicalRelations PaperP1.SplitWeightedDegreeGenerators
  PaperP1.HomogeneousSplitRadicalPolynomials

theorem mapDomain_base_pure {ι : Type*} (d : Fin 3 →₀ ℕ) (i : ι) :
    (d.mapDomain Sum.inl) (Sum.inr i) = 0 :=
  Finsupp.mapDomain_of_notMem_range d (Sum.inr i) (by rintro ⟨j, hj⟩; cases hj)

theorem rename_monomial_mem (F ι : Type*) [Field F] (D : ℕ) (d : Fin 3 →₀ ℕ) (hd : d.degree = D) :
    (MvPolynomial.rename Sum.inl (MvPolynomial.monomial d 1) : WeightedPolynomial F ι) ∈ baseMonomials F ι D := by
  rw [MvPolynomial.rename_monomial]
  exact ⟨d.mapDomain Sum.inl, (Finsupp.degree_mapDomain _ d).trans hd,
    mapDomain_base_pure d, rfl⟩

def baseAlgebra {F ι A : Type*} [Field F] [CommRing A] [Algebra F A]
    (D : ℕ) (φ : WeightedPolynomial F ι →ₐ[F] A) : Subalgebra F A :=
  Algebra.adjoin F (φ '' baseMonomials F ι D)

theorem native_degreeD_image_mem {F ι A : Type*} [Field F] [CommRing A] [Algebra F A]
    (D : ℕ) (φ : WeightedPolynomial F ι →ₐ[F] A)
    (p : MvPolynomial (Fin 3) F) (hp : p.IsHomogeneous D) :
    φ (MvPolynomial.rename Sum.inl p) ∈ baseAlgebra D φ := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    simpa only [map_zero] using (baseAlgebra D φ).zero_mem
  | add p q hp hq ihp ihq =>
    simpa only [map_add] using (baseAlgebra D φ).add_mem ihp ihq
  | monomial d c hd =>
    have hdeg : d.degree = D := by
      rw [Finsupp.degree_eq_weight_one]
      exact hd
    rw [MvPolynomial.rename_monomial]
    apply coefficient_monomial_mem φ (baseAlgebra D φ) (d.mapDomain Sum.inl) c
    apply Algebra.subset_adjoin
    exact ⟨MvPolynomial.rename Sum.inl (MvPolynomial.monomial d 1), rename_monomial_mem F ι D d hdeg,
      by rw [MvPolynomial.rename_monomial]⟩

theorem native_multiple_image_mem {F ι A : Type*} [Field F] [CommRing A] [Algebra F A]
    (D : ℕ) (hD : 0 < D) (φ : WeightedPolynomial F ι →ₐ[F] A)
    (n : ℕ) (p : MvPolynomial (Fin 3) F) (hp : p.IsHomogeneous (n * D)) :
    φ (MvPolynomial.rename Sum.inl p) ∈ baseAlgebra D φ :=
  WeightedVeroneseGeneration.homogeneous_image_mem (1 : Fin 3 → ℕ) D hD (fun _ ↦ Or.inl rfl)
    (φ.comp (MvPolynomial.rename Sum.inl)) (baseAlgebra D φ)
    (native_degreeD_image_mem D φ) n p hp

theorem radicand_image_mem {F ι A : Type*} [Field F] [CommRing A] [Algebra F A]
    (D : ℕ) (hD : 0 < D) (φ : WeightedPolynomial F ι →ₐ[F] A)
    (c : F) (I J : Finset ℤ) (hdeg : I.card + J.card ≤ 2 * D) :
    φ (MvPolynomial.rename Sum.inl (nativeRadicand c (2 * D - (I.card + J.card)) I J)) ∈ baseAlgebra D φ := by
  apply native_multiple_image_mem D hD φ 2
  convert nativeRadicand_homogeneous c (2 * D - (I.card + J.card)) I J using 1; omega

end PaperP1.SplitBaseVeronese
