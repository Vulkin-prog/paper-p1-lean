module

public import PaperP1.Algebra.HomogeneousSplitRadicalGrading
public import PaperP1.Algebra.WeightedVeroneseGeneration

/-! # The degree-D generators are precisely the base degree-D monomials and the radicals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitWeightedDegreeGenerators

open Finset PaperP1.HomogeneousSplitRadicalRelations

def baseMonomials (F ι : Type*) [Field F] (D : ℕ) : Set (WeightedPolynomial F ι) :=
  {p | ∃ d : (Fin 3 ⊕ ι) →₀ ℕ, d.degree = D ∧ (∀ i, d (Sum.inr i) = 0) ∧ MvPolynomial.monomial d 1 = p}

def generators (F ι : Type*) [Field F] (D : ℕ) : Set (WeightedPolynomial F ι) :=
  baseMonomials F ι D ∪ Set.range (fun i : ι ↦ MvPolynomial.X (Sum.inr i))

theorem pure_weight {ι : Type*} (D : ℕ) (d : (Fin 3 ⊕ ι) →₀ ℕ)
    (hpure : ∀ i, d (Sum.inr i) = 0) : Finsupp.weight (weight ι D) d = d.degree := by
  apply WeightedVeroneseGeneration.weight_eq_degree
  intro j hj
  cases j with
  | inl j => rfl
  | inr i => exact False.elim ((Finsupp.mem_support_iff.mp hj) (hpure i))

theorem generator_homogeneous {F ι : Type*} [Field F] (D : ℕ)
    {p : WeightedPolynomial F ι} (hp : p ∈ generators F ι D) :
    MvPolynomial.IsWeightedHomogeneous (weight ι D) p D := by
  rcases hp with ⟨d, hd, hpure, rfl⟩ | ⟨i, rfl⟩
  · exact MvPolynomial.isWeightedHomogeneous_monomial _ d 1 ((pure_weight D d hpure).trans hd)
  · exact radical_variable_homogeneous F ι D i

theorem coefficient_monomial_mem {F σ A : Type*} [CommRing F] [CommRing A] [Algebra F A]
    (φ : MvPolynomial σ F →ₐ[F] A) (S : Subalgebra F A) (d : σ →₀ ℕ) (c : F)
    (hd : φ (MvPolynomial.monomial d 1) ∈ S) : φ (MvPolynomial.monomial d c) ∈ S := by
  have he : φ (MvPolynomial.monomial d c) = c • φ (MvPolynomial.monomial d 1) := by
    rw [← map_smul]
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [he]
  exact S.smul_mem hd c

theorem monomial_degreeD_mem {F ι A : Type*} [Field F] [CommRing A] [Algebra F A]
    (D : ℕ) (hD : 0 < D) (φ : WeightedPolynomial F ι →ₐ[F] A) (S : Subalgebra F A)
    (hbase : ∀ d : (Fin 3 ⊕ ι) →₀ ℕ, d.degree = D → (∀ i, d (Sum.inr i) = 0) →
      φ (MvPolynomial.monomial d 1) ∈ S)
    (hroot : ∀ i : ι, φ (MvPolynomial.X (Sum.inr i)) ∈ S)
    (d : (Fin 3 ⊕ ι) →₀ ℕ) (hd : Finsupp.weight (weight ι D) d = D) (c : F) :
    φ (MvPolynomial.monomial d c) ∈ S := by
  classical
  apply coefficient_monomial_mem φ S d c
  by_cases hlarge : ∃ i : ι, d (Sum.inr i) ≠ 0
  · obtain ⟨i, hi⟩ := hlarge
    have hle : Finsupp.single (Sum.inr i) 1 ≤ d :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
    obtain ⟨r, hdr⟩ := le_iff_exists_add.mp hle
    have hz : Finsupp.weight (weight ι D) r = 0 := by
      rw [hdr, map_add, Finsupp.weight_single, one_smul] at hd
      change D + Finsupp.weight (weight ι D) r = D at hd
      omega
    have := Finsupp.nonTorsionWeight_of ℕ (weight ι D)
      (fun j ↦ HomogeneousSplitRadicalGrading.weight_ne_zero ι D hD j)
    have hr : r = 0 := (Finsupp.weight_eq_zero_iff_eq_zero (weight ι D)).mp hz
    have hdeq : d = Finsupp.single (Sum.inr i) 1 := by simpa only [hr, add_zero] using hdr
    rw [hdeq]
    exact hroot i
  · have hpure : ∀ i, d (Sum.inr i) = 0 := fun i ↦ by
      by_contra hi
      exact hlarge ⟨i, hi⟩
    exact hbase d ((pure_weight D d hpure).symm.trans hd) hpure

theorem degreeD_image_mem {F ι A : Type*} [Field F] [CommRing A] [Algebra F A]
    (D : ℕ) (hD : 0 < D) (φ : WeightedPolynomial F ι →ₐ[F] A)
    (p : WeightedPolynomial F ι) (hp : MvPolynomial.IsWeightedHomogeneous (weight ι D) p D) :
    φ p ∈ Algebra.adjoin F (φ '' generators F ι D) := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (Algebra.adjoin F (φ '' generators F ι D)).zero_mem
  | add p q hp hq ihp ihq =>
    simpa only [map_add] using (Algebra.adjoin F (φ '' generators F ι D)).add_mem ihp ihq
  | monomial d c hd =>
    apply monomial_degreeD_mem D hD φ _ _ _ d hd c
    · intro d hd hpure
      exact Algebra.subset_adjoin ⟨MvPolynomial.monomial d 1, Or.inl ⟨d, hd, hpure, rfl⟩, rfl⟩
    · intro i
      exact Algebra.subset_adjoin ⟨MvPolynomial.X (Sum.inr i), Or.inr ⟨i, rfl⟩, rfl⟩

theorem generators_finite (F ι : Type*) [Field F] [Finite ι] (D : ℕ) :
    (generators F ι D).Finite := by
  apply Set.Finite.union _ (Set.finite_range _)
  apply ((Finsupp.finite_of_degree_eq (σ := Fin 3 ⊕ ι) D).image
    (fun d ↦ (MvPolynomial.monomial d 1 : WeightedPolynomial F ι))).subset
  rintro p ⟨d, hd, _hpure, rfl⟩
  exact ⟨d, hd, rfl⟩

end PaperP1.SplitWeightedDegreeGenerators
