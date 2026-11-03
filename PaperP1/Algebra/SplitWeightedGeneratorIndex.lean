module

public import PaperP1.Algebra.StandardBaseVeronese
public import PaperP1.Algebra.HomogeneousMonomialCount

/-! # The literal projective coordinates have exactly binom(D+2,2)+k indices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitWeightedGeneratorIndex

open PaperP1.HomogeneousSplitRadicalRelations PaperP1.SplitWeightedDegreeGenerators

def generator (F ι : Type*) [Field F] (D : ℕ) :
    ({d : Fin 3 →₀ ℕ // d.degree = D} ⊕ ι) → generators F ι D
  | .inl d => ⟨MvPolynomial.rename Sum.inl (MvPolynomial.monomial d.1 1), Or.inl (by
      rw [StandardBaseVeronese.baseMonomials_eq_image]
      exact ⟨MvPolynomial.monomial d.1 1, ⟨d.1, d.property, rfl⟩, rfl⟩)⟩
  | .inr i => ⟨MvPolynomial.X (Sum.inr i), Or.inr ⟨i, rfl⟩⟩

theorem renamed_monomial_ne_radical (F ι : Type*) [Field F] (d : Fin 3 →₀ ℕ) (i : ι) :
    MvPolynomial.rename Sum.inl (MvPolynomial.monomial d (1 : F)) ≠
      (MvPolynomial.X (Sum.inr i) : WeightedPolynomial F ι) := by
  intro h
  rw [MvPolynomial.rename_monomial] at h
  have he := MvPolynomial.monomial_left_injective (one_ne_zero : (1 : F) ≠ 0) h
  have hi := congrArg (fun z : (Fin 3 ⊕ ι) →₀ ℕ ↦ z (Sum.inr i)) he
  have hnot : Sum.inr i ∉ Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ ι) := by simp
  rw [Finsupp.mapDomain_of_notMem_range d _ hnot, Finsupp.single_eq_same] at hi
  exact zero_ne_one hi

theorem generator_injective (F ι : Type*) [Field F] (D : ℕ) :
    Function.Injective (generator F ι D) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  cases a with
  | inl d =>
    cases b with
    | inl e =>
      change MvPolynomial.rename Sum.inl (MvPolynomial.monomial d.1 1) =
        MvPolynomial.rename Sum.inl (MvPolynomial.monomial e.1 1) at h
      exact congrArg Sum.inl (Subtype.ext (MvPolynomial.monomial_left_injective
        (one_ne_zero : (1 : F) ≠ 0) (MvPolynomial.rename_injective Sum.inl Sum.inl_injective h)))
    | inr i => exact False.elim (renamed_monomial_ne_radical F ι d.1 i h)
  | inr i =>
    cases b with
    | inl d => exact False.elim (renamed_monomial_ne_radical F ι d.1 i h.symm)
    | inr j =>
      change (MvPolynomial.X (Sum.inr i) : WeightedPolynomial F ι) = MvPolynomial.X (Sum.inr j) at h
      exact congrArg Sum.inr (Sum.inr_injective (MvPolynomial.X_injective h))

theorem generator_surjective (F ι : Type*) [Field F] (D : ℕ) :
    Function.Surjective (generator F ι D) := by
  rintro ⟨p, hp⟩
  rcases hp with hp | ⟨i, rfl⟩
  · rw [StandardBaseVeronese.baseMonomials_eq_image] at hp
    obtain ⟨q, ⟨d, hd, rfl⟩, hq⟩ := hp
    exact ⟨Sum.inl ⟨d, hd⟩, Subtype.ext hq⟩
  · exact ⟨Sum.inr i, rfl⟩

def indexEquiv (F ι : Type*) [Field F] (D : ℕ) :
    ({d : Fin 3 →₀ ℕ // d.degree = D} ⊕ ι) ≃ generators F ι D :=
  Equiv.ofBijective (generator F ι D) ⟨generator_injective F ι D, generator_surjective F ι D⟩

theorem index_card (F ι : Type*) [Field F] [Finite ι] (D : ℕ) :
    Nat.card (generators F ι D) = (D + 2).choose 2 + Nat.card ι := by
  have : Finite {d : Fin 3 →₀ ℕ // d.degree = D} := HomogeneousMonomialCount.exponent_finite (Fin 3) D
  rw [← Nat.card_congr (indexEquiv F ι D), Nat.card_sum, HomogeneousMonomialCount.ternary_exponent_card]

end PaperP1.SplitWeightedGeneratorIndex
