module

public import PaperP1.Algebra.SquareLineMatching
public import PaperP1.Arithmetic.SelectedProportionalPairs

/-! # Actual selected-value directness excludes functional radical solutions on affine rational lines -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalLineObstruction

open Finset Polynomial PaperP1.SquareLineMatching PaperP1.SelectedProportionalPairs

theorem two_equations (S T I₀ I₁ J₀ J₁ : Finset ℤ) (x y : ℤ) (α β c₀ c₁ : ℚ)
    (hI₀ : I₀ ⊆ S) (hI₁ : I₁ ⊆ S) (hJ₀ : J₀ ⊆ T) (hJ₁ : J₁ ⊆ T)
    (hdisj : Disjoint I₀ I₁) (hne₀ : I₀.Nonempty) (hne₁ : I₁.Nonempty)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (values x S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values x S)) (FiniteEvenSquareClasses.space (values y T)))
    (hline : (y : ℚ) = α * (x : ℚ) + β) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) :
    ¬(IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X]) (lineRestriction c₀ I₀ J₀ α β)) ∧
      IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X]) (lineRestriction c₁ I₁ J₁ α β))) := by
  rintro ⟨hsq₀, hsq₁⟩
  obtain ⟨i₀, hi₀⟩ := hne₀
  obtain ⟨i₁, hi₁⟩ := hne₁
  obtain ⟨j₀, hj₀, hmatch₀⟩ := function_matches_offset c₀ hc₀ I₀ J₀ α β hsq₀ i₀ hi₀
  obtain ⟨j₁, hj₁, hmatch₁⟩ := function_matches_offset c₁ hc₁ I₁ J₁ α β hsq₁ i₁ hi₁
  have hne : i₀ ≠ i₁ := by
    intro heq
    exact disjoint_left.mp hdisj hi₀ (heq ▸ hi₁)
  have hn₀ : (x + i₀).natAbs ∈ values x S := mem_image.mpr ⟨i₀, hI₀ hi₀, rfl⟩
  have hn₁ : (x + i₁).natAbs ∈ values x S := mem_image.mpr ⟨i₁, hI₁ hi₁, rfl⟩
  have hm₀ : (y + j₀).natAbs ∈ values y T := mem_image.mpr ⟨j₀, hJ₀ hj₀, rfl⟩
  have hm₁ : (y + j₁).natAbs ∈ values y T := mem_image.mpr ⟨j₁, hJ₁ hj₁, rfl⟩
  have hp₀ : ((y + j₀).natAbs : ℚ) = α * ((x + i₀).natAbs : ℚ) := by
    rw [value_cast y j₀ (hposT j₀ (hJ₀ hj₀)), value_cast x i₀ (hposS i₀ (hI₀ hi₀)), hline]
    linear_combination hmatch₀
  have hp₁ : ((y + j₁).natAbs : ℚ) = α * ((x + i₁).natAbs : ℚ) := by
    rw [value_cast y j₁ (hposT j₁ (hJ₁ hj₁)), value_cast x i₁ (hposS i₁ (hI₁ hi₁)), hline]
    linear_combination hmatch₁
  have hcrossQ : ((x + i₀).natAbs : ℚ) * ((y + j₁).natAbs : ℚ) =
      ((x + i₁).natAbs : ℚ) * ((y + j₀).natAbs : ℚ) := by
    rw [hp₀, hp₁]
    ring
  have hcross : (x + i₀).natAbs * (y + j₁).natAbs = (x + i₁).natAbs * (y + j₀).natAbs := by
    exact_mod_cast hcrossQ
  exact no_proportional_pairs (values x S) (values y T) hind hdirect (values_pos x S hposS)
    (values_pos y T hposT) _ _ _ _ hn₀ hn₁ hm₀ hm₁
    (values_ne x i₀ i₁ (hposS i₀ (hI₀ hi₀)) (hposS i₁ (hI₁ hi₁)) hne) hcross

theorem family_obstruction {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (hA : 2 ≤ A.card) (S T : Finset ℤ) (I J : ι → Finset ℤ)
    (x y : ℤ) (α β : ℚ) (c : ι → ℚ)
    (hI : ∀ i ∈ A, I i ⊆ S) (hJ : ∀ i ∈ A, J i ⊆ T)
    (hdisj : (A : Set ι).PairwiseDisjoint I) (hne : ∀ i ∈ A, (I i).Nonempty)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (values x S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values x S)) (FiniteEvenSquareClasses.space (values y T)))
    (hline : (y : ℚ) = α * (x : ℚ) + β) (hc : ∀ i ∈ A, c i ≠ 0) :
    ¬∀ i ∈ A, IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X]) (lineRestriction (c i) (I i) (J i) α β)) := by
  intro hsq
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (by omega : 1 < A.card)
  exact two_equations S T (I i) (I j) (J i) (J j) x y α β (c i) (c j)
    (hI i hi) (hI j hj) (hJ i hi) (hJ j hj) (hdisj hi hj hij) (hne i hi) (hne j hj)
    hposS hposT hind hdirect hline (hc i hi) (hc j hj) ⟨hsq i hi, hsq j hj⟩

theorem vertical_family_obstruction {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (hA : 2 ≤ A.card) (S T : Finset ℤ) (I J : ι → Finset ℤ)
    (x y : ℤ) (c : ι → ℚ)
    (hI : ∀ i ∈ A, I i ⊆ S) (hJ : ∀ i ∈ A, J i ⊆ T)
    (hdisj : (A : Set ι).PairwiseDisjoint J) (hne : ∀ i ∈ A, (J i).Nonempty)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (values y T))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values x S)) (FiniteEvenSquareClasses.space (values y T)))
    (hc : ∀ i ∈ A, c i ≠ 0) :
    ¬∀ i ∈ A, IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X])
      (C (c i) * C ((FormalWordPolynomials.linearOver ℚ (I i)).eval (x : ℚ)) *
        FormalWordPolynomials.linearOver ℚ (J i))) := by
  intro hsq
  apply family_obstruction A hA T S J I y x 0 (x : ℚ) c hJ hI hdisj hne
    hposT hposS hind hdirect.symm (by ring) hc
  intro i hi
  have heq : lineRestriction (c i) (J i) (I i) 0 (x : ℚ) =
      C (c i) * C ((FormalWordPolynomials.linearOver ℚ (I i)).eval (x : ℚ)) *
        FormalWordPolynomials.linearOver ℚ (J i) := by
    simp only [lineRestriction, C_0, zero_mul, zero_add, comp_C]
    ring
  rw [heq]
  exact hsq i hi

end PaperP1.SplitRadicalLineObstruction
