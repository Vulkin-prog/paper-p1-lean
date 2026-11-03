module

public import PaperP1.Algebra.LinearRationalGraph
public import PaperP1.Arithmetic.SplitRadicalLineObstruction

/-! # Two actual offset-grid matches exclude a rational line through a direct-sum host -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalGridLineObstruction

open Polynomial Finset PaperP1.SelectedProportionalPairs

theorem two_matches (S T : Finset ℤ) (x y i₀ i₁ j₀ j₁ : ℤ) (α β : ℚ)
    (hi₀ : i₀ ∈ S) (hi₁ : i₁ ∈ S) (hj₀ : j₀ ∈ T) (hj₁ : j₁ ∈ T) (hne : i₀ ≠ i₁)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (values x S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values x S)) (FiniteEvenSquareClasses.space (values y T)))
    (hline : (y : ℚ) = α * (x : ℚ) + β)
    (hmatch₀ : β + (j₀ : ℚ) = α * (i₀ : ℚ)) (hmatch₁ : β + (j₁ : ℚ) = α * (i₁ : ℚ)) : False := by
  have hn₀ : (x + i₀).natAbs ∈ values x S := mem_image.mpr ⟨i₀, hi₀, rfl⟩
  have hn₁ : (x + i₁).natAbs ∈ values x S := mem_image.mpr ⟨i₁, hi₁, rfl⟩
  have hm₀ : (y + j₀).natAbs ∈ values y T := mem_image.mpr ⟨j₀, hj₀, rfl⟩
  have hm₁ : (y + j₁).natAbs ∈ values y T := mem_image.mpr ⟨j₁, hj₁, rfl⟩
  have hp₀ : ((y + j₀).natAbs : ℚ) = α * ((x + i₀).natAbs : ℚ) := by
    rw [value_cast y j₀ (hposT j₀ hj₀), value_cast x i₀ (hposS i₀ hi₀), hline]
    linear_combination hmatch₀
  have hp₁ : ((y + j₁).natAbs : ℚ) = α * ((x + i₁).natAbs : ℚ) := by
    rw [value_cast y j₁ (hposT j₁ hj₁), value_cast x i₁ (hposS i₁ hi₁), hline]
    linear_combination hmatch₁
  have hcrossQ : ((x + i₀).natAbs : ℚ) * ((y + j₁).natAbs : ℚ) =
      ((x + i₁).natAbs : ℚ) * ((y + j₀).natAbs : ℚ) := by
    rw [hp₀, hp₁]
    ring
  have hcross : (x + i₀).natAbs * (y + j₁).natAbs = (x + i₁).natAbs * (y + j₀).natAbs := by
    exact_mod_cast hcrossQ
  exact no_proportional_pairs (values x S) (values y T) hind hdirect (values_pos x S hposS)
    (values_pos y T hposT) _ _ _ _ hn₀ hn₁ hm₀ hm₁
    (values_ne x i₀ i₁ (hposS i₀ hi₀) (hposS i₁ hi₁) hne) hcross

theorem rational_graph (S T : Finset ℤ) (x y i₀ i₁ j₀ j₁ : ℤ)
    (hi₀ : i₀ ∈ S) (hi₁ : i₁ ∈ S) (hj₀ : j₀ ∈ T) (hj₁ : j₁ ∈ T) (hne : i₀ ≠ i₁)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (values x S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values x S)) (FiniteEvenSquareClasses.space (values y T)))
    (p q : ℚ[X]) (hp : p.natDegree ≤ 1) (hq : q.natDegree = 0) (hq0 : q ≠ 0)
    (hgrid₀ : p.eval (-(i₀ : ℚ)) = -(j₀ : ℚ) * q.eval (-(i₀ : ℚ)))
    (hgrid₁ : p.eval (-(i₁ : ℚ)) = -(j₁ : ℚ) * q.eval (-(i₁ : ℚ)))
    (hpoint : p.eval (x : ℚ) = (y : ℚ) * q.eval (x : ℚ)) : False := by
  obtain ⟨α, β, hparam⟩ := LinearRationalGraph.exists_parameters p q hp hq hq0
  have hline := (hparam (x : ℚ) (y : ℚ)).mp hpoint
  have hmatch₀ : β + (j₀ : ℚ) = α * (i₀ : ℚ) := by
    have hg := (hparam (-(i₀ : ℚ)) (-(j₀ : ℚ))).mp hgrid₀
    linear_combination -hg
  have hmatch₁ : β + (j₁ : ℚ) = α * (i₁ : ℚ) := by
    have hg := (hparam (-(i₁ : ℚ)) (-(j₁ : ℚ))).mp hgrid₁
    linear_combination -hg
  exact two_matches S T x y i₀ i₁ j₀ j₁ α β hi₀ hi₁ hj₀ hj₁ hne hposS hposT hind hdirect hline hmatch₀ hmatch₁

end PaperP1.RationalGridLineObstruction
