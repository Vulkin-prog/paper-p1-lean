module

public import PaperP1.Arithmetic.CurveIntegerFibres
public import PaperP1.Algebra.CurveSwapField
public import PaperP1.Algebra.FiniteSupportImageRank
public import Mathlib.Algebra.Field.ZMod

/-! # Counting actual grid points from an injectively projected square-word basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveSquareGridBound

open Polynomial PaperP1.BivariateDegrees PaperP1.CurveCriticalFibres
  PaperP1.CurveFunctionField PaperP1.FormalWordPolynomials PaperP1.CurveIntegerFibres
  PaperP1.FiniteSupportImageRank

local instance : CommRing ℤ[X][X] := inferInstance
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem basis_grid_bound {E ι : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype ι]
    (C₀ : ℤ[X][X]) [hC : Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀)
    (b : Module.Basis ι (ZMod 2) E) (f g : E →ₗ[ZMod 2] (ℤ →₀ ZMod 2))
    (hf : Function.Injective f) (hg : Function.Injective g) (B : ℕ)
    (hbf : ∀ i, (f (b i)).support ⊆ offsetBox B)
    (hbg : ∀ i, (g (b i)).support ⊆ offsetBox B)
    (hsquare : ∀ i, IsSquare (specialize C₀ (wordOver ℤ (f (b i)).support (g (b i)).support)))
    (hrf : ∀ i u, u ∈ (f (b i)).support → u ∉ badOffsets C₀)
    (hrg : ∀ i v, v ∈ (g (b i)).support → v ∉ badOffsets (Bivariate.swap C₀)) :
    max (degreeX C₀) (degreeY C₀) * Module.finrank (ZMod 2) E ≤ (integerGrid C₀ B).card := by
  classical
  have hvertical : degreeY C₀ * Module.finrank (ZMod 2) E ≤ (integerGrid C₀ B).card := by
    apply (Nat.mul_le_mul_left (degreeY C₀) (rank_le_supportUnion (K := ZMod 2) (E := E) b f hf)).trans
    apply mul_card_le_grid C₀ B (supportUnion b f) (degreeY C₀) (supportUnion_subset b f _ hbf)
    intro u hu
    obtain ⟨i, hi⟩ := (mem_supportUnion b f u).mp hu
    exact degree_le_fibre C₀ hy _ _ (hsquare i) B
      (fun v hv ↦ (mem_offsetBox B v).mp (hbg i hv)) u hi (hrf i u hi)
  let : Fact (Irreducible (Bivariate.swap C₀)) := ⟨hC.out.map Bivariate.swap⟩
  have hswapY : 0 < degreeY (Bivariate.swap C₀) := by
    simpa only [BivariateCurveDegrees.degreeY_swap] using hx
  have hhorizontal : degreeX C₀ * Module.finrank (ZMod 2) E ≤ (integerGrid C₀ B).card := by
    have h : degreeY (Bivariate.swap C₀) * Module.finrank (ZMod 2) E ≤
        (integerGrid (Bivariate.swap C₀) B).card := by
      apply (Nat.mul_le_mul_left _ (rank_le_supportUnion (K := ZMod 2) (E := E) b g hg)).trans
      apply mul_card_le_grid (Bivariate.swap C₀) B (supportUnion b g) _ (supportUnion_subset b g _ hbg)
      intro v hv
      obtain ⟨i, hi⟩ := (mem_supportUnion b g v).mp hv
      exact degree_le_fibre (Bivariate.swap C₀) hswapY _ _
        (CurveSwapField.square_word_swap C₀ _ _ (hsquare i)) B
        (fun u hu ↦ (mem_offsetBox B u).mp (hbf i hu)) v hi (hrg i v hi)
    simpa only [BivariateCurveDegrees.degreeY_swap, grid_card_swap] using h
  rcases le_total (degreeX C₀) (degreeY C₀) with h | h
  · simpa only [max_eq_right h] using hvertical
  · simpa only [max_eq_left h] using hhorizontal

end PaperP1.CurveSquareGridBound
