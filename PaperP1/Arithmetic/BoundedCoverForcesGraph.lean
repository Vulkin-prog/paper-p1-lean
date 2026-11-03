module

public import PaperP1.Arithmetic.UniqueKernelFibreMatching
public import PaperP1.Combinatorics.DisjointExceptionalFamilies

/-! # A bounded-degree radical cover with enough disjoint equations forces an actual graph image -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedCoverForcesGraph

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveCriticalFibres PaperP1.CurveFunctionField

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
  (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (d : ι → ℤ) (hd : ∀ ν, d ν ≠ 0)
  (I : ι → Finset ℤ) (j : ι → ℤ)

def goodFamilies : Finset ι :=
  UniqueCoordinateBudget.good (UniqueKernelFibreMatching.space C₀ hx hy d hd I j) \
    DisjointExceptionalFamilies.bad I (badOffsets C₀)

theorem good_integer_matches (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (ν : ι) (hν : ν ∈ goodFamilies C₀ hx hy d hd I j) (u : ℤ) (hu : u ∈ I ν) :
    C₀.evalEval (-u) (-j ν) = 0 := by
  obtain ⟨hgood, hreg⟩ := Finset.mem_sdiff.mp hν
  exact UniqueKernelFibreMatching.good_integer_point C₀ hx hy d hd I j hI hj ν hgood u hu
    (DisjointExceptionalFamilies.regular I (badOffsets C₀) ν hreg u hu)

theorem degreeY_eq_one_of_nonempty (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (hne : ∀ ν, (I ν).Nonempty) (hgood : (goodFamilies C₀ hx hy d hd I j).Nonempty) : degreeY C₀ = 1 := by
  obtain ⟨ν, hν⟩ := hgood
  obtain ⟨u, hu⟩ := hne ν
  obtain ⟨hcoord, hreg⟩ := Finset.mem_sdiff.mp hν
  exact UniqueKernelFibreMatching.degreeY_eq_one C₀ hx hy d hd I j hI hj ν hcoord u hu
    (DisjointExceptionalFamilies.regular I (badOffsets C₀) ν hreg u hu)

variable {L : Type*} [Field L] [Algebra (FunctionField C₀) L] [Module.Finite (FunctionField C₀) L]

theorem card_cover_budget (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ))
    (r : ι → L) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν)) :
    Fintype.card ι ≤ (goodFamilies C₀ hx hy d hd I j).card +
      2 * Nat.log 2 (Module.finrank (FunctionField C₀) L) + (badOffsets C₀).card := by
  let U := UniqueKernelFibreMatching.space C₀ hx hy d hd I j
  have hbad := ScaledCurveEquationClasses.bad_card_le_twice_log C₀ hx hy d hd I (fun ν ↦ {j ν}) r hr
  change (UniqueCoordinateBudget.bad U).card ≤ 2 * Nat.log 2 (Module.finrank (FunctionField C₀) L) at hbad
  have hpartition : (UniqueCoordinateBudget.bad U).card + (UniqueCoordinateBudget.good U).card = Fintype.card ι := by
    simpa only [UniqueCoordinateBudget.bad, Finset.card_univ] using
      card_sdiff_add_card_eq_card (subset_univ (UniqueCoordinateBudget.good U))
  have hdeleted : (UniqueCoordinateBudget.good U).card ≤ (goodFamilies C₀ hx hy d hd I j).card +
      (DisjointExceptionalFamilies.bad I (badOffsets C₀)).card := card_le_card_sdiff_add_card
  have hcrit := DisjointExceptionalFamilies.card_bad_le I (badOffsets C₀) hI
  omega

include hx hy hd in
theorem degreeY_eq_one_of_many (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (hne : ∀ ν, (I ν).Nonempty) (r : ι → L)
    (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν))
    (hlarge : (badOffsets C₀).card + 2 * Nat.log 2 (Module.finrank (FunctionField C₀) L) < Fintype.card ι) :
    degreeY C₀ = 1 := by
  have hcover := card_cover_budget C₀ hx hy d hd I j hI r hr
  apply degreeY_eq_one_of_nonempty C₀ hx hy d hd I j hI hj hne
  exact Finset.card_pos.mp (by omega)

theorem good_card_bounded (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (r : ι → L)
    (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν))
    (E : ℕ) (hX : degreeX C₀ ≤ E) (hY : degreeY C₀ ≤ E)
    (hrank : Module.finrank (FunctionField C₀) L ≤ E) (hlarge : 4 * (E + 1) ^ 2 ≤ Fintype.card ι) :
    2 * E + 1 ≤ (goodFamilies C₀ hx hy d hd I j).card := by
  have hcover := card_cover_budget C₀ hx hy d hd I j hI r hr
  have hcrit := badOffsets_card C₀
  have hlog := (Nat.log_le_self 2 (Module.finrank (FunctionField C₀) L)).trans hrank
  have hprod : degreeX C₀ * degreeY C₀ ≤ E ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hX hY
  nlinarith

include hx hy hd in
theorem degreeY_eq_one_bounded (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (hne : ∀ ν, (I ν).Nonempty) (r : ι → L)
    (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν))
    (E : ℕ) (hX : degreeX C₀ ≤ E) (hY : degreeY C₀ ≤ E)
    (hrank : Module.finrank (FunctionField C₀) L ≤ E) (hlarge : 4 * (E + 1) ^ 2 ≤ Fintype.card ι) :
    degreeY C₀ = 1 := by
  have hgood := good_card_bounded C₀ hx hy d hd I j hI r hr E hX hY hrank hlarge
  exact degreeY_eq_one_of_nonempty C₀ hx hy d hd I j hI hj hne (Finset.card_pos.mp (by omega))

end PaperP1.BoundedCoverForcesGraph
