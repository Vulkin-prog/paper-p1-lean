module

public import PaperP1.Arithmetic.ScaledCurveEquationClasses
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # A unique nonzero equation coordinate forces every regular fibre root to its own selected offset -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniqueKernelFibreMatching

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveCriticalFibres PaperP1.CurveFibreRegularity
  PaperP1.CurveFunctionField PaperP1.ScaledCurveEquationClasses

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
  (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (d : ι → ℤ) (hd : ∀ ν, d ν ≠ 0)
  (I : ι → Finset ℤ) (j : ι → ℤ)

abbrev space : Submodule (ZMod 2) (ι → ZMod 2) :=
  LinearMap.ker (classMap C₀ hx hy d hd I (fun ν ↦ {j ν}))

omit [DecidableEq ι] in
theorem root_matches_selected {K : Type*} [Field K] [CharZero K]
    (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (w : space C₀ hx hy d hd I j) (u : ℤ) (hu : u ∈ (selected w.val).biUnion I)
    (hregular : u ∉ badOffsets C₀) (z : K) (hz : (fibre C₀ u).eval z = 0) :
    ∃ μ ∈ selected w.val, z = -(j μ : K) := by
  classical
  have hJ : Pairwise fun ν μ ↦ Disjoint ({j ν} : Finset ℤ) {j μ} := by
    intro ν μ hne
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact hne (hj ((mem_singleton.mp ha).symm.trans (mem_singleton.mp hb)))
  have hsquare := kernel_literal_square C₀ hx hy d hd I (fun ν ↦ {j ν}) w.val w.property hI hJ
  obtain ⟨v, hv, heq⟩ := ScaledCurveSquareMatching.root_matches_offset C₀ hy
    (∏ ν ∈ selected w.val, d ν) (Finset.prod_ne_zero_iff.mpr (fun ν _ ↦ hd ν))
    ((selected w.val).biUnion I) ((selected w.val).biUnion (fun ν ↦ {j ν})) hsquare u hu hregular z hz
  obtain ⟨μ, hμ, hvμ⟩ := mem_biUnion.mp hv
  have hvj : v = j μ := mem_singleton.mp hvμ
  exact ⟨μ, hμ, hvj ▸ heq⟩

theorem good_root_matches {K : Type*} [Field K] [CharZero K]
    (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (ν : ι) (hν : ν ∈ UniqueCoordinateBudget.good (space C₀ hx hy d hd I j))
    (u : ℤ) (hu : u ∈ I ν) (hregular : u ∉ badOffsets C₀)
    (z : K) (hz : (fibre C₀ u).eval z = 0) : z = -(j ν : K) := by
  classical
  by_contra hnot
  have hform := ((UniqueCoordinateBudget.mem_good (space C₀ hx hy d hd I j) ν).mp hν).1
  obtain ⟨w, hwν, _⟩ := BinaryFormSeparation.exists_one_zero
    (UniqueCoordinateBudget.form (space C₀ hx hy d hd I j) ν) 0 hform hform
  change w.val ν = 1 at hwν
  have hselν : ν ∈ selected w.val := by simp [selected, hwν]
  obtain ⟨μ, hμ, hmatch⟩ := root_matches_selected C₀ hx hy d hd I j hI hj w u
    (mem_biUnion.mpr ⟨ν, hselν, hu⟩) hregular z hz
  have hne : ν ≠ μ := by
    intro heq
    subst μ
    exact hnot hmatch
  obtain ⟨v, hvν, hvμ⟩ := BinaryFormSeparation.good_coordinate (space C₀ hx hy d hd I j) ν μ hν hne
  have hselν' : ν ∈ selected v.val := by simp [selected, hvν]
  obtain ⟨δ, hδ, hmatch'⟩ := root_matches_selected C₀ hx hy d hd I j hI hj v u
    (mem_biUnion.mpr ⟨ν, hselν', hu⟩) hregular z hz
  have hμδ : μ = δ := hj (Int.cast_injective (neg_injective (hmatch.symm.trans hmatch')))
  rw [← hμδ] at hδ
  exact (mem_filter.mp hδ).2 hvμ

theorem degreeY_eq_one
    (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (ν : ι) (hν : ν ∈ UniqueCoordinateBudget.good (space C₀ hx hy d hd I j))
    (u : ℤ) (hu : u ∈ I ν) (hregular : u ∉ badOffsets C₀) : degreeY C₀ = 1 := by
  classical
  have hle : (fibre (K := ℂ) C₀ u).roots.toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    have hzroot := (Polynomial.mem_roots (fibre_nonzero (K := ℂ) C₀ (Fact.out : Irreducible C₀) hy u hregular)).mp
      (Multiset.mem_toFinset.mp hz)
    have hwroot := (Polynomial.mem_roots (fibre_nonzero (K := ℂ) C₀ (Fact.out : Irreducible C₀) hy u hregular)).mp
      (Multiset.mem_toFinset.mp hw)
    exact (good_root_matches C₀ hx hy d hd I j hI hj ν hν u hu hregular z hzroot).trans
      (good_root_matches C₀ hx hy d hd I j hI hj ν hν u hu hregular w hwroot).symm
  rw [fibre_roots_card (K := ℂ) C₀ (Fact.out : Irreducible C₀) hy u hregular] at hle
  omega

theorem good_integer_point
    (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (ν : ι) (hν : ν ∈ UniqueCoordinateBudget.good (space C₀ hx hy d hd I j))
    (u : ℤ) (hu : u ∈ I ν) (hregular : u ∉ badOffsets C₀) :
    C₀.evalEval (-u) (-j ν) = 0 := by
  classical
  have hcard : 0 < (fibre (K := ℂ) C₀ u).roots.toFinset.card := by
    rw [fibre_roots_card (K := ℂ) C₀ (Fact.out : Irreducible C₀) hy u hregular]
    exact hy
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
  have hzroot := (Polynomial.mem_roots (fibre_nonzero (K := ℂ) C₀ (Fact.out : Irreducible C₀) hy u hregular)).mp
    (Multiset.mem_toFinset.mp hz)
  have heq := good_root_matches C₀ hx hy d hd I j hI hj ν hν u hu hregular z hzroot
  have hfzero : (fibre (K := ℂ) C₀ u).eval (-(j ν : ℂ)) = 0 := heq ▸ hzroot
  have hcast : ((C₀.evalEval (-u) (-j ν) : ℤ) : ℂ) = 0 :=
    (fibre_integer_evaluation (K := ℂ) C₀ u (j ν)).symm.trans hfzero
  exact_mod_cast hcast

end PaperP1.UniqueKernelFibreMatching
