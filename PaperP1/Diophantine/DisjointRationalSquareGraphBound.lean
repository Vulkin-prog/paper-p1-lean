module

public import PaperP1.Algebra.RationalGraphPoleEquations
public import PaperP1.Algebra.RationalSquareGraphNonconstant
public import PaperP1.Combinatorics.DisjointOffsetGridSelection
public import PaperP1.Diophantine.GridRationalGraphDescent

/-! # Actual split-product squares on any rational graph give an offset-only admissible-point bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointRationalSquareGraphBound

open Polynomial Finset PaperP1.SelectedProportionalPairs

variable {F ι : Type*} [Field F] [CharZero F] [DecidableEq ι]

theorem integral_point (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B)
    (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (c : ι → F)
    (hdisj : (A : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ A, (I ν).card = a)
    (hiB : ∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) (hjB : ∀ ν ∈ A, (j ν).natAbs ≤ B)
    (hc : ∀ ν ∈ A, c ν ≠ 0) (p q : F[X]) (hq : q ≠ 0) (hcop : IsCoprime p q)
    (hA : 3 * max p.natDegree q.natDegree + 1 ≤ A.card)
    (hsq : ∀ ν ∈ A, IsSquare (RationalGraphSquareRoots.value (c ν) (j ν : F)
      (FormalWordPolynomials.linearOver F (I ν)) p q))
    (S T : Finset ℤ) (hiS : ∀ ν ∈ A, I ν ⊆ S) (hjT : ∀ ν ∈ A, j ν ∈ T)
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : p.eval (X : F) = (Y : F) * q.eval (X : F))
    (hposS : ∀ z ∈ S, 0 < X + z) (hposT : ∀ z ∈ T, 0 < Y + z)
    (hind : EvenIndependentValues.Independent (values X S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T))) :
    X.natAbs ≤ GridRationalGraphExclusion.bound (max p.natDegree q.natDegree) B := by
  obtain ⟨ν, hν⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  have hIν : (I ν).Nonempty := Finset.card_pos.mp (by rw [hcard ν hν]; exact ha)
  have hd := RationalSquareGraphNonconstant.degree_pos (c ν) (j ν) (I ν) hIν p q hq (hc ν hν)
    (hsq ν hν) X Y hpoint (hposT (j ν) (hjT ν hν))
  let good := A \ RationalGraphPoleEquations.badEquations A I q
  have hgood : 2 * max p.natDegree q.natDegree + 1 ≤ good.card :=
    RationalGraphPoleEquations.survivors_card A I p q hq hdisj hA
  have hdgood : (good : Set ι).PairwiseDisjoint I := Set.Pairwise.mono sdiff_subset hdisj
  obtain ⟨x, y, hinj, hsel⟩ := DisjointOffsetGridSelection.select_n good I j a
    (2 * max p.natDegree q.natDegree + 1) hdgood
    (fun μ hμ ↦ hcard μ (mem_sdiff.mp hμ).1)
    (hgood.trans (Nat.le_mul_of_pos_right good.card ha))
  have hxB (t) : (x t).natAbs ≤ B := by
    obtain ⟨μ, hμ, hx, _⟩ := hsel t
    exact hiB μ (mem_sdiff.mp hμ).1 (x t) hx
  have hyB (t) : (y t).natAbs ≤ B := by
    obtain ⟨μ, hμ, _, hy⟩ := hsel t
    exact hy ▸ hjB μ (mem_sdiff.mp hμ).1
  have hxS (t) : x t ∈ S := by
    obtain ⟨μ, hμ, hx, _⟩ := hsel t
    exact hiS μ (mem_sdiff.mp hμ).1 hx
  have hyT (t) : y t ∈ T := by
    obtain ⟨μ, hμ, _, hy⟩ := hsel t
    exact hy ▸ hjT μ (mem_sdiff.mp hμ).1
  have hgrid (t) : p.eval (-(x t : F)) = -(y t : F) * q.eval (-(x t : F)) := by
    obtain ⟨μ, hμ, hx, hy⟩ := hsel t
    rw [hy]
    exact RationalGraphSquareRoots.offset_match (c μ) (j μ : F) (I μ) p q hq (hc μ (mem_sdiff.mp hμ).1)
      (hsq μ (mem_sdiff.mp hμ).1) (x t) hx (RationalGraphPoleEquations.survivor_nonvanishing A I q μ hμ _ hx)
  exact GridRationalGraphDescent.integral_point _ B hd hB x y hinj hxB hyB S T hxS hyT
    p q hq hcop rfl hgrid X Y hcomparable hpoint hposS hposT hind hdirect

end PaperP1.DisjointRationalSquareGraphBound
