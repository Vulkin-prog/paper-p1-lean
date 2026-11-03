module

public import PaperP1.Arithmetic.BoundedCoverForcesGraph
public import PaperP1.Algebra.IntegerGraphEquation
public import PaperP1.Algebra.RationalGridNonconstant
public import PaperP1.Combinatorics.DisjointOffsetGridSelection
public import PaperP1.Diophantine.GridRationalGraphAlternative

/-! # Repeated left offsets exclude the affine graph without host independence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveCoverRepeatedLeftBound

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveFunctionField PaperP1.SelectedProportionalPairs

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
  (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (d : ι → ℤ) (hd : ∀ ν, d ν ≠ 0)
  (I : ι → Finset ℤ) (j : ι → ℤ)
  {L : Type*} [Field L] [Algebra (FunctionField C₀) L] [Module.Finite (FunctionField C₀) L]

include hx hy hd in
theorem integral_point (a B E : ℕ) (ha : 2 ≤ a) (hB : 1 ≤ B)
    (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (hcard : ∀ ν, (I ν).card = a) (hiB : ∀ ν, ∀ z ∈ I ν, z.natAbs ≤ B) (hjB : ∀ ν, (j ν).natAbs ≤ B)
    (hX : degreeX C₀ ≤ E) (hY : degreeY C₀ ≤ E) (hrank : Module.finrank (FunctionField C₀) L ≤ E)
    (hlarge : 4 * (E + 1) ^ 2 ≤ Fintype.card ι)
    (r : ι → L) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν))
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs) (hpoint : C₀.evalEval X Y = 0)
    (hposT : ∀ ν, 0 < Y + j ν) :
    ∃ n : ℕ, 0 < n ∧ n ≤ E ∧ X.natAbs ≤ GridRationalGraphExclusion.bound n B := by
  have ha0 : 0 < a := by omega
  have hne (ν : ι) : (I ν).Nonempty := Finset.card_pos.mp (by rw [hcard ν]; exact ha0)
  have hYone := BoundedCoverForcesGraph.degreeY_eq_one_bounded C₀ hx hy d hd I j hI hj hne r hr E hX hY hrank hlarge
  let G := BoundedCoverForcesGraph.goodFamilies C₀ hx hy d hd I j
  have hG : 2 * E + 1 ≤ G.card := BoundedCoverForcesGraph.good_card_bounded C₀ hx hy d hd I j hI r hr E hX hY hrank hlarge
  let f := IntegerGraphEquation.function C₀
  let n := max f.num.natDegree f.denom.natDegree
  have hnE : n ≤ E := (IntegerGraphEquation.reduced_degree_le C₀ hYone).trans hX
  have hpnt : f.num.eval (X : ℚ) = (Y : ℚ) * f.denom.eval (X : ℚ) :=
    IntegerGraphEquation.reduced_point C₀ hYone X Y hpoint
  obtain ⟨ν, hν⟩ := Finset.card_pos.mp (by omega : 0 < G.card)
  obtain ⟨u, hu⟩ := hne ν
  have hmatch0 := IntegerGraphEquation.reduced_point C₀ hYone (-u) (-j ν)
    (BoundedCoverForcesGraph.good_integer_matches C₀ hx hy d hd I j hI hj ν hν u hu)
  have hmatch : f.num.eval (-(u : ℚ)) = -(j ν : ℚ) * f.denom.eval (-(u : ℚ)) := by
    simpa only [Int.cast_neg] using hmatch0
  have hn : 0 < n := RationalGridNonconstant.degree_pos f.num f.denom f.denom_ne_zero u (j ν) X Y
    hmatch hpnt (hposT ν)
  have hcount : 2 * n + 1 ≤ G.card * a := by
    have hfirst : 2 * n + 1 ≤ G.card := (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hnE) 1).trans hG
    exact hfirst.trans (Nat.le_mul_of_pos_right G.card ha0)
  obtain ⟨x, y, hinj, hsel⟩ := DisjointOffsetGridSelection.select_n G I j a (2 * n + 1)
    (fun ν _ μ _ hneq ↦ hI hneq) (fun ν _ ↦ hcard ν) hcount
  have hxB (t) : (x t).natAbs ≤ B := by
    obtain ⟨μ, _, hμ, _⟩ := hsel t
    exact hiB μ (x t) hμ
  have hyB (t) : (y t).natAbs ≤ B := by
    obtain ⟨μ, _, _, hyμ⟩ := hsel t
    exact hyμ ▸ hjB μ
  have hgrid (t) : f.num.eval (-(x t : ℚ)) = -(y t : ℚ) * f.denom.eval (-(x t : ℚ)) := by
    obtain ⟨μ, hμ, hxu, hyμ⟩ := hsel t
    rw [hyμ]
    simpa only [Int.cast_neg] using IntegerGraphEquation.reduced_point C₀ hYone (-x t) (-j μ)
      (BoundedCoverForcesGraph.good_integer_matches C₀ hx hy d hd I j hI hj μ hμ (x t) hxu)
  rcases GridRationalGraphAlternative.integral_point n B hn hB x y hinj hxB hyB
    f.num f.denom f.denom_ne_zero f.isCoprime_num_denom rfl hgrid X Y hcomparable hpnt with hbound | hline
  · exact ⟨n, hn, hnE, hbound⟩
  · obtain ⟨α, β, hline⟩ := hline
    obtain ⟨u₀, hu₀, u₁, hu₁, hne⟩ := Finset.one_lt_card.mp
      (show 1 < (I ν).card by rw [hcard ν]; omega)
    have hmatch₀ := IntegerGraphEquation.reduced_point C₀ hYone (-u₀) (-j ν)
      (BoundedCoverForcesGraph.good_integer_matches C₀ hx hy d hd I j hI hj ν hν u₀ hu₀)
    have hmatch₁ := IntegerGraphEquation.reduced_point C₀ hYone (-u₁) (-j ν)
      (BoundedCoverForcesGraph.good_integer_matches C₀ hx hy d hd I j hI hj ν hν u₁ hu₁)
    have h₀ := (hline (-u₀) (-j ν)).mp hmatch₀
    have h₁ := (hline (-u₁) (-j ν)).mp hmatch₁
    have hcast : (u₀ : ℚ) ≠ (u₁ : ℚ) := by exact_mod_cast hne
    have hmul : α * ((u₀ : ℚ) - (u₁ : ℚ)) = 0 := by
      nlinarith
    have hα : α = 0 := (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hcast)
    have hhost := (hline (X : ℚ) (Y : ℚ)).mp hpnt
    have hzero : (Y : ℚ) + (j ν : ℚ) = 0 := by
      rw [hα] at h₀ hhost
      linarith
    have hpositive : (0 : ℚ) < (Y : ℚ) + (j ν : ℚ) := by exact_mod_cast hposT ν
    exact False.elim (by linarith)

end PaperP1.CurveCoverRepeatedLeftBound
