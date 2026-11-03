module

public import PaperP1.Arithmetic.BoundedCoverForcesGraph
public import PaperP1.Algebra.IntegerGraphEquation
public import PaperP1.Algebra.RationalGridNonconstant
public import PaperP1.Combinatorics.DisjointOffsetGridSelection
public import PaperP1.Diophantine.GridRationalGraphAlternative
public import PaperP1.Arithmetic.AffineGridAlignment

/-! # Nonalignment excludes the actual affine graph for every positive left size -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveCoverNonalignedBound

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveFunctionField PaperP1.SelectedProportionalPairs

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
  (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (d : ι → ℤ) (hd : ∀ ν, d ν ≠ 0)
  (I : ι → Finset ℤ) (j : ι → ℤ)
  {L : Type*} [Field L] [Algebra (FunctionField C₀) L] [Module.Finite (FunctionField C₀) L]

include hx hy hd in
theorem integral_point (a B E : ℕ) (ha : 0 < a) (hB : 1 ≤ B)
    (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hj : Function.Injective j)
    (hcard : ∀ ν, (I ν).card = a) (hiB : ∀ ν, ∀ z ∈ I ν, z.natAbs ≤ B) (hjB : ∀ ν, (j ν).natAbs ≤ B)
    (hX : degreeX C₀ ≤ E) (hY : degreeY C₀ ≤ E) (hrank : Module.finrank (FunctionField C₀) L ≤ E)
    (hlarge : 4 * (E + 1) ^ 2 ≤ Fintype.card ι)
    (r : ι → L) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν))
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs) (hpoint : C₀.evalEval X Y = 0)
    (hposT : ∀ ν, 0 < Y + j ν) (hXB : (B : ℤ) < X) (hYB : (B : ℤ) < Y)
    (hnonaligned : ¬ AffineGridAlignment.Aligned B X Y) :
    ∃ n : ℕ, 0 < n ∧ n ≤ E ∧ X.natAbs ≤ GridRationalGraphExclusion.bound n B := by
  have hne (ν : ι) : (I ν).Nonempty := Finset.card_pos.mp (by rw [hcard ν]; exact ha)
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
    exact hfirst.trans (Nat.le_mul_of_pos_right G.card ha)
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
    let t₀ : Fin (2 * n + 1) := ⟨0, by omega⟩
    let t₁ : Fin (2 * n + 1) := ⟨1, by omega⟩
    let p : ℤ × ℤ := (-x t₀, -y t₀)
    let q : ℤ × ℤ := (-x t₁, -y t₁)
    have hbound (t : Fin (2 * n + 1)) : |-(x t)| ≤ (B : ℤ) ∧ |-(y t)| ≤ (B : ℤ) := by
      simp only [abs_neg]
      constructor
      · simpa only [Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).mpr (hxB t)
      · simpa only [Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).mpr (hyB t)
    have hne : p ≠ q := by
      intro heq
      have heqx : x t₀ = x t₁ := neg_injective (congrArg Prod.fst heq)
      have heqt := congrArg Fin.val (hinj heqx)
      exact (by decide : (0 : ℕ) ≠ 1) heqt
    have hpLine : (p.2 : ℚ) = α * (p.1 : ℚ) + β := by
      change ((-y t₀ : ℤ) : ℚ) = α * ((-x t₀ : ℤ) : ℚ) + β
      simpa only [Int.cast_neg] using (hline (-(x t₀ : ℚ)) (-(y t₀ : ℚ))).mp (hgrid t₀)
    have hqLine : (q.2 : ℚ) = α * (q.1 : ℚ) + β := by
      change ((-y t₁ : ℤ) : ℚ) = α * ((-x t₁ : ℤ) : ℚ) + β
      simpa only [Int.cast_neg] using (hline (-(x t₁ : ℚ)) (-(y t₁ : ℚ))).mp (hgrid t₁)
    exact False.elim (hnonaligned (AffineGridAlignment.of_affine_grid B X Y p q hXB hYB
      (hbound t₀) (hbound t₁) hne α β hpLine hqLine ((hline (X : ℚ) (Y : ℚ)).mp hpnt)))

end PaperP1.CurveCoverNonalignedBound
