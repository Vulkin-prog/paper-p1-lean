module

public import PaperP1.Algebra.UniversalRadicalProjectionEvaluation
public import PaperP1.Algebra.MvPolynomialSubstitutionDegree
public import PaperP1.Algebra.SplitRadicalProjectionPolynomial

/-! # The actual image equation has degree bounded only by the number and sizes of its root lists -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalProjectionDegree

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.ScaledSplitWordSquares
  PaperP1.SplitRadicalCoordinateAlgebra PaperP1.SplitRadicalProjectionPolynomial
  PaperP1.UniversalRadicalProjection PaperP1.UniversalRadicalProjectionEvaluation
  PaperP1.TrivariatePolynomialEquiv

theorem coefficientLift_linear_left {F : Type*} [Field F] (I : Finset ℤ) :
    coefficientLift F (C (linearOver F I)) = ∏ i ∈ I, (MvPolynomial.X 2 + MvPolynomial.C (i : F)) := by
  simp only [linearOver, map_prod, map_add, coefficientLift_CX, coefficientLift_CC]

theorem coefficientLift_linear_right {F : Type*} [Field F] (I : Finset ℤ) :
    coefficientLift F ((linearOver F I).map C) = ∏ i ∈ I, (MvPolynomial.X 1 + MvPolynomial.C (i : F)) := by
  simp only [linearOver, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    map_prod, map_add, coefficientLift_X, coefficientLift_CC]

theorem coefficientLift_scaled {F : Type*} [Field F] (c : F) (I J : Finset ℤ) :
    coefficientLift F (scaledPolynomial c I J) = MvPolynomial.C c *
      (∏ i ∈ I, (MvPolynomial.X 2 + MvPolynomial.C (i : F))) *
      ∏ j ∈ J, (MvPolynomial.X 1 + MvPolynomial.C (j : F)) := by
  rw [scaledPolynomial, wordOver, map_mul, map_mul, coefficientLift_CC,
    coefficientLift_linear_left, coefficientLift_linear_right, mul_assoc]

theorem linear_product_degree_le {F : Type*} [Field F] (j : Fin 3) (I : Finset ℤ) :
    (∏ i ∈ I, (MvPolynomial.X j + MvPolynomial.C (i : F))).totalDegree ≤ I.card := by
  let p : ℤ → MvPolynomial (Fin 3) F := fun i ↦ MvPolynomial.X j + MvPolynomial.C (i : F)
  have hlinear : ∀ i : ℤ, (p i).totalDegree ≤ 1 := by
    intro i
    have hh := MvPolynomial.totalDegree_add (MvPolynomial.X j : MvPolynomial (Fin 3) F) (MvPolynomial.C (i : F))
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] at hh
    exact hh.trans (max_le (Nat.le_refl 1) (Nat.zero_le 1))
  have hprod := MvPolynomial.totalDegree_finsetProd I p
  have hsum : (∑ i ∈ I, (p i).totalDegree) ≤ I.card := by
    calc
      (∑ i ∈ I, (p i).totalDegree) ≤ ∑ _i ∈ I, (1 : ℕ) := sum_le_sum fun i _ ↦ hlinear i
      _ = I.card := by simp
  exact hprod.trans hsum

theorem coefficientLift_scaled_degree {F : Type*} [Field F] (c : F) (I J : Finset ℤ) :
    (coefficientLift F (scaledPolynomial c I J)).totalDegree ≤ I.card + J.card := by
  rw [coefficientLift_scaled]
  have hleft : (MvPolynomial.C c * ∏ i ∈ I, (MvPolynomial.X (2 : Fin 3) + MvPolynomial.C (i : F))).totalDegree ≤ I.card := by
    have hh := (MvPolynomial.totalDegree_mul (MvPolynomial.C c)
      (∏ i ∈ I, (MvPolynomial.X (2 : Fin 3) + MvPolynomial.C (i : F))))
    rw [MvPolynomial.totalDegree_C, zero_add] at hh
    exact hh.trans (linear_product_degree_le 2 I)
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hleft (linear_product_degree_le 1 J))

theorem equation_totalDegree_upper (F K : Type*) [CommRing F] [IsDomain F] [Field K] [CharZero K]
    [Algebra F[X][X] K] [IsFractionRing F[X][X] K] (s : List F[X][X])
    (hs : PaperP1.IndependentQuadraticTower.Independent (s.map (algebraMap F[X][X] K)))
    (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ i, (coefficientLift F (s.get i)).totalDegree ≤ d) :
    (asMvPolynomial F (PaperP1.RadicalProjectionPolynomial.equation F[X][X] s)).totalDegree ≤ degreeConstant s.length * d := by
  have hsub : ∀ o, (substitution F s o).totalDegree ≤ d := by
    intro o
    cases o with
    | none => simpa only [substitution, MvPolynomial.totalDegree_X] using hd
    | some i => exact hdegree i
  have hh := MvPolynomialSubstitutionDegree.totalDegree_eval2_le (Int.castRingHom F)
    (substitution F s) d hsub (universalPolynomial s.length)
  change (evaluateUniversal F s (universalPolynomial s.length)).totalDegree ≤ degreeConstant s.length * d at hh
  rw [evaluation_eq_equation F K s hs] at hh
  exact hh

theorem source_surface_degree_upper {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (K : ℕ) (hK : ∀ i, (I i).card + (J i).card ≤ K) :
    (sourceSurfaceEquation l c I J).totalDegree ≤ degreeConstant l.length * max 1 K := by
  have hdegree : ∀ i : Fin (radicands l c I J).length,
      (coefficientLift F ((radicands l c I J).get i)).totalDegree ≤ max 1 K := by
    intro i
    have hmem : (radicands l c I J).get i ∈ l.map (fun j ↦ scaledPolynomial (c j) (I j) (J j)) := List.get_mem _ i
    obtain ⟨j, _hj, heq⟩ := List.mem_map.mp hmem
    rw [← heq]
    exact (coefficientLift_scaled_degree (c j) (I j) (J j)).trans ((hK j).trans (Nat.le_max_right 1 K))
  have hh := equation_totalDegree_upper F (FunctionField F) (radicands l c I J)
    (generic_independent l hl c hc I J hne hI hJ) (max 1 K) (Nat.le_max_left 1 K) hdegree
  simpa only [sourceSurfaceEquation, sourceEquation, radicands, List.length_map] using hh

end PaperP1.SplitRadicalProjectionDegree
