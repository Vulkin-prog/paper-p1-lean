module

public import PaperP1.Diophantine.GeometricProjectiveFibres
public import PaperP1.Diophantine.ProjectiveUnitCharts
public import PaperP1.Algebra.BivariateHeight
public import Mathlib.Data.ZMod.Units
public import Mathlib.RingTheory.Int.Basic

/-! # Exact rational-root divisibility and coordinate bounds for primitive binary zeros -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveHomogeneousRootBound

open Polynomial Finset PaperP1.HomogeneousCharts

theorem eval_homogenize_other_axis {R : Type*} [CommRing R] (P : R[X]) (d : ℕ) (t : R) :
    MvPolynomial.eval ![0, t] (P.homogenize d) = P.coeff 0 * t ^ d := by
  classical
  rw [Polynomial.homogenize, map_sum]
  simp only [MvPolynomial.eval_monomial]
  rw [Finset.sum_eq_single (0, d)]
  · simp
  · intro kl hkl hne
    have hs := Finset.mem_antidiagonal.mp hkl
    have hz : kl.1 ≠ 0 := by
      intro hzero
      apply hne
      exact Prod.ext hzero (by omega)
    simp [zero_pow hz]
  · intro hnot
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr (by omega)))

theorem endpoint_divisibility (P : ℤ[X]) (d : ℕ) (u v : ℤ)
    (hprim : u.natAbs.Coprime v.natAbs)
    (hz : MvPolynomial.eval ![u, v] (P.homogenize d) = 0) :
    u ∣ P.coeff 0 ∧ v ∣ P.coeff d := by
  have hmod (n : ℕ) : MvPolynomial.eval ![(u : ZMod n), (v : ZMod n)]
      ((P.map (Int.castRingHom (ZMod n))).homogenize d) = 0 := by
    rw [Polynomial.homogenize_map, MvPolynomial.eval_map]
    have hm := congrArg (Int.castRingHom (ZMod n)) hz
    rw [MvPolynomial.eval₂_comp, map_zero] at hm
    have he : ![(u : ZMod n), (v : ZMod n)] = (Int.castRingHom (ZMod n)) ∘ ![u, v] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact hm
  have cast_zero (w : ℤ) : (w : ZMod w.natAbs) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    rw [← Int.natAbs_dvd_natAbs]
    simp
  have unit_cast (w t : ℤ) (hc : w.natAbs.Coprime t.natAbs) : IsUnit (t : ZMod w.natAbs) := by
    apply (ZMod.isUnit_intCast_iff_isCoprime _ _).mpr
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact hc
  have recover (w c : ℤ) (hc : (c : ZMod w.natAbs) = 0) : w ∣ c := by
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd c w.natAbs).mp hc
    rw [← Int.natAbs_dvd_natAbs] at hd ⊢
    simpa only [Int.natAbs_natCast] using hd
  constructor
  · have he := hmod u.natAbs
    rw [cast_zero, eval_homogenize_other_axis, Polynomial.coeff_map] at he
    apply recover u
    exact ((unit_cast u v hprim).pow d).mul_left_eq_zero.mp he
  · have he := hmod v.natAbs
    rw [cast_zero, HomogeneousChartSpecialization.eval_homogenize_axis, Polynomial.coeff_map] at he
    apply recover v
    exact ((unit_cast v u hprim.symm).pow d).mul_left_eq_zero.mp he

theorem coordinate_natAbs_bounds (P : ℤ[X]) (d : ℕ) (u v : ℤ)
    (hprim : u.natAbs.Coprime v.natAbs)
    (hz : MvPolynomial.eval ![u, v] (P.homogenize d) = 0)
    (hconstant : P.coeff 0 ≠ 0) (hleading : P.coeff d ≠ 0) :
    u.natAbs ≤ (P.coeff 0).natAbs ∧ v.natAbs ≤ (P.coeff d).natAbs := by
  have hd := endpoint_divisibility P d u v hprim hz
  exact ⟨Int.natAbs_le_of_dvd_ne_zero hd.1 hconstant,
    Int.natAbs_le_of_dvd_ne_zero hd.2 hleading⟩

theorem evaluation_bound (P : ℤ[X]) (d : ℕ) (hd : P.natDegree ≤ d)
    (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hc : ∀ i, |(P.coeff i : ℝ)| ≤ A) (x : Fin 2 → ℤ)
    (hx : ∀ c, |(x c : ℝ)| ≤ L) :
    |((MvPolynomial.eval x (P.homogenize d) : ℤ) : ℝ)| ≤ (d + 1) * A * L ^ d := by
  have he := BihomogeneousSwap.eval_binary_expansion (P.homogenize d)
    (Polynomial.isHomogeneous_homogenize P) x
  simp only [chart, Polynomial.aeval_homogenize_X_one P hd] at he
  rw [he, Int.cast_sum]
  calc
    _ ≤ ∑ i : Fin (d + 1), |((P.coeff i.val * x 0 ^ i.val * x 1 ^ (d - i.val) : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (d + 1), A * L ^ d := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Int.cast_mul, Int.cast_pow, abs_mul, abs_pow]
      calc
        _ ≤ A * L ^ i.val * L ^ (d - i.val) := by gcongr; exacts [hc i.val, hx 0, hx 1]
        _ = A * L ^ d := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (by have := i.isLt; omega)]
    _ = _ := by simp [mul_assoc]

theorem fibre_coordinate_bounds (G : ℤ[X][X]) (x y : Fin 2 → ℤ)
    (hprim : (y 0).natAbs.Coprime (y 1).natAbs)
    (hz : MvPolynomial.eval₂ (MvPolynomial.eval y) x (IntegerFactorProjectiveCurve.projective G) = 0)
    (hconstant : MvPolynomial.eval x ((G.coeff 0).homogenize (BivariateDegrees.degreeX G)) ≠ 0)
    (hleading : MvPolynomial.eval x
      ((G.coeff (BivariateDegrees.degreeY G)).homogenize (BivariateDegrees.degreeX G)) ≠ 0) :
    (y 0).natAbs ≤ (MvPolynomial.eval x
      ((G.coeff 0).homogenize (BivariateDegrees.degreeX G))).natAbs ∧
    (y 1).natAbs ≤ (MvPolynomial.eval x
      ((G.coeff (BivariateDegrees.degreeY G)).homogenize (BivariateDegrees.degreeX G))).natAbs := by
  let F := GeometricProjectiveFibres.fibre G x
  have hh := GeometricProjectiveFibres.fibre_homogeneous G x
  have hy : ![y 0, y 1] = y := by funext i; fin_cases i <;> rfl
  have he : MvPolynomial.eval ![y 0, y 1] ((chart F).homogenize (BivariateDegrees.degreeY G)) = 0 := by
    rw [chart_homogenize F hh, hy, GeometricProjectiveFibres.fibre_evaluation]
    exact hz
  have hc : (chart F).coeff 0 ≠ 0 := by
    rw [GeometricProjectiveFibres.fibre_chart_coefficient G x 0 (Nat.zero_le _)]
    exact hconstant
  have hl : (chart F).coeff (BivariateDegrees.degreeY G) ≠ 0 := by
    rw [GeometricProjectiveFibres.fibre_chart_coefficient G x _ le_rfl]
    exact hleading
  have hb := coordinate_natAbs_bounds (chart F) (BivariateDegrees.degreeY G) (y 0) (y 1) hprim he hc hl
  simpa only [F, GeometricProjectiveFibres.fibre_chart_coefficient G x 0 (Nat.zero_le _),
    GeometricProjectiveFibres.fibre_chart_coefficient G x _ le_rfl] using hb

theorem fibre_height_bound (G : ℤ[X][X]) (x y : Fin 2 → ℤ)
    (hprim : (y 0).natAbs.Coprime (y 1).natAbs)
    (hz : MvPolynomial.eval₂ (MvPolynomial.eval y) x (IntegerFactorProjectiveCurve.projective G) = 0)
    (hconstant : MvPolynomial.eval x ((G.coeff 0).homogenize (BivariateDegrees.degreeX G)) ≠ 0)
    (hleading : MvPolynomial.eval x
      ((G.coeff (BivariateDegrees.degreeY G)).homogenize (BivariateDegrees.degreeX G)) ≠ 0)
    (L : ℝ) (hL : 0 ≤ L) (hx : ∀ c, |(x c : ℝ)| ≤ L) :
    ∀ c, |(y c : ℝ)| ≤ (BivariateDegrees.degreeX G + 1) * (BivariateHeight.height G : ℝ) *
      L ^ BivariateDegrees.degreeX G := by
  have hb := fibre_coordinate_bounds G x y hprim hz hconstant hleading
  have hreal (z t : ℤ) (hn : z.natAbs ≤ t.natAbs) : |(z : ℝ)| ≤ |(t : ℝ)| := by
    have hc : (z.natAbs : ℝ) ≤ (t.natAbs : ℝ) := by exact_mod_cast hn
    simpa only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] using hc
  have he (j : ℕ) := evaluation_bound (G.coeff j) (BivariateDegrees.degreeX G)
    (BivariateDegrees.natDegree_coeff_le_degreeX G j) (BivariateHeight.height G : ℝ) L
    (Nat.cast_nonneg _) hL (by
      intro i
      have hc := BivariateHeight.coefficient_natAbs_le_height G j i
      have hc' : (((G.coeff j).coeff i).natAbs : ℝ) ≤ (BivariateHeight.height G : ℝ) := by exact_mod_cast hc
      simpa only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] using hc') x hx
  intro c
  fin_cases c
  · exact (hreal _ _ hb.1).trans (he 0)
  · exact (hreal _ _ hb.2).trans (he (BivariateDegrees.degreeY G))

end PaperP1.PrimitiveHomogeneousRootBound
