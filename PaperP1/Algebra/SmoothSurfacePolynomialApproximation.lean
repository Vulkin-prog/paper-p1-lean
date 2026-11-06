module

public import PaperP1.Algebra.NormalizedP3SurfaceDeterminant

/-! # One actual polynomial substitution approximates every polynomial on every point of a smooth class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothSurfacePolynomialApproximation

open Polynomial MvPolynomial

theorem ternary_integer (p N : ℕ) (hp : p.Prime) (P : ℤ[X][X][X]) (a b c : ℤ)
    (hP : (p : ℤ) ∣ TernaryPolynomialEvaluation.evaluation a b c P)
    (hder : ¬(p : ℤ) ∣ TernaryPolynomialEvaluation.evaluation a b c P.derivative) :
    ∃ T : ℤ[X][X][X] →+* MvPolynomial (Fin 2) ℤ, ∀ x y z : ℤ,
      (p : ℤ) ∣ x - a → (p : ℤ) ∣ y - b → (p : ℤ) ∣ z - c →
      TernaryPolynomialEvaluation.evaluation x y z P = 0 → ∀ F : ℤ[X][X][X],
      (p : ℤ) ^ N ∣ TernaryPolynomialEvaluation.evaluation x y z F -
        MvPolynomial.eval ![x - a, y - b] (T F) := by
  obtain ⟨q, hq⟩ := SmoothIntegerSurfaceBranch.implicit_mod_prime_power p N hp P a b c hP hder
  refine ⟨IteratedBivariatePolynomialDeterminant.toMv.comp
    (SmoothSurfaceDeterminant.substitution a b q), ?_⟩
  intro x y z hx hy hz hroot F
  have hd := (hq x y z hx hy hz hroot).trans
    (Polynomial.sub_dvd_eval_sub z (q.evalEval (x - a) (y - b))
      (F.map (Polynomial.evalEvalRingHom x y)))
  change (p : ℤ) ^ N ∣ TernaryPolynomialEvaluation.evaluation x y z F -
    MvPolynomial.eval ![x - a, y - b]
      (IteratedBivariatePolynomialDeterminant.toMv (SmoothSurfaceDeterminant.substitution a b q F))
  rw [IteratedBivariatePolynomialDeterminant.evaluation, SmoothSurfaceDeterminant.substitution_eval]
  have hxa : a + (x - a) = x := by ring
  have hyb : b + (y - b) = y := by ring
  rw [hxa, hyb]
  simpa only [Polynomial.eval_map, TernaryPolynomialEvaluation.evaluation,
    Polynomial.coe_eval₂RingHom] using hd

theorem affine_last (p N : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 3) ℤ) (a : Fin 3 → ℤ)
    (hP : (p : ℤ) ∣ MvPolynomial.eval a P)
    (hder : ¬(p : ℤ) ∣ MvPolynomial.eval a (pderiv 2 P)) :
    ∃ T : MvPolynomial (Fin 3) ℤ →+* MvPolynomial (Fin 2) ℤ,
      ∀ v : Fin 3 → ℤ, (∀ k, (p : ℤ) ∣ v k - a k) → MvPolynomial.eval v P = 0 →
      ∀ F : MvPolynomial (Fin 3) ℤ,
      (p : ℤ) ^ N ∣ MvPolynomial.eval v F -
        MvPolynomial.eval ![v 0 - a 0, v 1 - a 1] (T F) := by
  have ha : ![a 0, a 1, a 2] = a := by ext k; fin_cases k <;> rfl
  obtain ⟨T, hT⟩ := ternary_integer p N hp (TernaryMvPolynomialEvaluation.iterated P)
    (a 0) (a 1) (a 2)
    (by simpa only [TernaryMvPolynomialEvaluation.evaluation, ha] using hP)
    (by simpa only [TernaryMvPolynomialEvaluation.derivative,
      TernaryMvPolynomialEvaluation.evaluation, ha] using hder)
  refine ⟨T.comp TernaryMvPolynomialEvaluation.iterated, ?_⟩
  intro v hv hroot F
  have hv' : ![v 0, v 1, v 2] = v := by ext k; fin_cases k <;> rfl
  have hroot' : TernaryPolynomialEvaluation.evaluation (v 0) (v 1) (v 2)
      (TernaryMvPolynomialEvaluation.iterated P) = 0 := by
    simpa only [TernaryMvPolynomialEvaluation.evaluation, hv'] using hroot
  simpa only [TernaryMvPolynomialEvaluation.evaluation, hv', RingHom.comp_apply] using
    hT (v 0) (v 1) (v 2) (hv 0) (hv 1) (hv 2) hroot' (TernaryMvPolynomialEvaluation.iterated F)

theorem affine_integer (p N : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 3) ℤ) (a : Fin 3 → ℤ)
    (hP : (p : ℤ) ∣ MvPolynomial.eval a P)
    (hgrad : ∃ k, ¬(p : ℤ) ∣ MvPolynomial.eval a (pderiv k P)) :
    ∃ (x y : (Fin 3 → ℤ) → ℤ) (T : MvPolynomial (Fin 3) ℤ →+* MvPolynomial (Fin 2) ℤ),
      ∀ v : Fin 3 → ℤ, (∀ k, (p : ℤ) ∣ v k - a k) → MvPolynomial.eval v P = 0 →
        (p : ℤ) ∣ x v ∧ (p : ℤ) ∣ y v ∧ ∀ F : MvPolynomial (Fin 3) ℤ,
        (p : ℤ) ^ N ∣ MvPolynomial.eval v F - MvPolynomial.eval ![x v, y v] (T F) := by
  obtain ⟨k, hk⟩ := hgrad
  let e := Equiv.swap k (2 : Fin 3)
  have hPe : (p : ℤ) ∣ MvPolynomial.eval (fun i ↦ a (e i)) (rename e P) := by
    simpa only [e, CoordinateSwapEvaluation.evaluation] using hP
  have hde : ¬(p : ℤ) ∣ MvPolynomial.eval (fun i ↦ a (e i)) (pderiv 2 (rename e P)) := by
    simpa only [e, CoordinateSwapEvaluation.evaluation_partial] using hk
  obtain ⟨T, hT⟩ := affine_last p N hp (rename e P) (fun i ↦ a (e i)) hPe hde
  refine ⟨(fun v ↦ v (e 0) - a (e 0)), (fun v ↦ v (e 1) - a (e 1)),
    T.comp (rename e).toRingHom, ?_⟩
  intro v hv hroot
  refine ⟨hv (e 0), hv (e 1), ?_⟩
  intro F
  have hroot' : MvPolynomial.eval (fun i ↦ v (e i)) (rename e P) = 0 := by
    simpa only [e, CoordinateSwapEvaluation.evaluation] using hroot
  simpa only [e, CoordinateSwapEvaluation.evaluation, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
    hT (fun i ↦ v (e i)) (fun i ↦ hv (e i)) hroot' (rename e F)

theorem normalized_integer (p N d : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) (a : Fin 4 → ℤ) (ha : a 3 = 1)
    (hP : (p : ℤ) ∣ MvPolynomial.eval a P)
    (hgrad : ∃ k, ¬(p : ℤ) ∣ MvPolynomial.eval a (pderiv k P)) :
    ∃ (x y : (Fin 4 → ℤ) → ℤ) (T : MvPolynomial (Fin 4) ℤ →+* MvPolynomial (Fin 2) ℤ),
      ∀ v : Fin 4 → ℤ, v 3 = 1 → (∀ k, (p : ℤ) ∣ v k - a k) → MvPolynomial.eval v P = 0 →
        (p : ℤ) ∣ x v ∧ (p : ℤ) ∣ y v ∧ ∀ F : MvPolynomial (Fin 4) ℤ,
        (p : ℤ) ^ N ∣ MvPolynomial.eval v F - MvPolynomial.eval ![x v, y v] (T F) := by
  have ha' : Fin.snoc (fun k : Fin 3 ↦ a k.castSucc) 1 = a := by
    funext k
    cases k using Fin.lastCases with
    | last => exact (Fin.snoc_last _ _).trans ha.symm
    | cast k => exact Fin.snoc_castSucc _ _ k
  have hbase : (p : ℤ) ∣ MvPolynomial.eval (fun k : Fin 3 ↦ a k.castSucc)
      (LastChartPolynomial.dehomogenize P) := by
    simpa only [LastChartPolynomial.evaluation, ha'] using hP
  have hder : ∃ k, ¬(p : ℤ) ∣ MvPolynomial.eval (fun k : Fin 3 ↦ a k.castSucc)
      (pderiv k (LastChartPolynomial.dehomogenize P)) := by
    obtain ⟨k, hk⟩ := NormalizedP3SurfaceDeterminant.free_partial p d P hhom a ha hP hgrad
    exact ⟨k, by simpa only [LastChartPolynomial.pderiv, LastChartPolynomial.evaluation, ha'] using hk⟩
  obtain ⟨x, y, T, hT⟩ := affine_integer p N hp (LastChartPolynomial.dehomogenize P)
    (fun k : Fin 3 ↦ a k.castSucc) hbase hder
  refine ⟨(fun v ↦ x (fun k ↦ v k.castSucc)), (fun v ↦ y (fun k ↦ v k.castSucc)),
    T.comp LastChartPolynomial.dehomogenize, ?_⟩
  intro v hvlast hv hroot
  have hv' : Fin.snoc (fun k : Fin 3 ↦ v k.castSucc) 1 = v := by
    funext k
    cases k using Fin.lastCases with
    | last => exact (Fin.snoc_last _ _).trans hvlast.symm
    | cast k => exact Fin.snoc_castSucc _ _ k
  have hroot' : MvPolynomial.eval (fun k : Fin 3 ↦ v k.castSucc)
      (LastChartPolynomial.dehomogenize P) = 0 := by
    simpa only [LastChartPolynomial.evaluation, hv'] using hroot
  obtain ⟨hx, hy, hF⟩ := hT (fun k : Fin 3 ↦ v k.castSucc) (fun k ↦ hv k.castSucc) hroot'
  refine ⟨hx, hy, ?_⟩
  intro F
  simpa only [LastChartPolynomial.evaluation, hv', RingHom.comp_apply] using
    hF (LastChartPolynomial.dehomogenize F)

end PaperP1.SmoothSurfacePolynomialApproximation
