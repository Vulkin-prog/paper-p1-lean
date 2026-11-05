module

public import PaperP1.Algebra.NilpotentPolynomialParameter
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # A finite implicit polynomial branch over a nilpotent ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateNilpotentImplicitFunction

open Polynomial PaperP1.NilpotentPolynomialParameter

variable {R : Type*} [CommRing R]

def localPolynomial (N : ℕ) (a : R) (P : R[X][X]) : (Trunc R N)[X] :=
  P.map (Polynomial.eval₂RingHom (algebraMap R (Trunc R N))
    (algebraMap R (Trunc R N) a + parameter R N))

theorem local_evaluation_mod (I : Ideal R) (N : ℕ) (a b : R) (P : R[X][X]) :
    Ideal.Quotient.mk (liftedIdeal I N)
      ((localPolynomial N a P).eval (algebraMap R (Trunc R N) b)) =
      Ideal.Quotient.mk (liftedIdeal I N) (algebraMap R (Trunc R N) (P.evalEval a b)) := by
  let φ := algebraMap R (Trunc R N)
  let ψ := Ideal.Quotient.mk (liftedIdeal I N)
  have hτ : ψ (parameter R N) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (parameter_mem I N)
  have he : ψ.comp (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom φ (φ a + parameter R N)) (φ b)) =
      (ψ.comp φ).comp (Polynomial.evalEvalRingHom a b) := by
    ext <;> simp [RingHom.comp_apply, hτ]
  have h := RingHom.congr_fun he P
  simpa only [RingHom.comp_apply, localPolynomial, Polynomial.eval_map,
    Polynomial.coe_eval₂RingHom, Polynomial.coe_evalEvalRingHom,
    Polynomial.coe_evalRingHom, Polynomial.evalEval] using h

theorem local_derivative_mod (I : Ideal R) (N : ℕ) (a b : R) (P : R[X][X]) :
    Ideal.Quotient.mk (liftedIdeal I N)
      ((localPolynomial N a P).derivative.eval (algebraMap R (Trunc R N) b)) =
      Ideal.Quotient.mk (liftedIdeal I N) (algebraMap R (Trunc R N) (P.derivative.evalEval a b)) := by
  have hd : (localPolynomial N a P).derivative = localPolynomial N a P.derivative := by
    simp only [localPolynomial, Polynomial.derivative_map]
  rw [hd]
  exact local_evaluation_mod I N a b P.derivative

theorem exists_local_root (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (P : R[X][X]) (a b : R) (hP : P.evalEval a b ∈ I)
    (hder : IsUnit (Ideal.Quotient.mk I (P.derivative.evalEval a b))) :
    ∃ u : Trunc R N, (localPolynomial N a P).eval u = 0 ∧
      u - algebraMap R (Trunc R N) b ∈ liftedIdeal I N := by
  let φ := algebraMap R (Trunc R N)
  let ψ := Ideal.Quotient.mk (liftedIdeal I N)
  have hker : ∀ r ∈ I, (ψ.comp φ) r = 0 := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (base_mem I N r hr)
  let θ := Ideal.Quotient.lift I (ψ.comp φ) hker
  have hdu : IsUnit (ψ (φ (P.derivative.evalEval a b))) := by
    have hu := hder.map θ
    simpa only [θ, Ideal.Quotient.lift_mk, RingHom.comp_apply] using hu
  have hroot : (localPolynomial N a P).eval (φ b) ∈ liftedIdeal I N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [local_evaluation_mod]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (base_mem I N _ hP)
  have hd : IsUnit (ψ ((localPolynomial N a P).derivative.eval (φ b))) := by
    rw [local_derivative_mod]
    exact hdu
  exact NilpotentSimpleRoot.exists_root (liftedIdeal I N) (N + N) (liftedIdeal_pow I N hN)
    (localPolynomial N a P) (φ b) hroot hd

theorem evaluate_local (N : ℕ) (a : R) (P : R[X][X]) (u : Trunc R N)
    (t : R) (ht : t ^ N = 0) :
    evaluation N t ht ((localPolynomial N a P).eval u) =
      P.evalEval (a + t) (evaluation N t ht u) := by
  let φ := algebraMap R (Trunc R N)
  let ε := evaluation N t ht
  have hbase (r : R) : evaluation N t ht (AdjoinRoot.of ((Polynomial.X : R[X]) ^ N) r) = r := by
    exact evaluation_base N t ht r
  have he : ε.comp (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom φ (φ a + parameter R N)) u) =
      Polynomial.evalEvalRingHom (a + t) (ε u) := by
    ext <;> simp [RingHom.comp_apply, φ, ε, hbase, evaluation_parameter]
  have h := RingHom.congr_fun he P
  simpa only [RingHom.comp_apply, localPolynomial, Polynomial.eval_map,
    Polynomial.coe_eval₂RingHom, Polynomial.coe_evalEvalRingHom,
    Polynomial.coe_evalRingHom, Polynomial.evalEval] using h

theorem exists_polynomial_branch (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (P : R[X][X]) (a b : R) (hP : P.evalEval a b ∈ I)
    (hder : IsUnit (Ideal.Quotient.mk I (P.derivative.evalEval a b))) :
    ∃ q : R[X], ∀ t ∈ I, P.evalEval (a + t) (q.eval t) = 0 ∧ q.eval t - b ∈ I := by
  obtain ⟨u, hu, hres⟩ := exists_local_root I N hN P a b hP hder
  obtain ⟨q, hq⟩ := exists_polynomial N u
  refine ⟨q, ?_⟩
  intro t htI
  have ht : t ^ N = 0 := by
    have hm := Ideal.pow_mem_pow htI N
    rw [hN] at hm
    exact hm
  have hqu : evaluation N t ht u = q.eval t := by
    rw [← hq, evaluation_polynomial]
  have hroot : P.evalEval (a + t) (q.eval t) = 0 := by
    have he := congrArg (evaluation N t ht) hu
    rw [map_zero, evaluate_local, hqu] at he
    exact he
  have hm := Ideal.mem_map_of_mem (evaluation N t ht) hres
  have hmem := evaluation_ideal_le I N t ht htI hm
  have hres' : q.eval t - b ∈ I := by
    simpa only [map_sub, evaluation_base, hqu] using hmem
  exact ⟨hroot, hres'⟩

theorem quotient_evaluation_eq (I : Ideal R) (P : R[X][X]) (a b x y : R)
    (hx : x - a ∈ I) (hy : y - b ∈ I) :
    Ideal.Quotient.mk I (P.evalEval x y) = Ideal.Quotient.mk I (P.evalEval a b) := by
  let φ := Ideal.Quotient.mk I
  have hxq : φ x = φ a := Ideal.Quotient.eq.mpr hx
  have hyq : φ y = φ b := Ideal.Quotient.eq.mpr hy
  have he : φ.comp (Polynomial.evalEvalRingHom x y) = φ.comp (Polynomial.evalEvalRingHom a b) := by
    ext <;> simp [RingHom.comp_apply, hxq, hyq]
  have h := RingHom.congr_fun he P
  simpa only [RingHom.comp_apply, Polynomial.coe_evalEvalRingHom,
    Polynomial.coe_evalRingHom, Polynomial.evalEval] using h

theorem unique_fibre_root (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (P : R[X][X]) (a b x y z : R)
    (hder : IsUnit (Ideal.Quotient.mk I (P.derivative.evalEval a b)))
    (hx : x - a ∈ I) (hy : y - b ∈ I) (hz : z - b ∈ I)
    (hPy : P.evalEval x y = 0) (hPz : P.evalEval x z = 0) : y = z := by
  let Q := P.map (Polynomial.evalRingHom x)
  have hQy : Q.eval y = 0 := by
    simpa only [Q, Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hPy
  have hQz : Q.eval z = 0 := by
    simpa only [Q, Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hPz
  have hde : Q.derivative.eval z = P.derivative.evalEval x z := by
    simp only [Q, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_evalRingHom]
  have hdu : IsUnit (Ideal.Quotient.mk I (Q.derivative.eval z)) := by
    rw [hde, quotient_evaluation_eq I P.derivative a b x z hx hz]
    exact hder
  have hyz : y - z ∈ I := by
    have he : (y - b) - (z - b) = y - z := by ring
    rw [← he]
    exact I.sub_mem hy hz
  exact NilpotentSimpleRoot.unique_root I N hN Q y z hQy hQz hyz hdu

theorem exists_polynomial_implicit (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (P : R[X][X]) (a b : R) (hP : P.evalEval a b ∈ I)
    (hder : IsUnit (Ideal.Quotient.mk I (P.derivative.evalEval a b))) :
    ∃ q : R[X], ∀ x y : R, x - a ∈ I → y - b ∈ I → P.evalEval x y = 0 →
      y = q.eval (x - a) := by
  obtain ⟨q, hq⟩ := exists_polynomial_branch I N hN P a b hP hder
  refine ⟨q, ?_⟩
  intro x y hx hy hzero
  have hbq := hq (x - a) hx
  have he : a + (x - a) = x := by ring
  rw [he] at hbq
  exact unique_fibre_root I N hN P a b x y (q.eval (x - a)) hder hx hy hbq.2 hzero hbq.1

end PaperP1.BivariateNilpotentImplicitFunction
