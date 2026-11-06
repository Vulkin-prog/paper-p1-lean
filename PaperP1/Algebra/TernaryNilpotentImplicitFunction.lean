module

public import PaperP1.Algebra.BivariateNilpotentImplicitFunction
public import PaperP1.Algebra.TernaryPolynomialEvaluation

/-! # Two free polynomial parameters on a nilpotent smooth surface branch -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryNilpotentImplicitFunction

open Polynomial PaperP1.NilpotentPolynomialParameter

variable {R : Type*} [CommRing R]

def localMap (N : ℕ) (a : R) : R[X][X][X] →+* (Trunc R N)[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom
    (Polynomial.eval₂RingHom (algebraMap R (Trunc R N))
      (algebraMap R (Trunc R N) a + parameter R N)))

def localPolynomial (N : ℕ) (a : R) (P : R[X][X][X]) : (Trunc R N)[X][X] :=
  localMap N a P

theorem local_evaluation_mod (I : Ideal R) (N : ℕ) (a b c : R) (P : R[X][X][X]) :
    Ideal.Quotient.mk (liftedIdeal I N)
      ((localPolynomial N a P).evalEval
        (algebraMap R (Trunc R N) b) (algebraMap R (Trunc R N) c)) =
      Ideal.Quotient.mk (liftedIdeal I N)
        (algebraMap R (Trunc R N) (TernaryPolynomialEvaluation.evaluation a b c P)) := by
  let φ := algebraMap R (Trunc R N)
  let ψ := Ideal.Quotient.mk (liftedIdeal I N)
  have hτ : ψ (parameter R N) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (parameter_mem I N)
  have he : ψ.comp ((Polynomial.evalEvalRingHom (φ b) (φ c)).comp (localMap N a)) =
      (ψ.comp φ).comp (TernaryPolynomialEvaluation.evaluation a b c) := by
    ext <;> simp [localMap, TernaryPolynomialEvaluation.evaluation, RingHom.comp_apply, hτ, φ]
  exact RingHom.congr_fun he P

theorem local_derivative_mod (I : Ideal R) (N : ℕ) (a b c : R) (P : R[X][X][X]) :
    Ideal.Quotient.mk (liftedIdeal I N)
      ((localPolynomial N a P).derivative.evalEval
        (algebraMap R (Trunc R N) b) (algebraMap R (Trunc R N) c)) =
      Ideal.Quotient.mk (liftedIdeal I N)
        (algebraMap R (Trunc R N) (TernaryPolynomialEvaluation.evaluation a b c P.derivative)) := by
  have hd : (localPolynomial N a P).derivative = localPolynomial N a P.derivative := by
    simp only [localPolynomial, localMap, Polynomial.coe_mapRingHom, Polynomial.derivative_map]
  rw [hd]
  exact local_evaluation_mod I N a b c P.derivative

theorem exists_local_branch (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (P : R[X][X][X]) (a b c : R)
    (hP : TernaryPolynomialEvaluation.evaluation a b c P ∈ I)
    (hder : IsUnit (Ideal.Quotient.mk I (TernaryPolynomialEvaluation.evaluation a b c P.derivative))) :
    ∃ q : (Trunc R N)[X], ∀ t ∈ liftedIdeal I N,
      (localPolynomial N a P).evalEval (algebraMap R (Trunc R N) b + t) (q.eval t) = 0 ∧
        q.eval t - algebraMap R (Trunc R N) c ∈ liftedIdeal I N := by
  let φ := algebraMap R (Trunc R N)
  let ψ := Ideal.Quotient.mk (liftedIdeal I N)
  have hker : ∀ r ∈ I, (ψ.comp φ) r = 0 := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (base_mem I N r hr)
  let θ := Ideal.Quotient.lift I (ψ.comp φ) hker
  have hdu : IsUnit (ψ (φ (TernaryPolynomialEvaluation.evaluation a b c P.derivative))) := by
    have hu := hder.map θ
    simpa only [θ, Ideal.Quotient.lift_mk, RingHom.comp_apply] using hu
  have hroot : (localPolynomial N a P).evalEval (φ b) (φ c) ∈ liftedIdeal I N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [local_evaluation_mod]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (base_mem I N _ hP)
  have hd : IsUnit (ψ ((localPolynomial N a P).derivative.evalEval (φ b) (φ c))) := by
    rw [local_derivative_mod]
    exact hdu
  exact BivariateNilpotentImplicitFunction.exists_polynomial_branch
    (liftedIdeal I N) (N + N) (liftedIdeal_pow I N hN)
    (localPolynomial N a P) (φ b) (φ c) hroot hd

theorem evaluate_local (N : ℕ) (a : R) (P : R[X][X][X]) (x y : Trunc R N)
    (t : R) (ht : t ^ N = 0) :
    evaluation N t ht ((localPolynomial N a P).evalEval x y) =
      TernaryPolynomialEvaluation.evaluation (a + t) (evaluation N t ht x)
        (evaluation N t ht y) P := by
  let ε := evaluation N t ht
  have hbase (r : R) : evaluation N t ht (AdjoinRoot.of ((Polynomial.X : R[X]) ^ N) r) = r :=
    evaluation_base N t ht r
  have he : ε.comp ((Polynomial.evalEvalRingHom x y).comp (localMap N a)) =
      TernaryPolynomialEvaluation.evaluation (a + t) (ε x) (ε y) := by
    ext <;> simp [localMap, TernaryPolynomialEvaluation.evaluation,
      RingHom.comp_apply, ε, hbase, evaluation_parameter]
  exact RingHom.congr_fun he P

theorem evaluate_lift (N : ℕ) (q : (Trunc R N)[X]) (Q : R[X][X])
    (hQ : Q.map (AdjoinRoot.mk ((Polynomial.X : R[X]) ^ N)) = q)
    (t u : R) (ht : t ^ N = 0) :
    evaluation N t ht (q.eval (algebraMap R (Trunc R N) u)) = Q.evalEval t u := by
  rw [← hQ, Polynomial.eval_map]
  change evaluation N t ht
    ((Polynomial.eval₂RingHom (AdjoinRoot.mk ((Polynomial.X : R[X]) ^ N))
      (algebraMap R (Trunc R N) u)) Q) = _
  have he : (evaluation N t ht).comp
      (Polynomial.eval₂RingHom (AdjoinRoot.mk ((Polynomial.X : R[X]) ^ N))
        (algebraMap R (Trunc R N) u)) = Polynomial.evalEvalRingHom t u := by
    ext <;> simp [RingHom.comp_apply, evaluation]
  exact RingHom.congr_fun he Q

theorem exists_polynomial_branch (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (P : R[X][X][X]) (a b c : R)
    (hP : TernaryPolynomialEvaluation.evaluation a b c P ∈ I)
    (hder : IsUnit (Ideal.Quotient.mk I (TernaryPolynomialEvaluation.evaluation a b c P.derivative))) :
    ∃ Q : R[X][X], ∀ t ∈ I, ∀ u ∈ I,
      TernaryPolynomialEvaluation.evaluation (a + t) (b + u) (Q.evalEval t u) P = 0 ∧
        Q.evalEval t u - c ∈ I := by
  obtain ⟨q, hq⟩ := exists_local_branch I N hN P a b c hP hder
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective
    (AdjoinRoot.mk ((Polynomial.X : R[X]) ^ N)) AdjoinRoot.mk_surjective q
  refine ⟨Q, ?_⟩
  intro t htI u huI
  have ht : t ^ N = 0 := by
    have hm := Ideal.pow_mem_pow htI N
    rw [hN] at hm
    exact hm
  have hbranch := hq (algebraMap R (Trunc R N) u) (base_mem I N u huI)
  have hvalue := evaluate_lift N q Q hQ t u ht
  have hroot := congrArg (evaluation N t ht) hbranch.1
  rw [map_zero, evaluate_local, map_add, evaluation_base, evaluation_base, hvalue] at hroot
  have hm := Ideal.mem_map_of_mem (evaluation N t ht) hbranch.2
  have hmem := evaluation_ideal_le I N t ht htI hm
  have hres : Q.evalEval t u - c ∈ I := by
    simpa only [map_sub, evaluation_base, hvalue] using hmem
  exact ⟨hroot, hres⟩

theorem unique_fibre_root (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (P : R[X][X][X]) (a b c x y z w : R)
    (hder : IsUnit (Ideal.Quotient.mk I (TernaryPolynomialEvaluation.evaluation a b c P.derivative)))
    (hx : x - a ∈ I) (hy : y - b ∈ I) (hz : z - c ∈ I) (hw : w - c ∈ I)
    (hPz : TernaryPolynomialEvaluation.evaluation x y z P = 0)
    (hPw : TernaryPolynomialEvaluation.evaluation x y w P = 0) : z = w := by
  let Q := P.map (Polynomial.evalEvalRingHom x y)
  have hQz : Q.eval z = 0 := by
    simpa only [Q, Polynomial.eval_map, TernaryPolynomialEvaluation.evaluation,
      Polynomial.coe_eval₂RingHom] using hPz
  have hQw : Q.eval w = 0 := by
    simpa only [Q, Polynomial.eval_map, TernaryPolynomialEvaluation.evaluation,
      Polynomial.coe_eval₂RingHom] using hPw
  have hde : Q.derivative.eval w = TernaryPolynomialEvaluation.evaluation x y w P.derivative := by
    simp only [Q, Polynomial.derivative_map, Polynomial.eval_map,
      TernaryPolynomialEvaluation.evaluation, Polynomial.coe_eval₂RingHom]
  have hdu : IsUnit (Ideal.Quotient.mk I (Q.derivative.eval w)) := by
    rw [hde, TernaryPolynomialEvaluation.quotient_evaluation_eq I P.derivative a b c x y w hx hy hw]
    exact hder
  have hzw : z - w ∈ I := by
    have he : (z - c) - (w - c) = z - w := by ring
    rw [← he]
    exact I.sub_mem hz hw
  exact NilpotentSimpleRoot.unique_root I N hN Q z w hQz hQw hzw hdu

theorem exists_polynomial_implicit (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (P : R[X][X][X]) (a b c : R)
    (hP : TernaryPolynomialEvaluation.evaluation a b c P ∈ I)
    (hder : IsUnit (Ideal.Quotient.mk I (TernaryPolynomialEvaluation.evaluation a b c P.derivative))) :
    ∃ Q : R[X][X], ∀ x y z : R, x - a ∈ I → y - b ∈ I → z - c ∈ I →
      TernaryPolynomialEvaluation.evaluation x y z P = 0 →
        z = Q.evalEval (x - a) (y - b) := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_branch I N hN P a b c hP hder
  refine ⟨Q, ?_⟩
  intro x y z hx hy hz hzero
  have hbq := hQ (x - a) hx (y - b) hy
  have hex : a + (x - a) = x := by ring
  have hey : b + (y - b) = y := by ring
  rw [hex, hey] at hbq
  exact unique_fibre_root I N hN P a b c x y z (Q.evalEval (x - a) (y - b))
    hder hx hy hz hbq.2 hzero hbq.1

end PaperP1.TernaryNilpotentImplicitFunction
