module

public import PaperP1.Algebra.HomogeneousPolynomialEvaluation
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Lean.Elab.Tactic.Omega

/-! # A nonzero principal homogeneous polynomial ideal has a homogeneous generator -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousPrincipalIdealGenerator

open MvPolynomial

variable {F σ : Type*} [Field F]

local instance polynomialRing : CommRing (MvPolynomial σ F) := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneous_of_span (p : MvPolynomial σ F) (hp0 : p ≠ 0)
    (hI : (Ideal.span {p}).IsHomogeneous (homogeneousSubmodule σ F)) :
    ∃ e : ℕ, p.IsHomogeneous e := by
  classical
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hp0
  let n := d.degree
  let z := homogeneousComponent n p
  have hzcoeff : z.coeff d = p.coeff d := by simp only [z, coeff_homogeneousComponent, n, ite_true]
  have hz0 : z ≠ 0 := by
    intro hz
    apply hd
    rw [← hzcoeff, hz]
    rfl
  have hzm : z ∈ Ideal.span {p} :=
    homogeneousComponent_mem_of_mem hI (Ideal.mem_span_singleton_self p) n
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hzm
  have hq0 : q ≠ 0 := by intro h; apply hz0; rw [← hq, h, zero_mul]
  have hdeg := congrArg totalDegree hq
  rw [totalDegree_mul_of_isDomain hq0 hp0, (homogeneousComponent_mem n p).totalDegree hz0] at hdeg
  have hn : n ≤ p.totalDegree := by
    simpa only [n, Finsupp.degree_apply, Finsupp.sum] using le_totalDegree (mem_support_iff.mpr hd)
  have hqdeg : q.totalDegree = 0 := by omega
  have hqc : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hqdeg
  have hc : q.coeff 0 ≠ 0 := by
    intro h
    apply hq0
    rw [hqc, h, map_zero]
  rw [hqc] at hq
  have he := congrArg (fun x ↦ C ((q.coeff 0)⁻¹) * x) hq
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at he
  refine ⟨n, ?_⟩
  rw [he]
  exact (homogeneousComponent_mem n p).C_mul _

theorem exists_generator (I : Ideal (MvPolynomial σ F)) [I.IsPrincipal]
    (hI : I.IsHomogeneous (homogeneousSubmodule σ F)) (hI0 : I ≠ ⊥) :
    ∃ (e : ℕ) (p : MvPolynomial σ F), p ≠ 0 ∧ p.IsHomogeneous e ∧ I = Ideal.span {p} := by
  let p := Submodule.IsPrincipal.generator I
  have hp : Ideal.span {p} = I := Ideal.span_singleton_generator I
  have hp0 : p ≠ 0 := by
    intro h
    apply hI0
    rw [← hp, h, Ideal.span_singleton_zero]
  obtain ⟨e, he⟩ := homogeneous_of_span p hp0 (hp ▸ hI)
  exact ⟨e, p, hp0, he, hp.symm⟩


theorem exists_positive_generator (I : Ideal (MvPolynomial σ F)) [I.IsPrincipal]
    (hI : I.IsHomogeneous (homogeneousSubmodule σ F)) (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    ∃ (e : ℕ) (p : MvPolynomial σ F), 0 < e ∧ p ≠ 0 ∧ p.IsHomogeneous e ∧ I = Ideal.span {p} := by
  obtain ⟨e, p, hp0, hp, hspan⟩ := exists_generator I hI hI0
  have he : 0 < e := by
    by_cases he0 : e = 0
    · have hpz : p.IsHomogeneous 0 := he0 ▸ hp
      have hc := HomogeneousPolynomialEvaluation.homogeneous_zero_eq_C p hpz
      have hc0 : p.coeff 0 ≠ 0 := by
        intro h
        apply hp0
        rw [hc, h, map_zero]
      have hu : IsUnit p := by rw [hc]; exact hc0.isUnit.map C
      exact False.elim (hItop (hspan.trans (Ideal.span_singleton_eq_top.mpr hu)))
    · exact Nat.pos_of_ne_zero he0
  exact ⟨e, p, he, hp0, hp, hspan⟩

end PaperP1.HomogeneousPrincipalIdealGenerator
