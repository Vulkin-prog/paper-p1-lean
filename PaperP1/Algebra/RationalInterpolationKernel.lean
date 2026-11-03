module

public import PaperP1.Algebra.RationalInterpolationUniqueness
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # The actual bounded-polynomial interpolation kernel is a line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalInterpolationKernel

open Polynomial PaperP1.RationalInterpolationUniqueness

variable {F : Type*} [Field F]

abbrev PairSpace (F : Type*) [Field F] (a : ℕ) := degreeLT F (a + 1) × degreeLT F (a + 1)

theorem bounded_natDegree (a : ℕ) (P : degreeLT F (a + 1)) : (P : F[X]).natDegree ≤ a :=
  natDegree_le_of_degree_le (mem_degreeLE.mp (by
    simpa only [degreeLT_succ_eq_degreeLE] using P.property))

def constraints (a : ℕ) (S : Finset F) (y : F → F) : PairSpace F a →ₗ[F] (S → F) where
  toFun u t := (u.1 : F[X]).eval (t : F) - y t * (u.2 : F[X]).eval (t : F)
  map_add' u v := by
    funext t
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, eval_add, Pi.add_apply]
    ring
  map_smul' δ u := by
    funext t
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Polynomial.smul_eq_C_mul, eval_mul, eval_C, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem mem_kernel_iff (a : ℕ) (S : Finset F) (y : F → F) (u : PairSpace F a) :
    u ∈ LinearMap.ker (constraints a S y) ↔ Interpolates S y (u.1 : F[X]) (u.2 : F[X]) := by
  constructor
  · intro h t ht
    exact sub_eq_zero.mp (congrFun (LinearMap.mem_ker.mp h) ⟨t, ht⟩)
  · intro h
    apply LinearMap.mem_ker.mpr
    funext t
    exact sub_eq_zero.mpr (h t t.property)

theorem kernel_eq_span (a : ℕ) (S : Finset F) (y : F → F) (u : PairSpace F a)
    (hQ0 : (u.2 : F[X]) ≠ 0) (hcop : IsCoprime (u.1 : F[X]) (u.2 : F[X]))
    (hdegree : max (u.1 : F[X]).natDegree (u.2 : F[X]).natDegree = a) (hcard : 2 * a < S.card)
    (hu : Interpolates S y (u.1 : F[X]) (u.2 : F[X])) :
    LinearMap.ker (constraints a S y) = Submodule.span F {u} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨δ, hP, hQ⟩ := unique_up_to_scalar a S y (u.1 : F[X]) (u.2 : F[X])
      (v.1 : F[X]) (v.2 : F[X]) hQ0 hcop hdegree (bounded_natDegree a v.1)
      (bounded_natDegree a v.2) hcard hu ((mem_kernel_iff a S y v).mp hv)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨δ, ?_⟩
    apply Prod.ext <;> apply Subtype.ext
    · simpa only [Prod.smul_fst, Submodule.coe_smul, smul_eq_C_mul] using hP.symm
    · simpa only [Prod.smul_snd, Submodule.coe_smul, smul_eq_C_mul] using hQ.symm
  · apply Submodule.span_le.mpr
    intro v hv
    have hvu : v = u := Set.mem_singleton_iff.mp hv
    exact hvu ▸ (mem_kernel_iff a S y u).mpr hu

theorem kernel_finrank (a : ℕ) (S : Finset F) (y : F → F) (u : PairSpace F a)
    (hQ0 : (u.2 : F[X]) ≠ 0) (hcop : IsCoprime (u.1 : F[X]) (u.2 : F[X]))
    (hdegree : max (u.1 : F[X]).natDegree (u.2 : F[X]).natDegree = a) (hcard : 2 * a < S.card)
    (hu : Interpolates S y (u.1 : F[X]) (u.2 : F[X])) :
    Module.finrank F (LinearMap.ker (constraints a S y)) = 1 := by
  rw [kernel_eq_span a S y u hQ0 hcop hdegree hcard hu]
  apply finrank_span_singleton
  intro hz
  exact hQ0 (congrArg (fun v : PairSpace F a ↦ (v.2 : F[X])) hz)

end PaperP1.RationalInterpolationKernel
