module

public import PaperP1.Algebra.NilpotentSimpleRoot
public import Mathlib.RingTheory.AdjoinRoot

/-! # A finite polynomial parameter over a nilpotent base ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NilpotentPolynomialParameter

open Polynomial

abbrev Trunc (R : Type*) [CommRing R] (N : ℕ) := AdjoinRoot ((Polynomial.X : R[X]) ^ N)

variable {R : Type*} [CommRing R]

def parameter (R : Type*) [CommRing R] (N : ℕ) : Trunc R N := AdjoinRoot.root _

def liftedIdeal (I : Ideal R) (N : ℕ) : Ideal (Trunc R N) :=
  I.map (algebraMap R (Trunc R N)) ⊔ Ideal.span {parameter R N}

def evaluation (N : ℕ) (t : R) (ht : t ^ N = 0) : Trunc R N →+* R :=
  AdjoinRoot.lift (f := (Polynomial.X : R[X]) ^ N) (RingHom.id R) t
    (by simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using ht)

theorem parameter_pow (N : ℕ) : parameter R N ^ N = 0 := by
  have h := AdjoinRoot.eval₂_root ((Polynomial.X : R[X]) ^ N)
  simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X, parameter] using h

theorem parameter_mem (I : Ideal R) (N : ℕ) : parameter R N ∈ liftedIdeal I N := by
  have hle : Ideal.span {parameter R N} ≤ liftedIdeal I N := le_sup_right
  exact hle (Ideal.subset_span (Set.mem_singleton _))

theorem base_mem (I : Ideal R) (N : ℕ) (r : R) (hr : r ∈ I) :
    algebraMap R (Trunc R N) r ∈ liftedIdeal I N := by
  have hle : I.map (algebraMap R (Trunc R N)) ≤ liftedIdeal I N := le_sup_left
  exact hle (Ideal.mem_map_of_mem _ hr)

theorem liftedIdeal_pow (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥) :
    liftedIdeal I N ^ (N + N) = ⊥ := by
  have hm : (I.map (algebraMap R (Trunc R N))) ^ N = ⊥ := by
    rw [← Ideal.map_pow, hN, Ideal.map_bot]
  have hp : (Ideal.span {parameter R N} : Ideal (Trunc R N)) ^ N = ⊥ := by
    rw [Ideal.span_singleton_pow, parameter_pow, Ideal.span_singleton_zero]
  apply le_antisymm _ bot_le
  calc
    liftedIdeal I N ^ (N + N) ≤
        (I.map (algebraMap R (Trunc R N))) ^ N ⊔
          (Ideal.span {parameter R N} : Ideal (Trunc R N)) ^ N :=
      Ideal.sup_pow_add_le_pow_sup_pow
    _ = ⊥ := by rw [hm, hp, sup_idem]

theorem evaluation_parameter (N : ℕ) (t : R) (ht : t ^ N = 0) :
    evaluation N t ht (parameter R N) = t := by
  exact AdjoinRoot.lift_root _

theorem evaluation_base (N : ℕ) (t : R) (ht : t ^ N = 0) (r : R) :
    evaluation N t ht (algebraMap R (Trunc R N) r) = r := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

theorem evaluation_ideal_le (I : Ideal R) (N : ℕ) (t : R) (ht : t ^ N = 0) (htI : t ∈ I) :
    (liftedIdeal I N).map (evaluation N t ht) ≤ I := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply sup_le
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change evaluation N t ht (algebraMap R (Trunc R N) r) ∈ I
    rw [evaluation_base]
    exact hr
  · apply Ideal.span_le.mpr
    intro r hr
    have he : r = parameter R N := Set.mem_singleton_iff.mp hr
    subst r
    change evaluation N t ht (parameter R N) ∈ I
    rw [evaluation_parameter]
    exact htI

theorem exists_polynomial (N : ℕ) (u : Trunc R N) :
    ∃ q : R[X], Polynomial.aeval (parameter R N) q = u := by
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective u
  refine ⟨q, ?_⟩
  change Polynomial.aeval (AdjoinRoot.root ((Polynomial.X : R[X]) ^ N)) q = u
  rw [AdjoinRoot.aeval_eq]
  exact hq

theorem evaluation_polynomial (N : ℕ) (t : R) (ht : t ^ N = 0) (q : R[X]) :
    evaluation N t ht (Polynomial.aeval (parameter R N) q) = q.eval t := by
  change evaluation N t ht (Polynomial.aeval (AdjoinRoot.root ((Polynomial.X : R[X]) ^ N)) q) = _
  rw [AdjoinRoot.aeval_eq]
  change AdjoinRoot.lift (f := (Polynomial.X : R[X]) ^ N) (RingHom.id R) t _
    (AdjoinRoot.mk _ q) = _
  rw [AdjoinRoot.lift_mk]
  rfl

end PaperP1.NilpotentPolynomialParameter
