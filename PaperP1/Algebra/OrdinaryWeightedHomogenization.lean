module

public import PaperP1.Algebra.WeightedOrdinarySubstitution

/-! # Explicit inverse homogenization on actual homogeneous ordinary polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryWeightedHomogenization

open Finset MvPolynomial PaperP1.HomogeneousSplitRadicalRelations

variable {F ι : Type*} [Field F]

def generator (D : ℕ) : Fin 3 ⊕ ι → WeightedPolynomial F ι :=
  Sum.elim (fun j ↦ X (Sum.inl (2 : Fin 3)) ^ (D - 1) * X (Sum.inl j)) (fun i ↦ X (Sum.inr i))

def map (D : ℕ) : WeightedPolynomial F ι →ₐ[F] WeightedPolynomial F ι := aeval (generator D)

theorem map_base (D : ℕ) (j : Fin 3) : map (F := F) (ι := ι) D (X (Sum.inl j)) =
    X (Sum.inl (2 : Fin 3)) ^ (D - 1) * X (Sum.inl j) := aeval_X _ _

theorem map_radical (D : ℕ) (i : ι) : map (F := F) D (X (Sum.inr i)) = X (Sum.inr i) := aeval_X _ _

theorem generator_homogeneous (D : ℕ) (hD : 0 < D) (i : Fin 3 ⊕ ι) :
    (generator (F := F) D i).IsWeightedHomogeneous (weight ι D) D := by
  cases i with
  | inl j =>
      have h := ((base_variable_homogeneous F ι D 2).pow (D - 1)).mul
        (base_variable_homogeneous F ι D j)
      simpa only [generator, Sum.elim_inl, smul_eq_mul, mul_one, Nat.sub_add_cancel hD] using h
  | inr i => exact radical_variable_homogeneous F ι D i

theorem map_homogeneous (D : ℕ) (hD : 0 < D) (n : ℕ) (p : WeightedPolynomial F ι)
    (hp : p.IsHomogeneous n) : (map D p).IsWeightedHomogeneous (weight ι D) (D * n) := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (isWeightedHomogeneous_zero F (weight ι D) (D * n))
  | add p q _ _ ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
      rw [map, aeval_monomial]
      have hprod : (d.prod fun i k ↦ generator (F := F) D i ^ k).IsWeightedHomogeneous
          (weight ι D) (D * d.weight 1) := by
        simpa only [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one,
          Finset.mul_sum, Nat.mul_comm] using
          IsWeightedHomogeneous.prod d.support (fun i ↦ generator (F := F) D i ^ d i)
            (fun i ↦ d i * D) (fun i _ ↦ (generator_homogeneous D hD i).pow (d i))
      simpa only [hd, MvPolynomial.algebraMap_eq] using hprod.C_mul c

theorem homogeneous_dilation {σ : Type*} (t : MvPolynomial σ F) (n : ℕ) (p : MvPolynomial σ F)
    (hp : p.IsHomogeneous n) : aeval (fun i ↦ t * X i) p = t ^ n * p := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | add p q _ _ ihp ihq => rw [map_add, ihp, ihq, mul_add]
  | monomial d c hd =>
      have hsum : ∑ i ∈ d.support, d i = n := by
        simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using hd
      rw [aeval_monomial, monomial_eq]
      simp only [MvPolynomial.algebraMap_eq, Finsupp.prod, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
      ring

theorem map_comp_map (D : ℕ) (n : ℕ) (p : WeightedPolynomial F ι) (hp : p.IsHomogeneous n) :
    WeightedOrdinarySubstitution.map D (map D p) = X (Sum.inl (2 : Fin 3)) ^ ((D - 1) * n) * p := by
  have heq : (WeightedOrdinarySubstitution.map (F := F) (ι := ι) D).comp (map D) =
      aeval (fun i ↦ X (Sum.inl (2 : Fin 3)) ^ (D - 1) * X i) := by
    ext i
    cases i with
    | inl j => simp only [AlgHom.comp_apply, map_base, map_mul, map_pow,
        WeightedOrdinarySubstitution.map_base, aeval_X]
    | inr i => simp only [AlgHom.comp_apply, map_radical, WeightedOrdinarySubstitution.map_radical, aeval_X]
  have h := (AlgHom.congr_fun heq p).trans
    (homogeneous_dilation (X (Sum.inl (2 : Fin 3)) ^ (D - 1)) n p hp)
  simpa only [AlgHom.comp_apply, pow_mul] using h

theorem map_eq_at_one {R : Type*} [CommRing R] (φ : WeightedPolynomial F ι →+* R)
    (hZ : φ (X (Sum.inl (2 : Fin 3))) = 1) (D : ℕ) (p : WeightedPolynomial F ι) :
    φ (map D p) = φ p := by
  have heq : φ.comp (map D).toRingHom = φ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change φ (map D (C a)) = φ (C a)
      simp only [map, aeval_C, MvPolynomial.algebraMap_eq]
    · intro i
      cases i with
      | inl j =>
          change φ (map D (X (Sum.inl j))) = φ (X (Sum.inl j))
          rw [map_base, map_mul, map_pow, hZ, one_pow, one_mul]
      | inr i =>
          change φ (map D (X (Sum.inr i))) = φ (X (Sum.inr i))
          rw [map_radical]
  exact RingHom.congr_fun heq p

end PaperP1.OrdinaryWeightedHomogenization
