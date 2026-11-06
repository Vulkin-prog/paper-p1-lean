module

public import PaperP1.Algebra.WeightedOrdinarySubstitution
public import PaperP1.Algebra.WeightedHomogeneousEvaluation

/-! # The actual ordinary coordinates XZ^(D-1), YZ^(D-1), Z^D and the original radical coordinates in the weighted source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryWeightedProjection

open MvPolynomial HomogeneousSplitRadicalRelations

variable {F ι : Type*} [Field F]

def generator (D : ℕ) : Fin 3 ⊕ ι → WeightedPolynomial F ι :=
  Sum.elim (fun j ↦ X (Sum.inl j) * X (Sum.inl (2 : Fin 3)) ^ (D - 1)) (fun i ↦ X (Sum.inr i))

def map (D : ℕ) : WeightedPolynomial F ι →ₐ[F] WeightedPolynomial F ι := aeval (generator D)

theorem map_base (D : ℕ) (j : Fin 3) : map (F := F) (ι := ι) D (X (Sum.inl j)) =
    X (Sum.inl j) * X (Sum.inl (2 : Fin 3)) ^ (D - 1) := aeval_X _ _

theorem map_radical (D : ℕ) (i : ι) : map (F := F) D (X (Sum.inr i)) = X (Sum.inr i) := aeval_X _ _

theorem map_Z (D : ℕ) (hD : 0 < D) : map (F := F) (ι := ι) D (X (Sum.inl (2 : Fin 3))) =
    X (Sum.inl (2 : Fin 3)) ^ D := by
  rw [map_base, ← pow_succ', Nat.sub_add_cancel hD]

theorem generator_homogeneous (D : ℕ) (hD : 0 < D) (i : Fin 3 ⊕ ι) :
    (generator (F := F) D i).IsWeightedHomogeneous (weight ι D) D := by
  cases i with
  | inl j =>
    have hh := (base_variable_homogeneous F ι D j).mul
      ((base_variable_homogeneous F ι D 2).pow (D - 1))
    have he : 1 + (D - 1) = D := by omega
    simpa only [generator, Sum.elim_inl, smul_eq_mul, mul_one, he] using hh
  | inr i => exact radical_variable_homogeneous F ι D i

theorem map_homogeneous (D : ℕ) (hD : 0 < D) {n : ℕ} (p : WeightedPolynomial F ι)
    (hp : p.IsHomogeneous n) : (map D p).IsWeightedHomogeneous (weight ι D) (n * D) := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using isWeightedHomogeneous_zero F (weight ι D) (n * D)
  | add p q _hp _hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
    have hd' : d.degree = n := by rw [Finsupp.degree_eq_weight_one]; exact hd
    have hprod := IsWeightedHomogeneous.prod d.support
      (fun i ↦ generator (F := F) D i ^ d i) (fun i ↦ d i * D)
      (fun i _hi ↦ by simpa only [smul_eq_mul] using (generator_homogeneous D hD i).pow (d i))
    have he : (∑ i ∈ d.support, d i * D) = n * D := by
      rw [← Finset.sum_mul, ← Finsupp.degree_apply, hd']
    rw [he] at hprod
    rw [map, aeval_monomial]
    simpa only [Finsupp.prod, MvPolynomial.algebraMap_eq] using hprod.C_mul c

end PaperP1.OrdinaryWeightedProjection
