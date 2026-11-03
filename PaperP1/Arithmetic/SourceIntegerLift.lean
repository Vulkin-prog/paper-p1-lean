module

public import PaperP1.Arithmetic.WeightedRootEvaluation
public import PaperP1.Geometry.SourceProjectiveEmbedding
public import PaperP1.Algebra.SplitWeightedGeneratorIndex
public import Mathlib.Algebra.BigOperators.Fin

/-! # Literal integer coordinates in the actual chosen projective source embedding -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceIntegerLift

open MvPolynomial PaperP1.HomogeneousSplitRadicalRelations PaperP1.SourceProjectiveEmbedding

variable {ι : Type}

def point (D : ℕ) (x y : ℤ) (w : ι → ℤ) : GeneratorIndex ℚ ι D → ℤ :=
  fun g ↦ Sum.elim (fun e : {d : Fin 3 →₀ ℕ // d.degree = D} ↦ x ^ (e.val 1) * y ^ (e.val 0)) w
    ((SplitWeightedGeneratorIndex.indexEquiv ℚ ι D).symm g)

theorem point_base (D : ℕ) (x y : ℤ) (w : ι → ℤ) (e : {d : Fin 3 →₀ ℕ // d.degree = D}) :
    point D x y w (SplitWeightedGeneratorIndex.indexEquiv ℚ ι D (Sum.inl e)) = x ^ (e.val 1) * y ^ (e.val 0) := by
  rw [point, Equiv.symm_apply_apply]
  rfl

theorem point_radical (D : ℕ) (x y : ℤ) (w : ι → ℤ) (i : ι) :
    point D x y w (SplitWeightedGeneratorIndex.indexEquiv ℚ ι D (Sum.inr i)) = w i := by
  rw [point, Equiv.symm_apply_apply]
  rfl

theorem base_evaluation (x y : ℤ) (w : ι → ℤ) (e : Fin 3 →₀ ℕ) :
    OrdinaryIntegerPoints.evaluation (OrdinaryIntegerPoints.lift x y w)
      (rename Sum.inl (monomial e (1 : ℚ))) = (x : ℚ) ^ (e 1) * (y : ℚ) ^ (e 0) := by
  change aeval (fun i ↦ (OrdinaryIntegerPoints.lift x y w i : ℚ)) (rename Sum.inl (monomial e (1 : ℚ))) = _
  rw [aeval_rename, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [map_one, one_mul, Fin.prod_univ_three]
  change (y : ℚ) ^ e 0 * (x : ℚ) ^ e 1 * (1 : ℚ) ^ e 2 = _
  rw [one_pow, mul_one, mul_comm]

theorem evaluation_coordinate (D : ℕ) (x y : ℤ) (w : ι → ℤ) (g : GeneratorIndex ℚ ι D) :
    OrdinaryIntegerPoints.evaluation (OrdinaryIntegerPoints.lift x y w) (g : WeightedPolynomial ℚ ι) =
      (point D x y w g : ℚ) := by
  obtain ⟨t, rfl⟩ := (SplitWeightedGeneratorIndex.indexEquiv ℚ ι D).surjective g
  cases t with
  | inl e =>
    rw [point_base]
    change OrdinaryIntegerPoints.evaluation (OrdinaryIntegerPoints.lift x y w)
      (rename Sum.inl (monomial e.val (1 : ℚ))) = ((x ^ e.val 1 * y ^ e.val 0 : ℤ) : ℚ)
    rw [base_evaluation, Int.cast_mul, Int.cast_pow, Int.cast_pow]
  | inr i =>
    rw [point_radical]
    exact OrdinaryIntegerPoints.evaluation_X _ (Sum.inr i)

def evaluation (D : ℕ) (v : GeneratorIndex ℚ ι D → ℤ) :
    MvPolynomial (GeneratorIndex ℚ ι D) ℚ →ₐ[ℚ] ℚ := aeval fun g ↦ (v g : ℚ)

theorem evaluation_comp (d : ι → ℤ) (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
    (x y : ℤ) (w : ι → ℤ)
    (hroot : ∀ i, w i ^ 2 = d i * SplitRadicalPointHeight.integerProduct (I i) x *
      SplitRadicalPointHeight.integerProduct (J i) y) :
    (evaluation D (point D x y w)).toRingHom =
      (WeightedRootEvaluation.sourceEvaluation d D I J x y w hroot).comp
        (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have hC : (evaluation D (point D x y w)).toRingHom.comp C =
        ((WeightedRootEvaluation.sourceEvaluation d D I J x y w hroot).comp
          (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD).toRingHom).comp C :=
      Subsingleton.elim _ _
    exact RingHom.congr_fun hC a
  · intro g
    change evaluation D (point D x y w) (X g) =
      WeightedRootEvaluation.sourceEvaluation d D I J x y w hroot
        (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD (X g))
    rw [evaluation, aeval_X, SourceProjectiveEmbedding.evaluation_X,
      WeightedRootEvaluation.sourceGenerator_value, evaluation_coordinate]

theorem global_relations_le_kernel (d : ι → ℤ) (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
    (x y : ℤ) (w : ι → ℤ)
    (hroot : ∀ i, w i ^ 2 = d i * SplitRadicalPointHeight.integerProduct (I i) x *
      SplitRadicalPointHeight.integerProduct (J i) y) :
    RingHom.ker (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD).toRingHom ≤
      RingHom.ker (evaluation D (point D x y w)).toRingHom := by
  intro f hf
  have heq := RingHom.congr_fun (evaluation_comp d D I J hdeg hD x y w hroot) f
  have hz := RingHom.mem_ker.mp hf
  change SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD f = 0 at hz
  change evaluation D (point D x y w) f = 0
  change evaluation D (point D x y w) f = WeightedRootEvaluation.sourceEvaluation d D I J x y w hroot
    (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD f) at heq
  rw [hz, map_zero] at heq
  exact heq

end PaperP1.SourceIntegerLift
