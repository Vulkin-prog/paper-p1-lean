module

public import PaperP1.Algebra.GradedQuotientPieceLifts
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Homogeneous separating elements inject the product of actual shifted component pieces into the whole quotient piece -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedSeparatedComponentPieces

open Finset

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
  (H : ℕ → Submodule F A) [GradedAlgebra H] (I Q : Ideal A)
  (w : ℕ) (f : A) (hf : f ∈ H w) (n : ℕ) (hn : w ≤ n)

def componentMap : HomogeneousQuotientGrading.piece H Q (n - w) →ₗ[F]
    HomogeneousQuotientGrading.piece H I n := by
  let L := (H (n - w)).subtype.comp (GradedQuotientPieceLifts.lift H Q (n - w))
  let M := (LinearMap.mulLeft F f).comp L
  let p := (Ideal.Quotient.mkₐ F I).toLinearMap.comp M
  exact p.codRestrict (HomogeneousQuotientGrading.piece H I n) (fun x ↦ by
    refine Submodule.mem_map.mpr ⟨f * (GradedQuotientPieceLifts.lift H Q (n - w) x : A), ?_, rfl⟩
    have hm := SetLike.mul_mem_graded hf (GradedQuotientPieceLifts.lift H Q (n - w) x).property
    simpa only [Nat.add_sub_of_le hn] using hm)

theorem componentMap_value (x : HomogeneousQuotientGrading.piece H Q (n - w)) :
    (componentMap H I Q w f hf n hn x : A ⧸ I) =
      Ideal.Quotient.mk I (f * (GradedQuotientPieceLifts.lift H Q (n - w) x : A)) := rfl

theorem componentMap_own (hIQ : I ≤ Q) (x : HomogeneousQuotientGrading.piece H Q (n - w)) :
    Ideal.Quotient.factorₐ F hIQ (componentMap H I Q w f hf n hn x : A ⧸ I) =
      Ideal.Quotient.mk Q f * (x : A ⧸ Q) := by
  change Ideal.Quotient.mk Q (f * (GradedQuotientPieceLifts.lift H Q (n - w) x : A)) = _
  rw [map_mul, GradedQuotientPieceLifts.lift_quotient_value]

theorem componentMap_other (P : Ideal A) (hIP : I ≤ P) (hfP : f ∈ P)
    (x : HomogeneousQuotientGrading.piece H Q (n - w)) :
    Ideal.Quotient.factorₐ F hIP (componentMap H I Q w f hf n hn x : A ⧸ I) = 0 := by
  change Ideal.Quotient.mk P (f * (GradedQuotientPieceLifts.lift H Q (n - w) x : A)) = 0
  rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hfP, zero_mul]

variable {ι : Type*} [Fintype ι]

def sumMap (Q : ι → Ideal A) (w : ι → ℕ) (f : ι → A) (hf : ∀ i, f i ∈ H (w i))
    (n : ℕ) (hn : ∀ i, w i ≤ n) :
    (∀ i, HomogeneousQuotientGrading.piece H (Q i) (n - w i)) →ₗ[F]
      HomogeneousQuotientGrading.piece H I n :=
  ∑ i, (componentMap H I (Q i) (w i) (f i) (hf i) n (hn i)).comp (LinearMap.proj i)

theorem sumMap_projection (Q : ι → Ideal A) (hIQ : ∀ i, I ≤ Q i)
    (w : ι → ℕ) (f : ι → A) (hf : ∀ i, f i ∈ H (w i))
    (hsep : ∀ i j, j ≠ i → f i ∈ Q j) (n : ℕ) (hn : ∀ i, w i ≤ n)
    (v : ∀ i, HomogeneousQuotientGrading.piece H (Q i) (n - w i)) (i : ι) :
    Ideal.Quotient.factorₐ F (hIQ i) (sumMap H I Q w f hf n hn v : A ⧸ I) =
      Ideal.Quotient.mk (Q i) (f i) * (v i : A ⧸ Q i) := by
  classical
  simp only [sumMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum]
  rw [map_sum, Finset.sum_eq_single i]
  · exact componentMap_own H I (Q i) (w i) (f i) (hf i) n (hn i) (hIQ i) (v i)
  · intro j _hj hji
    exact componentMap_other H I (Q j) (w j) (f j) (hf j) n (hn j) (Q i) (hIQ i)
      (hsep j i hji.symm) (v j)
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem sumMap_injective (Q : ι → Ideal A) (hprime : ∀ i, (Q i).IsPrime) (hIQ : ∀ i, I ≤ Q i)
    (w : ι → ℕ) (f : ι → A) (hf : ∀ i, f i ∈ H (w i))
    (hnot : ∀ i, f i ∉ Q i) (hsep : ∀ i j, j ≠ i → f i ∈ Q j)
    (n : ℕ) (hn : ∀ i, w i ≤ n) : Function.Injective (sumMap H I Q w f hf n hn) := by
  have hzero : ∀ v, sumMap H I Q w f hf n hn v = 0 → v = 0 := by
    intro v hv
    funext i
    let : (Q i).IsPrime := hprime i
    apply Subtype.ext
    have hh := congrArg (fun a : HomogeneousQuotientGrading.piece H I n ↦
      Ideal.Quotient.factorₐ F (hIQ i) (a : A ⧸ I)) hv
    rw [sumMap_projection H I Q hIQ w f hf hsep n hn v i, Submodule.coe_zero, map_zero] at hh
    have hnonzero : Ideal.Quotient.mk (Q i) (f i) ≠ 0 :=
      fun he ↦ hnot i (Ideal.Quotient.eq_zero_iff_mem.mp he)
    exact (mul_eq_zero.mp hh).resolve_left hnonzero
  intro x y hxy
  have hh := hzero (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp hh

theorem dimension_le [∀ n, Module.Finite F (H n)]
    (Q : ι → Ideal A) (hprime : ∀ i, (Q i).IsPrime) (hIQ : ∀ i, I ≤ Q i)
    (w : ι → ℕ) (f : ι → A) (hf : ∀ i, f i ∈ H (w i))
    (hnot : ∀ i, f i ∉ Q i) (hsep : ∀ i j, j ≠ i → f i ∈ Q j)
    (n : ℕ) (hn : ∀ i, w i ≤ n) :
    (∑ i, Module.finrank F (HomogeneousQuotientGrading.piece H (Q i) (n - w i))) ≤
      Module.finrank F (HomogeneousQuotientGrading.piece H I n) := by
  let (i : ι) : Module.Finite F (HomogeneousQuotientGrading.piece H (Q i) (n - w i)) :=
    Module.Finite.of_surjective (GradedQuotientHilbertMonotonicity.quotientMap H (Q i) (n - w i))
      (GradedQuotientHilbertMonotonicity.quotientMap_surjective H (Q i) (n - w i))
  let : Module.Finite F (HomogeneousQuotientGrading.piece H I n) :=
    Module.Finite.of_surjective (GradedQuotientHilbertMonotonicity.quotientMap H I n)
      (GradedQuotientHilbertMonotonicity.quotientMap_surjective H I n)
  have hh := LinearMap.finrank_le_finrank_of_injective
    (f := sumMap H I Q w f hf n hn) (sumMap_injective H I Q hprime hIQ w f hf hnot hsep n hn)
  simpa only [Module.finrank_pi_fintype] using hh

end PaperP1.GradedSeparatedComponentPieces
