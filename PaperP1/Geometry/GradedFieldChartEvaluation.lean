module

public import PaperP1.Algebra.GradedDehomogenization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Actual evaluation on a degree-one projective affine chart over a field -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.GradedFieldChartEvaluation

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {A σ K : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [Field K] (G : ℕ → σ) [GradedRing G]

def evaluation (ε : A →+* K) (b : A) (hb : ε b ≠ 0) : Away G b →+* K :=
  (Localization.awayLift ε b (isUnit_iff_ne_zero.mpr hb)).comp
    (algebraMap (Away G b) (Localization.Away b))

theorem evaluation_mk (ε : A →+* K) {b : A} (hb : ε b ≠ 0) (hbg : b ∈ G 1)
    (n : ℕ) (P : A) (hP : P ∈ G (n • (1 : ℕ))) :
    evaluation G ε b hb (Away.mk G hbg n P hP) = ε P / ε b ^ n := by
  change Localization.awayLift ε b (isUnit_iff_ne_zero.mpr hb)
    (Localization.mk P ⟨b ^ n, n, rfl⟩) = _
  rw [Localization.awayLift_mk ε b P (ε b)⁻¹ (mul_inv_cancel₀ hb) n]
  rw [div_eq_mul_inv, inv_pow]

theorem evaluation_dehomogenization (ε : A →+* K) {b : A} (hb : ε b ≠ 0)
    (hbg : b ∈ G 1) (n : ℕ) (P : A) (hP : P ∈ G n) :
    evaluation G ε b hb (GradedDehomogenization.map G hbg P) = ε P / ε b ^ n := by
  rw [GradedDehomogenization.map_homogeneous G hbg n P hP, evaluation_mk]

def pointMap (ε : A →+* K) {b : A} (hb : ε b ≠ 0) (hbg : b ∈ G 1) :
    Spec (CommRingCat.of K) ⟶ Proj G :=
  Spec.map (CommRingCat.ofHom (evaluation G ε b hb)) ≫ Proj.awayι G b hbg (by decide)

theorem chart_hom_apply {b : A} (hbg : b ∈ G 1)
    (x : (Proj.basicOpen G b).toScheme) :
    (Proj.basicOpenIsoSpec G b hbg (by decide)).hom x =
      ProjIsoSpecTopComponent.toSpec G b x := by
  exact ProjectiveSpectrum.Proj.toSpec_base_apply_eq G x

theorem chart_inv_apply {b : A} (hbg : b ∈ G 1) (q : PrimeSpectrum (Away G b)) :
    (Proj.basicOpenIsoSpec G b hbg (by decide)).inv q =
      ProjIsoSpecTopComponent.FromSpec.toFun hbg (by decide) q := by
  apply ProjIsoSpecTopComponent.toSpec_injective G hbg (by decide)
  rw [← chart_hom_apply G hbg]
  have he : (Proj.basicOpenIsoSpec G b hbg (by decide)).hom
      ((Proj.basicOpenIsoSpec G b hbg (by decide)).inv q) = q := by
    change ((Proj.basicOpenIsoSpec G b hbg (by decide)).inv ≫
      (Proj.basicOpenIsoSpec G b hbg (by decide)).hom) q = q
    rw [Iso.inv_hom_id]
    rfl
  rw [he]
  exact (ProjIsoSpecTopComponent.toSpec_fromSpec G hbg (by decide) q).symm

theorem chart_inv_homogeneous_mem {b : A} (hbg : b ∈ G 1)
    (q : PrimeSpectrum (Away G b)) {n : ℕ} (P : A) (hP : P ∈ G n) :
    P ∈ ((Proj.basicOpenIsoSpec G b hbg (by decide)).inv q).val.asHomogeneousIdeal ↔
      Away.mk G hbg n P (by simpa only [smul_eq_mul, mul_one] using hP) ∈ q.asIdeal := by
  rw [chart_inv_apply]
  change P ∈ ProjIsoSpecTopComponent.FromSpec.carrier hbg q ↔ _
  rw [ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff_of_mem_mul hbg (by decide) q P
    (n := n) (by simpa only [mul_one] using hP)]
  apply Eq.to_iff
  congr 1
  apply HomogeneousLocalization.val_injective
  rfl

theorem pointMap_homogeneous_mem (ε : A →+* K) {b : A} (hb : ε b ≠ 0)
    (hbg : b ∈ G 1) {n : ℕ} (P : A) (hP : P ∈ G n) :
    P ∈ (pointMap G ε hb hbg (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔ ε P = 0 := by
  change P ∈ ((Proj.basicOpenIsoSpec G b hbg (by decide)).inv
    (PrimeSpectrum.comap (evaluation G ε b hb) (IsLocalRing.closedPoint K))).val.asHomogeneousIdeal ↔ _
  rw [chart_inv_homogeneous_mem G hbg _ P hP]
  change evaluation G ε b hb (Away.mk G hbg n P _) ∈ IsLocalRing.maximalIdeal K ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot, evaluation_mk, div_eq_zero_iff]
  exact or_iff_left (pow_ne_zero n hb)

end PaperP1.GradedFieldChartEvaluation
