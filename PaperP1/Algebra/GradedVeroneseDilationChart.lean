module

public import PaperP1.Algebra.GradedVeroneseDilation
public import PaperP1.Algebra.GradedChartLocalization

/-! # The actual homogeneous dilation induces a bijection on the normalized chart, including zero divisors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseDilationChart

open HomogeneousLocalization GradedVeroneseDilation

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)
  {b : A} (hb : b ∈ G 1)

theorem map_injective :
    letI := GradedVeroneseGrading.grading G D hD
    Function.Injective (Away.map (gradedMap G D hD hb) b) := by
  let := GradedVeroneseGrading.grading G D hD
  let f := gradedMap G D hD hb
  have hfb : (f b : A) = b ^ D := congrArg Subtype.val (map_coordinate G D hD hb)
  apply (injective_iff_map_eq_zero (Away.map f b)).mpr
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G hb z
  have ha' : a ∈ G n := by simpa only [smul_eq_mul, mul_one] using ha
  rw [Away.map_mk] at hz
  have hzv := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk, val_zero, Localization.mk_eq_mk'] at hzv
  obtain ⟨⟨u, t, rfl⟩, ht⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hzv
  have ht' := congrArg (fun x : GradedVeroneseAlgebra.veronese G D ↦ (x : A)) ht
  change (f b : A) ^ t * (f a : A) = 0 at ht'
  have hfa : (f a : A) = b ^ ((D - 1) * n) * a := map_homogeneous G D hD hb n a ha'
  rw [hfb, hfa, ← pow_mul, ← mul_assoc, ← pow_add] at ht'
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk']
  apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
  exact ⟨⟨b ^ (D * t + (D - 1) * n), D * t + (D - 1) * n, rfl⟩, ht'⟩

theorem map_surjective :
    letI := GradedVeroneseGrading.grading G D hD
    Function.Surjective (Away.map (gradedMap G D hD hb) b) := by
  let := GradedVeroneseGrading.grading G D hD
  let f := gradedMap G D hD hb
  have hfb : (f b : A) = b ^ D := congrArg Subtype.val (map_coordinate G D hD hb)
  intro z
  obtain ⟨n, v, hv, rfl⟩ := Away.mk_surjective (GradedVeroneseGrading.piece G D) (f.map_mem hb) z
  have hv' : (v : A) ∈ G (n * D) := by
    change (v : A) ∈ G ((n • (1 : ℕ)) * D) at hv
    simpa only [smul_eq_mul, mul_one] using hv
  refine ⟨Away.mk G hb (n * D) (v : A) (by simpa only [smul_eq_mul, mul_one] using hv'), ?_⟩
  rw [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_iff_eq.mpr
  apply congrArg (algebraMap (GradedVeroneseAlgebra.veronese G D) (Localization.Away (f b)))
  apply Subtype.ext
  change (f b : A) ^ n * (f (v : A) : A) = (f b : A) ^ (n * D) * (v : A)
  have hfv : (f (v : A) : A) = b ^ ((D - 1) * (n * D)) * (v : A) :=
    map_homogeneous G D hD hb (n * D) (v : A) hv'
  rw [hfb, hfv, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
  have he : D * n + (D - 1) * (n * D) = D * (n * D) := by
    calc
      D * n + (D - 1) * (n * D) = (D - 1 + 1) * (n * D) := by ring
      _ = D * (n * D) := by rw [Nat.sub_add_cancel hD]
  rw [he]

theorem map_bijective :
    letI := GradedVeroneseGrading.grading G D hD
    Function.Bijective (Away.map (gradedMap G D hD hb) b) :=
  ⟨map_injective G D hD hb, map_surjective G D hD hb⟩

theorem localization_bijective : Function.Bijective (Localization.awayMap (map G D hD hb).toRingHom b) := by
  let := GradedVeroneseGrading.grading G D hD
  exact ⟨GradedChartLocalization.map_injective (gradedMap G D hD hb) hb (map_bijective G D hD hb).1,
    GradedChartLocalization.map_surjective (gradedMap G D hD hb) hb (map_bijective G D hD hb).2⟩

end PaperP1.GradedVeroneseDilationChart
