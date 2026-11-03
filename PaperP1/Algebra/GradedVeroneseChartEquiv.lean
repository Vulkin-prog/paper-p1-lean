module

public import PaperP1.Algebra.GradedVeroneseChart

/-! # Bijectivity of the literal Veronese chart map, with no domain hypothesis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseChartEquiv

open HomogeneousLocalization PaperP1.GradedVeroneseChart

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)
  {b : A} (hb : b ∈ G 1)

theorem map_injective :
    letI := GradedVeroneseGrading.grading G D hD
    Function.Injective (map G D hD hb) := by
  let := GradedVeroneseGrading.grading G D hD
  apply (injective_iff_map_eq_zero (map G D hD hb)).mpr
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (GradedVeroneseGrading.piece G D)
    (coordinate_mem G D hb) z
  rw [map_mk G D hD hb] at hz
  have hzv := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk, val_zero, Localization.mk_eq_mk'] at hzv
  obtain ⟨⟨u, t, rfl⟩, ht⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hzv
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk']
  apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
  refine ⟨⟨coordinate G D hb ^ t, t, rfl⟩, ?_⟩
  apply Subtype.ext
  change (b ^ D) ^ t * (a : A) = 0
  rw [← pow_mul]
  have htd : t ≤ D * t := by
    calc
      t = 1 * t := (one_mul t).symm
      _ ≤ D * t := Nat.mul_le_mul_right t hD
  calc
    b ^ (D * t) * (a : A) = b ^ (D * t - t) * (b ^ t * (a : A)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel htd]
    _ = 0 := by rw [ht, mul_zero]

theorem map_surjective :
    letI := GradedVeroneseGrading.grading G D hD
    Function.Surjective (map G D hD hb) := by
  let := GradedVeroneseGrading.grading G D hD
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G hb z
  have hn : n ≤ n * D := by
    calc
      n = n * 1 := (mul_one n).symm
      _ ≤ n * D := Nat.mul_le_mul_left n hD
  have ha' : a * b ^ (n * D - n) ∈ G (n * D) := by
    have hh := SetLike.mul_mem_graded ha (SetLike.pow_mem_graded (n * D - n) hb)
    simpa only [smul_eq_mul, mul_one, Nat.add_sub_of_le hn] using hh
  let a' : GradedVeroneseAlgebra.veronese G D :=
    ⟨a * b ^ (n * D - n), GradedVeroneseAlgebra.piece_mem G D n ha'⟩
  have haV : a' ∈ GradedVeroneseGrading.piece G D (n • (1 : ℕ)) := by
    change a * b ^ (n * D - n) ∈ G ((n • (1 : ℕ)) * D)
    simpa only [smul_eq_mul, mul_one] using ha'
  refine ⟨Away.mk (GradedVeroneseGrading.piece G D) (coordinate_mem G D hb) n a' haV, ?_⟩
  rw [map_mk G D hD hb]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_iff_eq.mpr
  apply congrArg (algebraMap A (Localization.Away b))
  change b ^ n * (a * b ^ (n * D - n)) = b ^ (n * D) * a
  calc
    b ^ n * (a * b ^ (n * D - n)) = (b ^ n * b ^ (n * D - n)) * a := by ring
    _ = b ^ (n * D) * a := by rw [← pow_add, Nat.add_sub_of_le hn]

def equiv :
    letI := GradedVeroneseGrading.grading G D hD
    Away (GradedVeroneseGrading.piece G D) (coordinate G D hb) ≃+* Away G b := by
  let := GradedVeroneseGrading.grading G D hD
  exact RingEquiv.ofBijective (map G D hD hb) ⟨map_injective G D hD hb, map_surjective G D hD hb⟩

theorem equiv_apply :
    letI := GradedVeroneseGrading.grading G D hD
    ∀ z, equiv G D hD hb z = map G D hD hb z := fun _ ↦ rfl

end PaperP1.GradedVeroneseChartEquiv
