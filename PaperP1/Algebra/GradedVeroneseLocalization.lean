module

public import PaperP1.Algebra.GradedChartLocalization
public import PaperP1.Algebra.GradedVeroneseMap
public import PaperP1.Algebra.GradedVeroneseChart
public import PaperP1.Algebra.LocalizationPrimeHeightEquiv

/-! # A bijective actual homogeneous chart preserves prime heights in all positive Veronese rings -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseLocalization

open HomogeneousLocalization DirectSum

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  (G : ℕ → Submodule F A) (H : ℕ → Submodule F B) [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (D : ℕ) (hD : 0 < D) {b : A} (hb : b ∈ G 1)

local notation "fV" => GradedVeroneseMap.map G H f hscalar D
local notation "bV" => GradedVeroneseChart.coordinate G D hb

include hD hb in
theorem map_injective (hf : Function.Injective (Away.map f b)) :
    Function.Injective (Localization.awayMap (fV).toRingHom bV) := by
  apply Localization.awayMap_injective_iff.mpr
  intro x hx
  have hraw : f (x : A) = 0 := by
    change fV x = 0 at hx
    exact congrArg (fun z : GradedVeroneseAlgebra.veronese H D ↦ (z : B)) hx
  obtain ⟨t, ht⟩ := (Localization.awayMap_injective_iff.mp (GradedChartLocalization.map_injective f hb hf))
    (x : A) hraw
  have htd : t ≤ D * t := by
    calc
      t = 1 * t := (one_mul t).symm
      _ ≤ D * t := Nat.mul_le_mul_right t hD
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change (b ^ D) ^ t * (x : A) = 0
  rw [← pow_mul]
  calc
    b ^ (D * t) * (x : A) = b ^ (D * t - t) * (b ^ t * (x : A)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel htd]
    _ = 0 := by rw [ht, mul_zero]

include hD hb in
theorem homogeneous_clear (hf : Function.Surjective (Away.map f b)) (n : ℕ)
    (y : GradedVeroneseAlgebra.veronese H D) (hy : (y : B) ∈ H (n * D)) :
    ∃ x m, fV x = fV bV ^ m * y := by
  obtain ⟨a, m, ha, hfa⟩ := GradedChartLocalization.homogeneous_clear_degree f hb hf (n * D) (y : B) hy
  have hm : (D - 1) * m + m = D * m := by
    calc
      (D - 1) * m + m = (D - 1 + 1) * m := by ring
      _ = D * m := by rw [Nat.sub_add_cancel hD]
  have hdegree : (D - 1) * m + (m + n * D) = (m + n) * D := by
    rw [← Nat.add_assoc, hm]
    ring
  have ha' : b ^ ((D - 1) * m) * a ∈ G ((m + n) * D) := by
    have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded ((D - 1) * m) hb) ha
    simpa only [smul_eq_mul, mul_one, hdegree] using h
  refine ⟨⟨_, GradedVeroneseAlgebra.piece_mem G D (m + n) ha'⟩, m, ?_⟩
  apply Subtype.ext
  change f (b ^ ((D - 1) * m) * a) = f (b ^ D) ^ m * (y : B)
  rw [map_mul, map_pow, map_pow, hfa, ← pow_mul, ← mul_assoc, ← pow_add, hm]

include hD hb in
theorem map_surjective (hf : Function.Surjective (Away.map f b)) :
    Function.Surjective (Localization.awayMap (fV).toRingHom bV) := by
  classical
  let := GradedVeroneseGrading.grading H D hD
  apply Localization.awayMap_surjective_iff.mpr
  intro y
  rw [← sum_support_decompose (GradedVeroneseGrading.piece H D) y]
  apply GradedChartLocalization.clear_sum (fV).toRingHom bV
  intro n _hn
  exact homogeneous_clear G H f hscalar D hD hb hf n _
    (decompose (GradedVeroneseGrading.piece H D) y n).property

include hD hb in
theorem map_bijective (hf : Function.Bijective (Away.map f b)) :
    Function.Bijective (Localization.awayMap (fV).toRingHom bV) :=
  ⟨map_injective G H f hscalar D hD hb hf.1, map_surjective G H f hscalar D hD hb hf.2⟩

include hD hb in
theorem height_comap (hf : Function.Bijective (Away.map f b))
    (Q : Ideal (GradedVeroneseAlgebra.veronese H D)) [Q.IsPrime] (hQ : fV bV ∉ Q) :
    (Q.comap (fV).toRingHom).height = Q.height :=
  LocalizationPrimeHeightEquiv.height_comap (fV).toRingHom bV
    (map_bijective G H f hscalar D hD hb hf) Q hQ

end PaperP1.GradedVeroneseLocalization
