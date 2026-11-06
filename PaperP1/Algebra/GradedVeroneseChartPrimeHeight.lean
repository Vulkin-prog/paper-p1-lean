module

public import PaperP1.Algebra.GradedVeroneseDilationChart
public import PaperP1.Algebra.GradedVeroneseQuotient
public import PaperP1.Algebra.LocalizationPrimeHeightEquiv

/-! # Every homogeneous prime avoiding a degree-one coordinate has the same height in every positive Veronese -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseChartPrimeHeight

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)
  {b : A} (hb : b ∈ G 1) (P : Ideal A) (hP : P.IsHomogeneous G) [P.IsPrime] (hbP : b ∉ P)

include hD hb hP hbP in
theorem comap_contracted :
    (GradedVeroneseQuotient.contracted G P D).comap (GradedVeroneseDilation.map G D hD hb).toRingHom = P := by
  let := GradedVeroneseGrading.grading G D hD
  let Q := GradedVeroneseQuotient.contracted G P D
  have hQ : Q.IsHomogeneous (GradedVeroneseGrading.piece G D) :=
    GradedVeroneseQuotient.contracted_homogeneous G P hP D hD
  have hS : (Q.comap (GradedVeroneseDilation.map G D hD hb).toRingHom).IsHomogeneous G :=
    (HomogeneousIdeal.comap (GradedVeroneseDilation.gradedMap G D hD hb)
      (⟨Q, hQ⟩ : HomogeneousIdeal (GradedVeroneseGrading.piece G D))).isHomogeneous
  have he : (⟨Q.comap (GradedVeroneseDilation.map G D hD hb).toRingHom, hS⟩ : HomogeneousIdeal G) = ⟨P, hP⟩ := by
    apply HomogeneousIdeal.ext'
    intro n a ha
    change (GradedVeroneseDilation.map G D hD hb a : A) ∈ P ↔ a ∈ P
    rw [GradedVeroneseDilation.map_homogeneous G D hD hb n a ha]
    exact Ideal.IsPrime.mul_mem_left_iff
      (fun hm ↦ hbP (Ideal.IsPrime.mem_of_pow_mem inferInstance ((D - 1) * n) hm))
  exact congrArg HomogeneousIdeal.toIdeal he

include hD hb hP hbP in
theorem height_eq : P.height = (GradedVeroneseQuotient.contracted G P D).height := by
  let Q := GradedVeroneseQuotient.contracted G P D
  let : Q.IsPrime := Ideal.comap_isPrime (GradedVeroneseAlgebra.veronese G D).val.toRingHom P
  have hn : GradedVeroneseDilation.map G D hD hb b ∉ Q := by
    change (GradedVeroneseDilation.map G D hD hb b : A) ∉ P
    rw [GradedVeroneseDilation.map_coordinate G D hD hb]
    exact fun hm ↦ hbP (Ideal.IsPrime.mem_of_pow_mem inferInstance D hm)
  have hh := LocalizationPrimeHeightEquiv.height_comap (GradedVeroneseDilation.map G D hD hb).toRingHom b
    (GradedVeroneseDilationChart.localization_bijective G D hD hb) Q hn
  rw [comap_contracted G D hD hb P hP hbP] at hh
  exact hh

end PaperP1.GradedVeroneseChartPrimeHeight
