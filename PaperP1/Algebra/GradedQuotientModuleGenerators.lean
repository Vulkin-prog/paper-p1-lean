module

public import PaperP1.Algebra.HomogeneousQuotientGrading
public import PaperP1.Algebra.GradedModulePieceMap

/-! # Actual homogeneous module generators descend to quotient domains -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedQuotientModuleGenerators

open Finset DirectSum

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (J : Ideal B)

def baseIdeal : Ideal A := J.comap f.toRingHom

include f in
theorem baseIdeal_homogeneous (hJ : J.IsHomogeneous H) : (baseIdeal f J).IsHomogeneous G := by
  intro n a ha
  change f (decompose G a n : A) ∈ J
  rw [f.map_directSumDecompose]
  exact (hJ.mem_iff.mp ha) n

def map : HomogeneousQuotientGrading.piece G (baseIdeal f J) →+*ᵍ
    HomogeneousQuotientGrading.piece H J where
  __ := Ideal.quotientMap J f.toRingHom le_rfl
  map_mem hx := by
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨f a, f.map_mem ha, rfl⟩

omit [GradedAlgebra G] [GradedAlgebra H] in
theorem map_mk (a : A) : map f J (Ideal.Quotient.mk (baseIdeal f J) a) = Ideal.Quotient.mk J (f a) := rfl

omit [GradedAlgebra G] [GradedAlgebra H] in
theorem map_injective : Function.Injective (map f J) := Ideal.quotientMap_injective

omit [GradedAlgebra G] [GradedAlgebra H] in
include hscalar in
theorem map_commutes (a : F) :
    map f J (algebraMap F (A ⧸ baseIdeal f J) a) = algebraMap F (B ⧸ J) a := by
  change Ideal.Quotient.mk J (f (algebraMap F A a)) = algebraMap F (B ⧸ J) a
  rw [hscalar]
  rfl

variable (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

omit [GradedAlgebra G] [GradedAlgebra H] in
theorem generators (hgen : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = b) :
    ∀ b : B ⧸ J, ∃ a : ι → (A ⧸ baseIdeal f J),
      ∑ i, map f J (a i) * Ideal.Quotient.mk J (v i) = b := by
  intro b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨a, ha⟩ := hgen b
  refine ⟨fun i ↦ Ideal.Quotient.mk (baseIdeal f J) (a i), ?_⟩
  simp only [map_mk, ← map_mul, ← map_sum, ha]

include hv in
omit [Fintype ι] [GradedAlgebra H] in
theorem generator_mem (i : ι) : Ideal.Quotient.mk J (v i) ∈
    HomogeneousQuotientGrading.piece H J (w i) :=
  Submodule.mem_map.mpr ⟨v i, hv i, rfl⟩

include hscalar hv in
theorem finrank_le (hJ : J.IsHomogeneous H)
    (hgen : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = b)
    (n : ℕ) (hn : ∀ i, w i ≤ n)
    [∀ i, Module.Finite F (HomogeneousQuotientGrading.piece G (baseIdeal f J) (n - w i))] :
    Module.finrank F (HomogeneousQuotientGrading.piece H J n) ≤
      ∑ i, Module.finrank F (HomogeneousQuotientGrading.piece G (baseIdeal f J) (n - w i)) := by
  let := HomogeneousQuotientGrading.grading G (baseIdeal f J) (baseIdeal_homogeneous f J hJ)
  let := HomogeneousQuotientGrading.grading H J hJ
  exact GradedModulePieceMap.finrank_le (map f J) (map_commutes f hscalar J)
    (fun i ↦ Ideal.Quotient.mk J (v i)) w (generator_mem J v w hv)
    (generators f J v hgen) n hn

end PaperP1.GradedQuotientModuleGenerators
