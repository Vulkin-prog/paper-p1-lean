module

public import PaperP1.Algebra.GradedVeroneseGrading
public import PaperP1.Algebra.GradedSurjectiveChartMap

/-! # Graded maps on literal Veronese subalgebras and preservation of surjectivity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseMap

open DirectSum

attribute [local instance] GradedVeroneseAlgebra.multipleGradedMonoid

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]
  (G : ℕ → Submodule F A) (H : ℕ → Submodule F B) [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a) (D : ℕ)

include f in
theorem mem_veronese {x : A} (hx : x ∈ GradedVeroneseAlgebra.veronese G D) :
    f x ∈ GradedVeroneseAlgebra.veronese H D := by
  obtain ⟨a, rfl⟩ := hx
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]; exact (GradedVeroneseAlgebra.veronese H D).zero_mem
  | of n x =>
    change f (DirectSum.coeAlgHom (fun n ↦ G (n * D))
      (DirectSum.of (fun n ↦ G (n * D)) n x)) ∈ GradedVeroneseAlgebra.veronese H D
    rw [DirectSum.coeAlgHom_of]
    exact GradedVeroneseAlgebra.piece_mem H D n (f.map_mem x.property)
  | add a b ha hb =>
    rw [map_add, map_add]
    exact (GradedVeroneseAlgebra.veronese H D).add_mem ha hb

def map : GradedVeroneseAlgebra.veronese G D →ₐ[F] GradedVeroneseAlgebra.veronese H D where
  toFun x := ⟨f x, mem_veronese G H f D x.property⟩
  map_zero' := Subtype.ext f.map_zero
  map_one' := Subtype.ext f.map_one
  map_add' x y := Subtype.ext (f.map_add (x : A) (y : A))
  map_mul' x y := Subtype.ext (f.map_mul (x : A) (y : A))
  commutes' a := Subtype.ext (hscalar a)

theorem map_val (x : GradedVeroneseAlgebra.veronese G D) :
    (map G H f hscalar D x : B) = f (x : A) := rfl

def gradedMap : GradedVeroneseGrading.piece G D →+*ᵍ GradedVeroneseGrading.piece H D where
  __ := (map G H f hscalar D).toRingHom
  map_mem hx := f.map_mem hx

include hscalar in
theorem surjective (hD : 0 < D) (hf : Function.Surjective f) :
    Function.Surjective (map G H f hscalar D) := by
  classical
  let := GradedVeroneseGrading.grading H D hD
  apply (AlgHom.range_eq_top (map G H f hscalar D)).mp
  apply top_unique
  intro y _
  rw [← sum_support_decompose (GradedVeroneseGrading.piece H D) y]
  apply (map G H f hscalar D).range.sum_mem
  intro n _
  let z := decompose (GradedVeroneseGrading.piece H D) y n
  obtain ⟨x, hx, hxy⟩ := GradedSurjectiveChartMap.homogeneous_preimage f hf (n * D)
    ((z : GradedVeroneseAlgebra.veronese H D) : B) z.property
  exact ⟨⟨x, GradedVeroneseAlgebra.piece_mem G D n hx⟩, Subtype.ext hxy⟩

end PaperP1.GradedVeroneseMap
