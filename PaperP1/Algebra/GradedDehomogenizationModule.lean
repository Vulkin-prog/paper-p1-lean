module

public import PaperP1.Algebra.GradedDehomogenizationPieces
public import PaperP1.Algebra.GradedModulePieceMap

/-! # Actual homogeneous independent families and module denominators descend to degree-one charts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedDehomogenizationModule

open Finset HomogeneousLocalization

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) {b : A} (hb : b ∈ G 1)

theorem natural_apply (a : A) :
    Away.map f b (GradedDehomogenization.map G hb a) =
      GradedDehomogenization.map H (f.map_mem hb) (f a) :=
  DFunLike.congr_fun (GradedDehomogenization.map_natural G hb f) a

theorem sum_product (v : ι → B) (a : ι → A) :
    GradedDehomogenization.map H (f.map_mem hb) (∑ i, f (a i) * v i) =
      ∑ i, Away.map f b (GradedDehomogenization.map G hb (a i)) *
        GradedDehomogenization.map H (f.map_mem hb) (v i) := by
  simp only [map_sum, map_mul, ← natural_apply f hb]

include hb in
theorem chart_map_injective [IsDomain B] (hinj : Function.Injective f) (hfb0 : f b ≠ 0) :
    Function.Injective (Away.map f b) := by
  apply (injective_iff_map_eq_zero (Away.map f b)).mpr
  intro z hz
  obtain ⟨m, hm⟩ := GradedDehomogenizationPieces.lift_large_degree G hb z
  obtain ⟨a, ha, he⟩ := hm m le_rfl
  have hδ : GradedDehomogenization.map H (f.map_mem hb) (f a) = 0 := by
    rw [← natural_apply f hb, he]
    exact hz
  have hfa := GradedDehomogenizationPieces.homogeneous_eq_zero H (f.map_mem hb) hfb0 m (f.map_mem ha) hδ
  have ha0 : a = 0 := hinj (hfa.trans (map_zero f).symm)
  rw [← he, ha0, map_zero]

variable (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

include hv in
theorem linearIndependent [IsDomain B] (hfb0 : f b ≠ 0)
    (hli : letI : Algebra A B := f.toRingHom.toAlgebra
      LinearIndependent A v) :
    letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
    LinearIndependent (Away G b) (fun i ↦ GradedDehomogenization.map H (f.map_mem hb) (v i)) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  change (∑ j, Away.map f b (c j) * GradedDehomogenization.map H (f.map_mem hb) (v j)) = 0 at hc
  obtain ⟨N, hN, hlifts⟩ := GradedDehomogenizationPieces.lift_finite_weighted G hb c w
  choose a ha hea using hlifts
  have hmem : (∑ j, f (a j) * v j) ∈ H N := by
    apply (H N).sum_mem
    intro j _
    have hj : f (a j) * v j ∈ H ((N - w j) + w j) := SetLike.mul_mem_graded (f.map_mem (ha j)) (hv j)
    simpa only [Nat.sub_add_cancel (hN j)] using hj
  have hδ : GradedDehomogenization.map H (f.map_mem hb) (∑ j, f (a j) * v j) = 0 := by
    rw [sum_product f hb v a]
    simpa only [hea] using hc
  have hz := GradedDehomogenizationPieces.homogeneous_eq_zero H (f.map_mem hb) hfb0 N hmem hδ
  have hz' : ∑ j, a j • v j = 0 := hz
  have ha0 := Fintype.linearIndependent_iff.mp hli a hz'
  rw [← hea i, ha0 i, map_zero]

theorem generators
    (hgen : ∀ z : B, ∃ a : ι → A, ∑ i, f (a i) * v i = z) :
    ∀ z : Away H (f b), ∃ a : ι → Away G b,
      ∑ i, Away.map f b (a i) * GradedDehomogenization.map H (f.map_mem hb) (v i) = z := by
  intro z
  obtain ⟨x, rfl⟩ := GradedDehomogenization.map_surjective H (f.map_mem hb) z
  obtain ⟨a, ha⟩ := hgen x
  refine ⟨fun i ↦ GradedDehomogenization.map G hb (a i), ?_⟩
  rw [← sum_product f hb v a, ha]

theorem generators_span
    (hgen : ∀ z : B, ∃ a : ι → A, ∑ i, f (a i) * v i = z) :
    letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
    Submodule.span (Away G b)
      (Set.range fun i ↦ GradedDehomogenization.map H (f.map_mem hb) (v i)) = ⊤ := by
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  apply top_unique
  intro z _
  apply (Submodule.mem_span_range_iff_exists_fun (Away G b)).mpr
  exact generators f hb v hgen z

theorem denominator (q : A)
    (hclear : ∀ z : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f q * z) :
    ∀ z : Away H (f b), ∃ a : ι → Away G b,
      ∑ i, Away.map f b (a i) * GradedDehomogenization.map H (f.map_mem hb) (v i) =
        Away.map f b (GradedDehomogenization.map G hb q) * z := by
  intro z
  obtain ⟨x, rfl⟩ := GradedDehomogenization.map_surjective H (f.map_mem hb) z
  obtain ⟨a, ha⟩ := hclear x
  refine ⟨fun i ↦ GradedDehomogenization.map G hb (a i), ?_⟩
  rw [← sum_product f hb v a, ha, map_mul, natural_apply]

end PaperP1.GradedDehomogenizationModule
