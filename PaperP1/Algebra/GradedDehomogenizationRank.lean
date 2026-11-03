module

public import PaperP1.Algebra.GradedDehomogenizationModule
public import PaperP1.Algebra.HomogeneousFreeApproximation
public import PaperP1.Algebra.GradedChartBasis

/-! # The actual finite graded module and any nonzero degree-one chart have the same rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedDehomogenizationRank

open Finset HomogeneousLocalization

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H] [IsDomain A] [IsDomain B]
  (f : G →+*ᵍ H) {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0) (hinj : Function.Injective f)
  (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

include hb hb0 hinj hv in
theorem finrank_eq
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
    Module.finrank (Away G b) (Away H (f b)) = Module.finrank A B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  have hfb0 : f b ≠ 0 := fun h ↦ hb0 (hinj (h.trans (map_zero f).symm))
  have : IsDomain (Away G b) := GradedChartBasis.chart_isDomain G hb0
  have : IsDomain (Away H (f b)) := GradedChartBasis.chart_isDomain H hfb0
  have : Module.Finite A B := FreeApproximationRank.finite_of_span v hgen
  have hg := GradedModulePieceMap.generators_of_span f v hgen
  have hcg := GradedDehomogenizationModule.generators_span f hb v hg
  have : Module.Finite (Away G b) (Away H (f b)) :=
    FreeApproximationRank.finite_of_span
      (fun i ↦ GradedDehomogenization.map H (f.map_mem hb) (v i)) hcg
  obtain ⟨s, m, q, hqm, hq0, hli, hclear⟩ :=
    HomogeneousFreeApproximation.exists_homogeneous_free_approximation f v w hv hgen
  have hglobal : Module.finrank A B = Fintype.card s :=
    FreeApproximationRank.finrank_eq (fun i : s ↦ v i) hinj hli q hq0 (fun z ↦
      (Submodule.mem_span_range_iff_exists_fun A).mpr (hclear z))
  have hcli := GradedDehomogenizationModule.linearIndependent f hb
    (fun i : s ↦ v i) (fun i : s ↦ w i) (fun i ↦ hv i) hfb0 hli
  have hδq : GradedDehomogenization.map G hb q ≠ 0 := fun h ↦ hq0
    (GradedDehomogenizationPieces.homogeneous_eq_zero G hb hb0 m hqm h)
  have hcq := GradedDehomogenizationModule.denominator f hb (fun i : s ↦ v i) q hclear
  have hchart : Module.finrank (Away G b) (Away H (f b)) = Fintype.card s :=
    FreeApproximationRank.finrank_eq
      (fun i : s ↦ GradedDehomogenization.map H (f.map_mem hb) (v i))
      (GradedDehomogenizationModule.chart_map_injective f hb hinj hfb0) hcli
      (GradedDehomogenization.map G hb q) hδq (fun z ↦
        (Submodule.mem_span_range_iff_exists_fun (Away G b)).mpr (hcq z))
  exact hchart.trans hglobal.symm

end PaperP1.GradedDehomogenizationRank
