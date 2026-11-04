module

public import PaperP1.Arithmetic.OccupiedDeterminantIntervals
public import PaperP1.Asymptotics.ConstructedClusterCurveData
public import PaperP1.Asymptotics.OrientedAuxiliaryLatticeData

/-! # Actual global primitive-source curve cover with both simultaneous ideal side sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurveCover

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals PaperP1.DeterminantIntervalPartition
open PaperP1.DeterminantHorizontalScale PaperP1.DeterminantLogScale PaperP1.DeterminantPositiveOrientation
open PaperP1.ActualProjectivePairs PaperP1.ConstructedClusterCurveData PaperP1.OccupiedDeterminantIntervals
open PaperP1.IntegerPairFactorCover PaperP1.QuadraticIntervalGrid

theorem uniform_global_cover (ε η δ C ρ Kshift Aexp ζ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hζ : 0 < ζ) (hζsmall : ζ < 7 / 16) (hgap : η + ζ / 2 < ε) :
    ∃ B Amax κ₀ κ₁ κf N₀ : ℕ, 0 < B ∧
      ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ Kshift * (Real.log N) ^ Aexp →
      ∀ X : Box N ρ C δ,
      let X' := orientedBox h X
      let M := horizontalScale N X.D X.E X.U X.V ζ
      let Sscale := Real.exp (logShape N X.D X.E X.U X.V)
      32 ≤ M ∧ 2 * M ≤ N ∧ (M : ℝ) * h.natAbs ≤ N ∧
      ∃ A₀ B₀ A₁ B₁ : ℕ → Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ T₀ T₁ : ℕ → ℝ,
        (∀ k : ℕ, k ≤ 2 * M → HorizontalGridCoordinateData.Data X' κ₀ M k (A₀ k) (B₀ k) (L₀ k) (L₁ k)) ∧
        (∀ q : ℕ, q ≤ 4 * M → VerticalGridCoordinateData.Data X' κ₁ M q (A₁ q) (B₁ q) (T₀ q) (T₁ q)) ∧
        ∀ S : Finset Quad, SignedPopulation X h S → (∀ p ∈ S, Primitive p) →
          let S' := orientedPopulation h S
          let I := occupied M X'.D X'.E S'
          ∃ F : ℕ → Bool × Bool → Finset ℤ[X][X],
            (∀ k ∈ I, M ≤ 4 * k ∧ k ≤ 2 * M) ∧
            (∀ k ∈ I, LocalCover N κf Amax B (cluster M X'.D X'.E k S')
              (B₀ k) (B₁ (grid M k)) (L₀ k) (T₀ (grid M k)) (F k)) ∧
            S.card ≤ ∑ k ∈ I, ∑ c : Bool × Bool, ∑ G ∈ F k c,
              (zeros G (FourProjectiveCharts.population c
                ((cluster M X'.D X'.E k S').image (coordinates (B₀ k) (B₁ (grid M k)))))).card ∧
            ((∑ k ∈ I, L₀ k) ≤ (N : ℝ) ^ ε * (Real.sqrt (X.D * X.E * Sscale) + X.D + X.E)) ∧
            ((∑ k ∈ I, T₀ (grid M k)) ≤ (N : ℝ) ^ ε * (Real.sqrt (X.U * X.V * Sscale) + X.U + X.V)) := by
  classical
  obtain ⟨B, Amax, κw, κ₀, κ₁, NA, hB, hdata⟩ :=
    OrientedAuxiliaryLatticeData.uniform_oriented_data ε η δ C ρ Kshift Aexp ζ
      hη hδ hC hρ hρ₁ hζ hζsmall hgap
  obtain ⟨κf, NC, hcover⟩ := uniform_local_cover Amax B κw κ₀ κ₁
  refine ⟨B, Amax, κ₀, κ₁, κf, max NA NC, hB, ?_⟩
  intro N hN h hh hshift X
  let X' := orientedBox h X
  let M := horizontalScale N X.D X.E X.U X.V ζ
  let Sscale := Real.exp (logShape N X.D X.E X.U X.V)
  obtain ⟨hM, hMN, hMh, A₀, B₀, A₁, B₁, L₀, L₁, T₀, T₁, hDdata, hUdata, hsums, haux⟩ :=
    hdata N (by omega) h hh hshift X
  refine ⟨hM, hMN, hMh, A₀, B₀, A₁, B₁, L₀, L₁, T₀, T₁, hDdata, hUdata, ?_⟩
  intro S hS hprimitive
  let S' := orientedPopulation h S
  let I := occupied M X'.D X'.E S'
  obtain ⟨hpopulation, hsigned, hpartition, hcurves⟩ := haux S hS
  have hprimitive' : ∀ p ∈ S', Primitive p := oriented_primitive h S hprimitive
  have hnorm : (M : ℝ) * |((h.natAbs : ℤ) : ℝ)| ≤ N := by
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg h.natAbs : (0 : ℝ) ≤ h.natAbs)] using hMh
  have hDp : 0 < X'.D := by linarith [X'.D_ge_one]
  have hEp : 0 < X'.E := by linarith [X'.E_ge_one]
  have hbox : ∀ p ∈ S', X'.D ≤ p.1.1 ∧ (p.1.1 : ℝ) ≤ 2 * X'.D ∧
      X'.E ≤ p.1.2 ∧ (p.1.2 : ℝ) ≤ 2 * X'.E := by
    intro p hp
    exact ⟨(hpopulation.d_bounds p hp).1, (hpopulation.d_bounds p hp).2,
      (hpopulation.e_bounds p hp).1, (hpopulation.e_bounds p hp).2⟩
  have hrange : ∀ k ∈ I, M ≤ 4 * k ∧ k ≤ 2 * M := index_range M (by omega) X'.D X'.E hDp hEp S' hbox
  have hlocal : ∀ k ∈ I, ∃ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax B (cluster M X'.D X'.E k S')
        (B₀ k) (B₁ (grid M k)) (L₀ k) (T₀ (grid M k)) F := by
    intro k hk
    obtain ⟨hkI, hcluster⟩ := mem_filter.mp hk
    have hkupper := (hrange k hk).2
    have hD := hDdata k hkupper
    have hU := hUdata (grid M k) (grid_upper M k (by omega) hkupper)
    obtain ⟨a, _, ha, w, hw, _, _, hH, hzero⟩ := hcurves k hkI hcluster
    exact hcover N (by omega) ρ C δ X' M k (A₀ k) (B₀ k) (A₁ (grid M k)) (B₁ (grid M k))
      (L₀ k) (L₁ k) (T₀ (grid M k)) (T₁ (grid M k)) hD hU (h.natAbs : ℤ) hnorm
      S' hsigned hprimitive' hcluster a ha B le_rfl w hw hH hzero
  have hchoice : ∀ k : ℕ, ∃ F : Bool × Bool → Finset ℤ[X][X],
      k ∈ I → LocalCover N κf Amax B (cluster M X'.D X'.E k S')
        (B₀ k) (B₁ (grid M k)) (L₀ k) (T₀ (grid M k)) F := by
    intro k
    by_cases hk : k ∈ I
    · obtain ⟨F, hF⟩ := hlocal k hk
      exact ⟨F, fun _ ↦ hF⟩
    · exact ⟨fun _ ↦ ∅, fun hki ↦ False.elim (hk hki)⟩
  choose F hF using hchoice
  have hlow : ∀ k ∈ I, M ≤ 4 * k := fun k hk ↦ (hrange k hk).1
  have hupper : ∀ k ∈ I, k ≤ 2 * M := fun k hk ↦ (hrange k hk).2
  have hside := hsums I hlow hupper
  refine ⟨F, hrange, hF, ?_, hside.1, hside.2⟩
  calc
    S.card = ∑ k ∈ I, (cluster M X'.D X'.E k S').card :=
      hpartition.trans (sum_clusters M X'.D X'.E S')
    _ ≤ _ := sum_le_sum (fun k hk ↦ (hF k hk).count)

end PaperP1.SourceCurveCover
