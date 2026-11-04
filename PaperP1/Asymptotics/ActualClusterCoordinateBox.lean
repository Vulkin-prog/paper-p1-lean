module

public import PaperP1.Arithmetic.ActualProjectivePairs
public import PaperP1.Asymptotics.HorizontalGridCoordinateData
public import PaperP1.Asymptotics.VerticalGridCoordinateData
public import PaperP1.Diophantine.FourChartRealBounds

/-! # Actual occupied-cluster points stay in the exact largest-side boxes in every chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualClusterCoordinateBox

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes PaperP1.TwoKernelDeterminantBoxes
open PaperP1.DeterminantRelativeIntervals PaperP1.DeterminantIntervalPartition PaperP1.ActualProjectivePairs

theorem coordinate_bounds {N κ₀ κ₁ M k : ℕ} {ρ C δ L₀ L₁ T₀ T₁ : ℝ} (X : Box N ρ C δ)
    (A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ)
    (hD : HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁)
    (hU : VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁)
    (h : ℤ) (hMh : (M : ℝ) * |(h : ℝ)| ≤ N) (S : Finset Quad) (hS : SignedPopulation X h S) :
    ∀ r ∈ (cluster M X.D X.E k S).image (coordinates B₀ B₁),
      (∀ i, |(r.1 i : ℝ)| ≤ L₀) ∧ ∀ i, |(r.2 i : ℝ)| ≤ T₀ := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hr
  obtain ⟨hpS, hindex⟩ := (mem_cluster M X.D X.E k S p).mp hp
  have hd := hS.d_bounds p hpS
  have he := hS.e_bounds p hpS
  have hfirst := hD.points ![(p.1.1 : ℤ), p.1.2]
    (by simpa using hd.1) (by simpa using hd.2) (by simpa using he.1) (by simpa using he.2)
    (by simpa using hindex)
  have hsecond := hU.points h hMh S hS p hpS (by rw [hindex])
  constructor
  · intro i
    change |(B₀.mulVec ![(p.1.1 : ℤ), p.1.2] i : ℝ)| ≤ L₀
    fin_cases i
    · exact hfirst.1
    · exact hfirst.2.trans hD.side_order
  · intro i
    change |(B₁.mulVec ![(p.2.2 : ℤ), p.2.1] i : ℝ)| ≤ T₀
    fin_cases i
    · exact hsecond.1
    · exact hsecond.2.trans hU.side_order

theorem chart_bounds {N κ₀ κ₁ M k : ℕ} {ρ C δ L₀ L₁ T₀ T₁ : ℝ} (X : Box N ρ C δ)
    (A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ)
    (hD : HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁)
    (hU : VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁)
    (h : ℤ) (hMh : (M : ℝ) * |(h : ℝ)| ≤ N) (S : Finset Quad) (hS : SignedPopulation X h S)
    (c : Bool × Bool) :
    ∀ r ∈ FourProjectiveCharts.population c ((cluster M X.D X.E k S).image (coordinates B₀ B₁)),
      (∀ i, |(r.1 i : ℝ)| ≤ L₀) ∧ ∀ i, |(r.2 i : ℝ)| ≤ T₀ :=
  FourChartRealBounds.population_bounds c _ L₀ T₀ (coordinate_bounds X A₀ B₀ A₁ B₁ hD hU h hMh S hS)

theorem nonempty_largest {N κ₀ κ₁ M k : ℕ} {ρ C δ L₀ L₁ T₀ T₁ : ℝ} (X : Box N ρ C δ)
    (A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ)
    (hD : HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁)
    (hU : VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁)
    (h : ℤ) (hMh : (M : ℝ) * |(h : ℝ)| ≤ N) (S : Finset Quad) (hS : SignedPopulation X h S)
    (hprimitive : ∀ p ∈ S, Primitive p) (hcluster : (cluster M X.D X.E k S).Nonempty) :
    1 ≤ L₀ ∧ 1 ≤ T₀ := by
  obtain ⟨p, hp⟩ := hcluster
  have hpS := ((mem_cluster M X.D X.E k S p).mp hp).1
  have hprim := coordinates_primitive A₀ B₀ A₁ B₁ hD.right_inverse hU.right_inverse p (hprimitive p hpS)
  have hbox := coordinate_bounds X A₀ B₀ A₁ B₁ hD hU h hMh S hS
    (coordinates B₀ B₁ p) (mem_image.mpr ⟨p, hp, rfl⟩)
  exact ⟨ReducedLatticeCoordinateBoxes.one_le_largest_of_primitive _ hprim.1 L₀ L₀ le_rfl ⟨hbox.1 0, hbox.1 1⟩,
    ReducedLatticeCoordinateBoxes.one_le_largest_of_primitive _ hprim.2 T₀ T₀ le_rfl ⟨hbox.2 0, hbox.2 1⟩⟩

end PaperP1.ActualClusterCoordinateBox
