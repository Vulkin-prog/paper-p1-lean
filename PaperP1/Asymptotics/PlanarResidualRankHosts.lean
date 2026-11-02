module

public import PaperP1.Arithmetic.FullComponentMotifs
public import PaperP1.Asymptotics.CoverPrimeSmallCost

/-! # Macroscopic covered relation spaces on prescribed planes have small actual host mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlanarResidualRankHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.TripleCross
  PaperP1.ThreeBlockCoordinates PaperP1.TripleCoverRank PaperP1.CoverGraphResolution
  PaperP1.ManyPlanarSquareProducts PaperP1.OrientedPlanarMotifCount

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Residual (η : ℝ) (X : Fin 3 → ℕ) (L H : ℕ) : Prop :=
  ∃ D : Finset (Vertex L), SharedPrimeCover.CoversShared X L H D ∧
    η * L ≤ (Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) : ℝ)

theorem residual_forces_many {η : ℝ} (hη : 0 < η) {X : Fin 3 → ℕ} {L H : ℕ}
    (hL : 1 ≤ L) (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hinj : ∀ i, Function.Injective (evenSquareClassMap (X i) L))
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)))
    (hcost : (3 * (LocalDefectBound.primeCount H + 2) : ℝ) ≤ η * (L + 1) / 4)
    (hres : Residual η X L H) : Many (η / 4) L H X := by
  obtain ⟨D, hD, hdim⟩ := hres
  have hcover := (SharedPrimeCover.cover_iff_shared (fun i ↦ by have hh := hX i; omega) hH D).mpr hD
  have hbound := (finite_rank_bound hX hH hinj hpair D hcover).2
  have hreal : (Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) : ℝ) ≤
      fullCount X L H D + 3 * ((LocalDefectBound.primeCount H : ℝ) + 2) := by exact_mod_cast hbound
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hwidth : η * (L + 1) ≤ 2 * (η * L) := by nlinarith only [hLR, hη]
  apply FullComponentMotifs.many_of_full_count hX hH D hcover
  nlinarith only [hreal, hdim, hcost, hwidth]

theorem uniform_all_covers (C C₀ η K ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ C₀ * (L + 1) →
      ∀ F : Finset Plane, (F.card : ℝ) ≤ (L + 1 : ℝ) ^ K →
      (∀ p ∈ F, p.1 ≠ 0 ∧ (∀ j, (↑(p.1 j).natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) ∧
        (p.2.natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) →
      ∀ S : Finset (Fin 3 → ℕ), (∀ X ∈ S, RegularDirect N L X) →
      (∀ X ∈ S, (∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2) ∧ Residual η X L H) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧ mass L S ≤ (N : ℝ) ^ (-1 + ε) ∧
        primitiveMass L S ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := companion_T20_6 C C₀ (η / 4) K ε (by positivity) hε
  obtain ⟨NP, _hNP, hp⟩ := CoverPrimeSmallCost.uniform_small_cost C C₀ η hη
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 10 (max NM (max NP NG)), by omega, ?_⟩
  intro N hN L H hband hBH hcut F hFcard hF S hS hcover
  obtain ⟨_hNtwo, _hBmin, hBtwo, _hthin, _hBlo, _hBhi⟩ := hg N (by omega) L hband
  have hcost := hp N (by omega) L H hband hBH hcut
  apply hm N (by omega) L H hband hcut F hFcard hF S hS
  intro X hX
  have hr := hS X hX
  have hXpos : ∀ i, 2 ≤ X i := by
    intro i
    have hh := (mem_Ico.mp (hr.2.1 i).1).1
    omega
  exact ⟨(hcover X hX).1, residual_forces_many hη (by omega) hXpos hBH
    (fun i ↦ TwoPointSquareClasses.injective_evenMap_of_rank (X i) L (hr.2.1 i).2)
    hr.2.2 hcost (hcover X hX).2⟩

def hosts (N L : ℕ) (C₀ η : ℝ) (F : Finset Plane) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 3 ↦ dyadicBlock N).filter fun X ↦
    RegularDirect N L X ∧ (∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2) ∧
      Residual η X L (cutoff C₀ L)

theorem hosts_data {N L : ℕ} {C₀ η : ℝ} {F : Finset Plane} {X : Fin 3 → ℕ}
    (hX : X ∈ hosts N L C₀ η F) :
    RegularDirect N L X ∧ (∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2) ∧
      Residual η X L (cutoff C₀ L) := (mem_filter.mp hX).2

/-- The prescribed-plane assertion of T20.8, with the existential cover left inside the host predicate. -/
theorem source_planar_assertion (C C₀ η K ε : ℝ) (hC₀ : 1 ≤ C₀) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset Plane, (F.card : ℝ) ≤ (L + 1 : ℝ) ^ K →
      (∀ p ∈ F, p.1 ≠ 0 ∧ (∀ j, (↑(p.1 j).natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) ∧
        (p.2.natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) →
      ((hosts N L C₀ η F).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧
        mass L (hosts N L C₀ η F) ≤ (N : ℝ) ^ (-1 + ε) ∧
        primitiveMass L (hosts N L C₀ η F) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_all_covers C C₀ η K ε hη hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hFcard hF
  have hcut := cutoff_bounds hC₀ L
  exact hu N hN L (cutoff C₀ L) hband hcut.1
    (by simpa only [Nat.cast_add, Nat.cast_one] using hcut.2) F hFcard hF
    (hosts N L C₀ η F) (fun _ hX ↦ (hosts_data hX).1)
    (fun _ hX ↦ ⟨(hosts_data hX).2.1, (hosts_data hX).2.2⟩)

end PaperP1.PlanarResidualRankHosts
