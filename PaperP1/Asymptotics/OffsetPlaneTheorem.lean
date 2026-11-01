module

public import PaperP1.Asymptotics.OffsetPlaneMass
public import PaperP1.Arithmetic.ThreePrimePlane
public import PaperP1.Arithmetic.SharedPrimeOffsets

/-! # Companion T20.3: the complete forced-plane proposition -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetPlaneTheorem

open Finset PaperP1.Arithmetic PaperP1.OffsetPlaneGeometry PaperP1.OffsetPlaneIntersections
  PaperP1.OffsetPlaneMass PaperP1.OffsetPlaneMassAsymptotic PaperP1.ThreePrimePlane
  PaperP1.SaturationPrimes PaperP1.TripleCross PaperP1.OffsetLinePopulation PaperP1.DefectivePredicate

def ForcedConclusion {L : ℕ} (X : Fin 3 → ℕ) (u : Code L) : Prop :=
  planeNormal u ≠ 0 ∧ geometry u ∈ family L ∧ (fun i ↦ (X i : ℝ)) ∈ geometry u ∧
    (∀ i, planeNormal u i ≠ 0) ∧ (∀ i, (planeNormal u i).natAbs ≤ 2 * (L + 1) ^ 2) ∧
    (planeConstant u).natAbs ≤ 6 * (L + 1) ^ 3 ∧
    ∀ (q : ℕ) (v : Fin 3 → Fin (L + 1)), 12 * (L + 1) ^ 3 < q →
      (∀ i, q ∣ value (X i) (v i)) → dot (planeNormal u) (offsetVector v) = -planeConstant u

def GeometryConclusion (N L : ℕ) (X : Fin 3 → ℕ) : Prop :=
  (∀ (p : Fin 2 → ℕ), Function.Injective p → ∀ (u : Fin 2 → Fin 3 → Fin (L + 1)),
    (∀ i, Nat.Prime (p i)) → (∀ i j, p i ∣ value (X j) (u i j)) →
      p 0 * p 1 ≤ 6 * N * (L + 1)) ∧
  ∀ (p : Fin 3 → ℕ), Function.Injective p → ∀ u : Code L,
    (∀ i, Nat.Prime (p i)) → (∀ i j, p i ∣ value (X j) (u i j)) →
      18 * N * (L + 1) ^ 2 < ∏ i, p i → ForcedConclusion X u

def SharedGeometryConclusion (N L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) : Prop :=
  (∀ p : ℕ, SharedPrimeOffsets.Shared (L := L) H X p →
    ∃! v : Fin 3 → Fin (L + 1), ∀ i, p ∈ oddPrimeSupport (value (X i) (v i))) ∧
  (∀ (p : Fin 2 → ℕ), Function.Injective p →
    (∀ i, SharedPrimeOffsets.Shared (L := L) H X (p i)) → p 0 * p 1 ≤ 6 * N * (L + 1)) ∧
  ∀ (p : Fin 3 → ℕ), Function.Injective p →
    ∀ hp : ∀ i, SharedPrimeOffsets.Shared (L := L) H X (p i),
      18 * N * (L + 1) ^ 2 < ∏ i, p i →
        let u : Code L := fun i ↦ SharedPrimeOffsets.offset (hp i)
        ForcedConclusion X u ∧
          ∀ (q : ℕ) (hq : SharedPrimeOffsets.Shared (L := L) H X q), 12 * (L + 1) ^ 3 < q →
            dot (planeNormal u) (offsetVector (SharedPrimeOffsets.offset hq)) = -planeConstant u

theorem shared_geometry_of_geometry {N L : ℕ} {H : ℝ} {X : Fin 3 → ℕ}
    (hH : ((L + 1 : ℕ) : ℝ) ≤ H) (hgeom : GeometryConclusion N L X) :
    SharedGeometryConclusion N L H X := by
  refine ⟨fun _ hp ↦ SharedPrimeOffsets.shared_unique_offset hH hp, ?_, ?_⟩
  · intro p hp hshared
    exact hgeom.1 p hp (fun i ↦ SharedPrimeOffsets.offset (hshared i))
      (fun i ↦ (hshared i).1) (fun i j ↦ SharedPrimeOffsets.offset_dvd (hshared i) j)
  · intro p hp hshared hlarge
    have hforced := hgeom.2 p hp (fun i ↦ SharedPrimeOffsets.offset (hshared i))
      (fun i ↦ (hshared i).1) (fun i j ↦ SharedPrimeOffsets.offset_dvd (hshared i) j) hlarge
    exact ⟨hforced, fun q hq hqbound ↦ hforced.2.2.2.2.2.2 q
      (SharedPrimeOffsets.offset hq) hqbound (SharedPrimeOffsets.offset_dvd hq)⟩

/-- Only the first two windows require full effective rank. -/
theorem finite_stronger {N L : ℕ} (X : Fin 3 → ℕ) (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1)
    (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hrank : ∀ i : Fin 3, i ≠ 2 → Module.finrank F₂ (squareClassSpace (X i) L) = L)
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L))) :
    GeometryConclusion N L X := by
  have hinj := PaperP1.TwoPointSquareClasses.injective_evenMap_of_rank (X 0) L (hrank 0 (by decide))
  refine ⟨?_, ?_⟩
  · intro p hp u hprime hdiv
    exact two_prime_bound X p hp u hN hLN hX hprime hdiv hinj (hpair (by decide))
  · intro p hp u hprime hdiv hlarge
    obtain ⟨hA, hcontains, hcoords, hheight, hconstant, hfurther⟩ :=
      forced_plane X p hp u hN hLN hX hprime hdiv hrank hpair hlarge
    exact ⟨hA, (mem_family L (geometry u)).mpr ⟨u, hA, rfl⟩,
      (geometry_contains_iff u X).mpr hcontains, hcoords, hheight, hconstant, hfurther⟩

/-- A single threshold precedes the length, actual centers, primes and offsets. -/
theorem uniform_stronger (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (family L).card ≤ (L + 1) ^ 9 ∧
      (∀ u : Code L, (∀ i, (planeNormal u i).natAbs ≤ 2 * (L + 1) ^ 2) ∧
        (planeConstant u).natAbs ≤ 6 * (L + 1) ^ 3) ∧
      pairMass N L ≤ (N : ℝ) ^ (-1 + ε) ∧
      ∀ X : Fin 3 → ℕ, (∀ i, X i ∈ Ico N (2 * N)) →
        (∀ i : Fin 3, i ≠ 2 → Module.finrank F₂ (squareClassSpace (X i) L) = L) →
        Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)) →
          GeometryConclusion N L X := by
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.SaturationDegrees.finite_conditions C 2 (by norm_num)
  obtain ⟨Nmass, hmass⟩ := pairMass_le_power_eventually C ε hε
  refine ⟨max Nfinite Nmass, ?_⟩
  intro N hN L hL
  obtain ⟨hN10, _, hLN, _, _⟩ := hfinite N (by omega) L hL
  exact ⟨family_card_le L, fun u ↦ ⟨normal_coordinate_bound u, constant_bound u⟩,
    hmass N (by omega) L hL, fun X hX hrank hpair ↦ finite_stronger X hN10 hLN hX hrank hpair⟩

/-- The source proposition, including the original affine mass of ordered primitive triples. -/
theorem companion_T20_3 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (family L).card ≤ (L + 1) ^ 9 ∧
      (∀ u : Code L, (∀ i, (planeNormal u i).natAbs ≤ 2 * (L + 1) ^ 2) ∧
        (planeConstant u).natAbs ≤ 6 * (L + 1) ^ 3) ∧
      primitiveMass N L ≤ (N : ℝ) ^ (-1 + ε) ∧
      ∀ X : Fin 3 → ℕ, (∀ i, X i ∈ Ico N (2 * N)) →
        (∀ i, Module.finrank F₂ (squareClassSpace (X i) L) = L) →
        Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)) →
          GeometryConclusion N L X := by
  obtain ⟨N₀, hN₀⟩ := uniform_stronger C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL
  obtain ⟨hcard, hheight, hmass, hgeom⟩ := hN₀ N hN L hL
  exact ⟨hcard, hheight, (primitiveMass_le_pairMass N L).trans hmass,
    fun X hX hrank hpair ↦ hgeom X hX (fun i _ ↦ hrank i) hpair⟩

/-- The exact source shared-prime population, with its unique odd-valuation offsets. -/
theorem companion_T20_3_shared (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (family L).card ≤ (L + 1) ^ 9 ∧ primitiveMass N L ≤ (N : ℝ) ^ (-1 + ε) ∧
      ∀ (H : ℝ), ((L + 1 : ℕ) : ℝ) ≤ H → ∀ X : Fin 3 → ℕ,
        (∀ i, X i ∈ Ico N (2 * N)) →
        (∀ i, Module.finrank F₂ (squareClassSpace (X i) L) = L) →
        Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)) →
          SharedGeometryConclusion N L H X := by
  obtain ⟨N₀, hN₀⟩ := companion_T20_3 C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL
  obtain ⟨hcard, _, hmass, hgeom⟩ := hN₀ N hN L hL
  exact ⟨hcard, hmass, fun H hH X hX hrank hpair ↦
    shared_geometry_of_geometry hH (hgeom X hX hrank hpair)⟩

end PaperP1.OffsetPlaneTheorem
