module

public import PaperP1.Arithmetic.EnlargedEndpointTriplePool
public import PaperP1.Asymptotics.EnlargedFixedChannelPairProbability
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.LogarithmicWordPowers
public import PaperP1.Model.JointMonotonicity

/-! # Every polynomial-height endpoint target has negligible actual mass, including zero exact units and all arithmetic defects -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedEndpointAlignedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CriticalBandScale

local instance (P : Prop) : Decidable P := Classical.propDecidable P

structure Representation (N L a b J : ℕ) (T : Finset ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  t : ℕ
  c : ℕ
  d : ℕ
  i : Fin (L + 1)
  offset : ℤ
  family_eq : T = {x, y, z}
  x_dyadic : x ∈ dyadicBlock N
  y_dyadic : y ∈ dyadicBlock N
  z_dyadic : z ∈ dyadicBlock N
  numerator_pos : 0 < c
  denominator_pos : 0 < d
  coprime : c.Coprime d
  denominator_height : d ≤ (L + 1) ^ J
  offset_height : |offset| ≤ ((L + 1) ^ J : ℕ)
  source_x : startCompleteVertexLabel x L i = a * t
  source_geometry : EnlargedPairGeometry.Geometric a b x y L
  target : (d : ℤ) * z = (c : ℤ) * t + offset
  near_endpoint : EndpointAlignedTriplePool.Near N a b (EnlargedEndpointTriplePool.radius a b L J) t

def hosts (N L a b J : ℕ) : Finset (Finset ℕ) :=
  (EnlargedEndpointTriplePool.families N L a b J).filter fun T ↦ T.card = 3 ∧ Nonempty (Representation N L a b J T)

def mass (N L a b J : ℕ) : ℝ := ∑ T ∈ hosts N L a b J, infiniteJointMoment L T

theorem hosts_card {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N L J : ℕ) :
    (hosts N L a b J).card ≤ 6 * a * (2 * EnlargedSourceTargetGeometry.sourceScale a b + 1) * (4 * EnlargedSourceTargetGeometry.sourceScale a b + 10) * (L + 1) ^ (4 * J + 3) :=
  (card_le_card (filter_subset _ _)).trans (EnlargedEndpointTriplePool.families_card ha hb N L J)

theorem host_data {N L a b J : ℕ} {T : Finset ℕ} (hT : T ∈ hosts N L a b J) :
    T.card = 3 ∧ Nonempty (Representation N L a b J T) := (mem_filter.mp hT).2

theorem source_mem_hosts {N L a b J : ℕ} {T : Finset ℕ} (r : Representation N L a b J T)
    (hcard : T.card = 3) (hN : 2 ≤ N) (ha : 0 < a)
    (hsize : (a * EnlargedSourceTargetGeometry.sourceScale a b) * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) : T ∈ hosts N L a b J := by
  apply mem_filter.mpr
  refine ⟨?_, hcard, ⟨r⟩⟩
  rw [r.family_eq]
  exact EnlargedEndpointTriplePool.source_mem_families (by omega : 0 < N) ha r.x_dyadic r.y_dyadic r.z_dyadic
    r.numerator_pos r.denominator_pos r.denominator_height r.offset_height r.source_geometry r.i r.source_x r.target
    r.near_endpoint hsize

theorem all_actual_sources (a b J : ℕ) (ha : 0 < a) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ T : Finset ℕ, T.card = 3 → Representation N L a b J T → T ∈ hosts N L a b J := by
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.source_size_eventually C (a * EnlargedSourceTargetGeometry.sourceScale a b) J
  refine ⟨max 10 NS, by omega, ?_⟩
  intro N hN L hband T hcard r
  exact source_mem_hosts r hcard (by omega) ha (hs N (by omega) L ((L + 1) ^ J) hband le_rfl)

theorem uniform_count {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ((hosts N L a b J).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale
    upperScale_pos.le (6 * (a : ℝ) * (2 * (EnlargedSourceTargetGeometry.sourceScale a b : ℝ) + 1) * (4 * (EnlargedSourceTargetGeometry.sourceScale a b : ℝ) + 10)) (4 * J + 3) ε hε
  refine ⟨max 10 (max NG NP), by omega, ?_⟩
  intro N hN L hband
  have hfactor : 6 * (a : ℝ) * (2 * (EnlargedSourceTargetGeometry.sourceScale a b : ℝ) + 1) * (4 * (EnlargedSourceTargetGeometry.sourceScale a b : ℝ) + 10) * ((L + 1 : ℕ) : ℝ) ^ (4 * J + 3) ≤ (N : ℝ) ^ ε := by
    have hh := hp N (by omega) L (hg N (by omega) L hband).2.2.2.2.2
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 6 * (a : ℝ) * (2 * (EnlargedSourceTargetGeometry.sourceScale a b : ℝ) + 1) * (4 * (EnlargedSourceTargetGeometry.sourceScale a b : ℝ) + 10) * (L + 1 : ℝ) ^ (4 * J + 3))] using hh
  exact (by exact_mod_cast hosts_card ha hb N L J :
    ((hosts N L a b J).card : ℝ) ≤ 6 * (a : ℝ) * (2 * (EnlargedSourceTargetGeometry.sourceScale a b : ℝ) + 1) * (4 * (EnlargedSourceTargetGeometry.sourceScale a b : ℝ) + 10) * ((L + 1 : ℕ) : ℝ) ^ (4 * J + 3)).trans hfactor

theorem uniform_mass {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b) (hab : a < b)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L a b J ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := uniform_count ha (by omega : 0 < b) J C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := EnlargedFixedChannelPairProbability.uniform_coarse ha hb hab hcop C (ε / 2) (by positivity)
  refine ⟨max 10 (max NC NP), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (T : Finset ℕ) (hT : T ∈ hosts N L a b J) :
      infiniteJointMoment L T ≤ (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    obtain ⟨_hcard, ⟨r⟩⟩ := host_data hT
    have hsub₀ : ({r.x, r.y} : Finset ℕ) ⊆ {r.x, r.y, r.z} := by
      intro n hn
      simp only [mem_insert, mem_singleton] at hn ⊢
      tauto
    have hsub : ({r.x, r.y} : Finset ℕ) ⊆ T := hsub₀.trans (le_of_eq r.family_eq.symm)
    exact (infiniteJointMoment_antitone L hsub).trans
      (hp N (by omega) L r.x r.y hband r.x_dyadic r.y_dyadic r.source_geometry)
  calc
    _ ≤ ∑ _T ∈ hosts N L a b J, (N : ℝ) ^ (-5 / 3 + ε / 2) := sum_le_sum hpoint
    _ = ((hosts N L a b J).card : ℝ) * (N : ℝ) ^ (-5 / 3 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-5 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.EnlargedEndpointAlignedTripleMass
