module

public import PaperP1.Asymptotics.PhysicalTargetTripleProbability
public import PaperP1.Arithmetic.AlignedTripleParameterPool
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Actual mass of all repeated-physical-slope targets, including exact contacts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalTargetTripleMass

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
  j : Fin (L + 1)
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
  source_y : startCompleteVertexLabel y L j = b * t
  target : (d : ℤ) * z = (c : ℤ) * t + offset
  physical : c = a * d ∨ c = b * d

def hosts (N L a b J : ℕ) : Finset (Finset ℕ) :=
  (AlignedTripleParameterPool.families N L a b J).filter fun T ↦ T.card = 3 ∧ Nonempty (Representation N L a b J T)

def mass (N L a b J : ℕ) : ℝ := ∑ T ∈ hosts N L a b J, infiniteJointMoment L T

theorem hosts_card (N L a b J : ℕ) : (hosts N L a b J).card ≤ 18 * a * N * (L + 1) ^ (3 * J + 2) :=
  (card_le_card (filter_subset _ _)).trans (AlignedTripleParameterPool.families_card N L a b J)

theorem host_data {N L a b J : ℕ} {T : Finset ℕ} (hT : T ∈ hosts N L a b J) :
    T.card = 3 ∧ Nonempty (Representation N L a b J T) := (mem_filter.mp hT).2

theorem source_mem_hosts {N L a b J : ℕ} {T : Finset ℕ} (r : Representation N L a b J T)
    (hcard : T.card = 3) (hN : 2 ≤ N) (ha : 0 < a)
    (hsize : a * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) : T ∈ hosts N L a b J := by
  apply mem_filter.mpr
  refine ⟨?_, hcard, ⟨r⟩⟩
  rw [r.family_eq]
  exact AlignedTripleParameterPool.source_mem_families hN ha r.x_dyadic r.y_dyadic r.z_dyadic
    r.numerator_pos r.denominator_pos r.denominator_height r.offset_height r.i r.j r.source_x r.source_y r.target hsize

theorem all_actual_sources (a b J : ℕ) (ha : 0 < a) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ T : Finset ℕ, T.card = 3 → Representation N L a b J T → T ∈ hosts N L a b J := by
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.source_size_eventually C a J
  refine ⟨max 10 NS, by omega, ?_⟩
  intro N hN L hband T hcard r
  exact source_mem_hosts r hcard (by omega) ha (hs N (by omega) L ((L + 1) ^ J) hband le_rfl)

theorem uniform_count (a b J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ((hosts N L a b J).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale
    upperScale_pos.le (18 * (a : ℝ)) (3 * J + 2) ε hε
  refine ⟨max 10 (max NG NP), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfactor : 18 * (a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ (3 * J + 2) ≤ (N : ℝ) ^ ε := by
    have hh := hp N (by omega) L (hg N (by omega) L hband).2.2.2.2.2
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 18 * (a : ℝ) * (L + 1 : ℝ) ^ (3 * J + 2))] using hh
  calc
    _ ≤ 18 * (a : ℝ) * N * ((L + 1 : ℕ) : ℝ) ^ (3 * J + 2) := by exact_mod_cast hosts_card N L a b J
    _ = (N : ℝ) * (18 * (a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ (3 * J + 2)) := by ring
    _ ≤ (N : ℝ) * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left hfactor hn.le
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ ε := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hn]

theorem uniform_mass {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L a b J ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := uniform_count a b J C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := PhysicalTargetTripleProbability.uniform_point_bound ha hab hb2a hcop J C (ε / 2) (by positivity)
  refine ⟨max 10 (max NC NP), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (T : Finset ℕ) (hT : T ∈ hosts N L a b J) :
      infiniteJointMoment L T ≤ (N : ℝ) ^ (-5 / 2 + ε / 2) := by
    obtain ⟨hcard, ⟨r⟩⟩ := host_data hT
    have hcardR : ({r.x, r.y, r.z} : Finset ℕ).card = 3 := by simpa only [r.family_eq] using hcard
    have hdistinct := RepeatedCoefficientUnionRank.triple_distinct hcardR
    rw [r.family_eq]
    exact hp N (by omega) L r.c r.d r.x r.y r.z r.t hband r.numerator_pos r.denominator_pos r.coprime
      r.denominator_height r.x_dyadic r.y_dyadic r.z_dyadic hdistinct.1 hdistinct.2 r.physical
      r.i r.j r.source_x r.source_y r.offset r.offset_height r.target
  calc
    _ ≤ ∑ _T ∈ hosts N L a b J, (N : ℝ) ^ (-5 / 2 + ε / 2) := sum_le_sum hpoint
    _ = ((hosts N L a b J).card : ℝ) * (N : ℝ) ^ (-5 / 2 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 + ε / 2) * (N : ℝ) ^ (-5 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.PhysicalTargetTripleMass
