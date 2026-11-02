module

public import PaperP1.Asymptotics.RationalTriplePrivateProbability
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.LogarithmicWordPowers
public import Mathlib.Data.Fintype.Pi

/-! # Aggregate actual private rational triples at polynomial logarithmic slope height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTriplePrivateMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateNormalizedFamilies
  PaperP1.RationalTripleNormalizers PaperP1.CriticalBandScale

local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Parameter := (Fin 3 → ℕ) × ℕ

def point (p : Parameter) : Fin 3 → ℕ := centres (p.1 0) (p.1 1) (p.1 2) p.2
def alpha (nonextremal : Bool) : ℝ := if nonextremal then 43 / 18 else 71 / 30
def coefficient (C : ℝ) (nonextremal : Bool) : ℝ := BinaryRankPowers.constant C (alpha nonextremal) 5

def pool (N L k : ℕ) : Finset Parameter :=
  (Fintype.piFinset fun _ : Fin 3 ↦ range ((L + 1) ^ k + 1)) ×ˢ range (2 * N)

def Admissible (N L : ℕ) (nonextremal : Bool) (p : Parameter) : Prop :=
  p.1 0 < p.1 1 ∧ p.1 1 < p.1 2 ∧ p.1 2 < 2 * p.1 0 ∧
    Nat.gcd (Nat.gcd (p.1 0) (p.1 1)) (p.1 2) = 1 ∧ 1 ≤ p.2 ∧
    (∀ i, point p i ∈ dyadicBlock N) ∧
    FiniteEvenSquareClasses.Private
      (valueUnion (scale (p.1 0) (p.1 1) (p.1 2)) (point p) L) ∧
    (nonextremal = true → ¬(p.1 0 = 10 ∧ p.1 1 = 12 ∧ p.1 2 = 15))

def parameters (N L k : ℕ) (nonextremal : Bool) : Finset Parameter := (pool N L k).filter (Admissible N L nonextremal)
def hosts (N L k : ℕ) (nonextremal : Bool) : Finset (Fin 3 → ℕ) := (parameters N L k nonextremal).image point
def mass (N L k : ℕ) (nonextremal : Bool) : ℝ :=
  ∑ X ∈ hosts N L k nonextremal, infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X)

theorem pool_card (N L k : ℕ) : (pool N L k).card = ((L + 1) ^ k + 1) ^ 3 * (2 * N) := by
  rw [pool, card_product, Fintype.card_piFinset_const, card_range, card_range]

theorem pool_bound (N L k : ℕ) : (pool N L k).card ≤ 16 * (L + 1) ^ (3 * k) * N := by
  have hp : 0 < (L + 1) ^ k := Nat.pow_pos (by omega)
  have htwo : (L + 1) ^ k + 1 ≤ 2 * (L + 1) ^ k := by omega
  have hpow := Nat.pow_le_pow_left htwo 3
  have hscale : (2 * (L + 1) ^ k) ^ 3 = 8 * (L + 1) ^ (3 * k) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]
    norm_num
  rw [hscale] at hpow
  rw [pool_card]
  have hh := Nat.mul_le_mul_right (2 * N) hpow
  convert hh using 1; ring

theorem hosts_card (N L k : ℕ) (nonextremal : Bool) :
    (hosts N L k nonextremal).card ≤ 16 * (L + 1) ^ (3 * k) * N :=
  card_image_le.trans ((card_le_card (filter_subset _ _)).trans (pool_bound N L k))

theorem host_data {N L k : ℕ} {nonextremal : Bool} {X : Fin 3 → ℕ}
    (hX : X ∈ hosts N L k nonextremal) :
    ∃ p ∈ pool N L k, Admissible N L nonextremal p ∧ point p = X := by
  obtain ⟨p, hp, hpx⟩ := mem_image.mp hX
  exact ⟨p, (mem_filter.mp hp).1, (mem_filter.mp hp).2, hpx⟩

theorem mem_hosts_of_source {N L k u v w t : ℕ} (nonextremal : Bool)
    (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u) (hprim : Nat.gcd (Nat.gcd u v) w = 1)
    (ht : 1 ≤ t) (hheight : w ≤ (L + 1) ^ k)
    (hdyad : ∀ i, centres u v w t i ∈ dyadicBlock N)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion (scale u v w) (centres u v w t) L))
    (hnon : nonextremal = true → ¬(u = 10 ∧ v = 12 ∧ w = 15)) :
    centres u v w t ∈ hosts N L k nonextremal := by
  let a : Fin 3 → ℕ := ![u, v, w]
  let p : Parameter := (a, t)
  have ha : a ∈ Fintype.piFinset (fun _ : Fin 3 ↦ range ((L + 1) ^ k + 1)) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i <;> norm_num [a, mem_range] <;> omega
  have htN : t < 2 * N := by
    have hx := (mem_Ico.mp (hdyad 0)).2
    change u * t < 2 * N at hx
    have hu : 1 ≤ u := by omega
    have hmul := Nat.mul_le_mul_right t hu
    omega
  have hp : p ∈ pool N L k := mem_product.mpr ⟨ha, mem_range.mpr htN⟩
  have hadm : Admissible N L nonextremal p := ⟨huv, hvw, hw2u, hprim, ht, hdyad, hprivate, hnon⟩
  exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hadm⟩, rfl⟩

theorem point_bound {N L k : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (nonextremal : Bool) {X : Fin 3 → ℕ} (hX : X ∈ hosts N L k nonextremal) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) ≤
      coefficient C nonextremal * (N : ℝ) ^ (-alpha nonextremal) := by
  obtain ⟨p, _hp, ⟨huv, hvw, hw2u, hprim, ht, _hdyad, hprivate, hnon⟩, rfl⟩ := host_data hX
  cases nonextremal
  · simpa only [point, coefficient, alpha, Bool.false_eq_true, ite_false, neg_div] using
      RationalTriplePrivateProbability.uniform_point_bound hN hL hband huv hvw hw2u hprim ht hprivate
  · simpa only [point, coefficient, alpha, ite_true, neg_div] using
      RationalTriplePrivateProbability.nonextremal_point_bound hN hL hband huv hvw hw2u hprim (hnon rfl) ht hprivate

theorem finite_mass_bound {N L k : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (nonextremal : Bool) :
    mass N L k nonextremal ≤
      (16 * coefficient C nonextremal) * ((L + 1 : ℕ) : ℝ) ^ (3 * k) * (N : ℝ) ^ (1 - alpha nonextremal) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcoef : 0 < coefficient C nonextremal := BinaryRankPowers.constant_pos _ _ _
  have hpower : (N : ℝ) * (N : ℝ) ^ (-alpha nonextremal) = (N : ℝ) ^ (1 - alpha nonextremal) := by
    calc
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-alpha nonextremal) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn, sub_eq_add_neg]
  calc
    _ ≤ ∑ _X ∈ hosts N L k nonextremal, coefficient C nonextremal * (N : ℝ) ^ (-alpha nonextremal) :=
      sum_le_sum (fun _ hX ↦ point_bound hN hL hband nonextremal hX)
    _ = ((hosts N L k nonextremal).card : ℝ) * (coefficient C nonextremal * (N : ℝ) ^ (-alpha nonextremal)) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (16 * ((L + 1 : ℕ) : ℝ) ^ (3 * k) * N) *
        (coefficient C nonextremal * (N : ℝ) ^ (-alpha nonextremal)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hosts_card N L k nonextremal) (by positivity)
    _ = (16 * coefficient C nonextremal) * ((L + 1 : ℕ) : ℝ) ^ (3 * k) *
        ((N : ℝ) * (N : ℝ) ^ (-alpha nonextremal)) := by ring
    _ = _ := by rw [hpower]

theorem uniform_mass (C : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) (nonextremal : Bool) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass N L k nonextremal ≤ (N : ℝ) ^ (1 - alpha nonextremal + ε) := by
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale
    upperScale_pos.le (16 * coefficient C nonextremal) (3 * k) ε hε
  refine ⟨max 10 (max NG NP), by omega, ?_⟩
  intro N hN L hband
  obtain ⟨_hN2, _hBmin, hBtwo, _hthin, _hBlo, hBhi⟩ := hg N (by omega) L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcoef : 0 < coefficient C nonextremal := BinaryRankPowers.constant_pos _ _ _
  have hfactor : (16 * coefficient C nonextremal) * ((L + 1 : ℕ) : ℝ) ^ (3 * k) ≤ (N : ℝ) ^ ε := by
    have hh := hp N (by omega) L hBhi
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (16 * coefficient C nonextremal) * (L + 1 : ℝ) ^ (3 * k))] using hh
  calc
    _ ≤ (16 * coefficient C nonextremal) * ((L + 1 : ℕ) : ℝ) ^ (3 * k) * (N : ℝ) ^ (1 - alpha nonextremal) :=
      finite_mass_bound (by omega) (by omega) hband nonextremal
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (1 - alpha nonextremal) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_full_mass (C : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L k false ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  simpa only [alpha, Bool.false_eq_true, ite_false, show (1 : ℝ) - 71 / 30 = -41 / 30 by norm_num] using
    uniform_mass C k ε hε false

theorem uniform_nonextremal_mass (C : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L k true ≤ (N : ℝ) ^ (-25 / 18 + ε) := by
  simpa only [alpha, ite_true, show (1 : ℝ) - 43 / 18 = -25 / 18 by norm_num] using
    uniform_mass C k ε hε true

def unorderedFamilies (N L k : ℕ) (nonextremal : Bool) : Finset (Finset ℕ) :=
  (hosts N L k nonextremal).image FiniteFamilyEnumeration.tupleSet

def unorderedMass (N L k : ℕ) (nonextremal : Bool) : ℝ :=
  ∑ T ∈ unorderedFamilies N L k nonextremal, infiniteJointMoment L T

theorem unordered_mass_le (N L k : ℕ) (nonextremal : Bool) :
    unorderedMass N L k nonextremal ≤ mass N L k nonextremal :=
  sum_image_le_of_nonneg (fun T _ ↦ infiniteJointMoment_nonneg L T)

theorem uniform_unordered_full_mass (C : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → unorderedMass N L k false ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_full_mass C k ε hε
  exact ⟨N₀, hN₀, fun N hN L hband ↦ (unordered_mass_le N L k false).trans (hu N hN L hband)⟩

theorem uniform_unordered_nonextremal_mass (C : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → unorderedMass N L k true ≤ (N : ℝ) ^ (-25 / 18 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_nonextremal_mass C k ε hε
  exact ⟨N₀, hN₀, fun N hN L hband ↦ (unordered_mass_le N L k true).trans (hu N hN L hband)⟩

end PaperP1.RationalTriplePrivateMass
