module

public import PaperP1.Asymptotics.FixedRationalTripleProbability

/-! # All zero-intercept triples at fixed slope height, including every residual defect -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedRationalTripleMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RationalTripleNormalizers

local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Parameter := RationalTriplePrivateMass.Parameter
abbrev point := RationalTriplePrivateMass.point
abbrev alpha := RationalTriplePrivateMass.alpha
abbrev pool (N Q : ℕ) := RationalTriplePrivateMass.pool N Q 1

def Admissible (N Q : ℕ) (nonextremal : Bool) (p : Parameter) : Prop :=
  p.1 0 < p.1 1 ∧ p.1 1 < p.1 2 ∧ p.1 2 < 2 * p.1 0 ∧
    Nat.gcd (Nat.gcd (p.1 0) (p.1 1)) (p.1 2) = 1 ∧ p.1 2 ≤ Q ∧ 1 ≤ p.2 ∧
    (∀ i, point p i ∈ dyadicBlock N) ∧
    (nonextremal = true → ¬(p.1 0 = 10 ∧ p.1 1 = 12 ∧ p.1 2 = 15))

def parameters (N Q : ℕ) (nonextremal : Bool) : Finset Parameter := (pool N Q).filter (Admissible N Q nonextremal)
def hosts (N Q : ℕ) (nonextremal : Bool) : Finset (Fin 3 → ℕ) := (parameters N Q nonextremal).image point
def mass (N L Q : ℕ) (nonextremal : Bool) : ℝ :=
  ∑ X ∈ hosts N Q nonextremal, infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X)

theorem hosts_card (N Q : ℕ) (nonextremal : Bool) :
    (hosts N Q nonextremal).card ≤ 16 * (Q + 1) ^ 3 * N := by
  have hh : (hosts N Q nonextremal).card ≤ 16 * (Q + 1) ^ (3 * 1) * N :=
    card_image_le.trans ((card_le_card (filter_subset (Admissible N Q nonextremal) (pool N Q))).trans
      (RationalTriplePrivateMass.pool_bound N Q 1))
  simpa only [Nat.mul_one] using hh

theorem host_data {N Q : ℕ} {nonextremal : Bool} {X : Fin 3 → ℕ} (hX : X ∈ hosts N Q nonextremal) :
    ∃ p ∈ pool N Q, Admissible N Q nonextremal p ∧ point p = X := by
  obtain ⟨p, hp, hpx⟩ := mem_image.mp hX
  exact ⟨p, (mem_filter.mp hp).1, (mem_filter.mp hp).2, hpx⟩

theorem mem_hosts_of_source {N Q u v w t : ℕ} (nonextremal : Bool)
    (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u) (hprim : Nat.gcd (Nat.gcd u v) w = 1)
    (hwQ : w ≤ Q) (ht : 1 ≤ t) (hdyad : ∀ i, centres u v w t i ∈ dyadicBlock N)
    (hnon : nonextremal = true → ¬(u = 10 ∧ v = 12 ∧ w = 15)) :
    centres u v w t ∈ hosts N Q nonextremal := by
  let a : Fin 3 → ℕ := ![u, v, w]
  let p : Parameter := (a, t)
  have ha : a ∈ Fintype.piFinset (fun _ : Fin 3 ↦ range ((Q + 1) ^ 1 + 1)) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i <;> norm_num [a, mem_range] <;> omega
  have htN : t < 2 * N := by
    have hx := (mem_Ico.mp (hdyad 0)).2
    change u * t < 2 * N at hx
    have hmul := Nat.mul_le_mul_right t (show 1 ≤ u by omega)
    omega
  have hp : p ∈ pool N Q := mem_product.mpr ⟨ha, mem_range.mpr htN⟩
  have hadm : Admissible N Q nonextremal p := ⟨huv, hvw, hw2u, hprim, hwQ, ht, hdyad, hnon⟩
  exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hadm⟩, rfl⟩

theorem uniform_mass (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (hε : 0 < ε) (nonextremal : Bool) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass N L Q nonextremal ≤ (N : ℝ) ^ (1 - alpha nonextremal + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := FixedRationalTripleProbability.uniform_point_bound Q hQ C (ε / 2) (by positivity) nonextremal
  obtain ⟨NB, hb⟩ := HalfCountSchedule.factor_absorption (16 * (Q + 1 : ℝ) ^ 3)
    (1 - alpha nonextremal + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NA NB), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (X : Fin 3 → ℕ) (hX : X ∈ hosts N Q nonextremal) :
      infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) ≤ (N : ℝ) ^ (-alpha nonextremal + ε / 2) := by
    obtain ⟨p, _hp, ⟨huv, hvw, hw2u, hprim, hwQ, ht, hdyad, hnon⟩, rfl⟩ := host_data hX
    have hx := hdyad 0
    change p.1 0 * p.2 ∈ dyadicBlock N at hx
    exact ha N (by omega) L (p.1 0) (p.1 1) (p.1 2) p.2 hband huv hvw hw2u hprim hwQ ht hx hnon
  have hpow : (N : ℝ) * (N : ℝ) ^ (-alpha nonextremal + ε / 2) =
      (N : ℝ) ^ (1 - alpha nonextremal + ε / 2) := by
    calc
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-alpha nonextremal + ε / 2) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (1 + (-alpha nonextremal + ε / 2)) := by rw [← Real.rpow_add hn]
      _ = _ := by congr 1; ring
  calc
    _ ≤ ∑ _X ∈ hosts N Q nonextremal, (N : ℝ) ^ (-alpha nonextremal + ε / 2) := sum_le_sum hpoint
    _ = ((hosts N Q nonextremal).card : ℝ) * (N : ℝ) ^ (-alpha nonextremal + ε / 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (16 * (Q + 1 : ℝ) ^ 3 * N) * (N : ℝ) ^ (-alpha nonextremal + ε / 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hosts_card N Q nonextremal) (Real.rpow_nonneg hn.le _)
    _ = (16 * (Q + 1 : ℝ) ^ 3) * (N : ℝ) ^ (1 - alpha nonextremal + ε / 2) := by rw [← hpow]; ring
    _ ≤ (N : ℝ) ^ ((1 - alpha nonextremal + ε / 2) + ε / 2) := hb N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_full_mass (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L Q false ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  simpa only [alpha, RationalTriplePrivateMass.alpha, Bool.false_eq_true, ite_false,
    show (1 : ℝ) - 71 / 30 = -41 / 30 by norm_num] using uniform_mass Q hQ C ε hε false

theorem uniform_nonextremal_mass (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L Q true ≤ (N : ℝ) ^ (-25 / 18 + ε) := by
  simpa only [alpha, RationalTriplePrivateMass.alpha, ite_true,
    show (1 : ℝ) - 43 / 18 = -25 / 18 by norm_num] using uniform_mass Q hQ C ε hε true

def unorderedFamilies (N Q : ℕ) (nonextremal : Bool) : Finset (Finset ℕ) :=
  (hosts N Q nonextremal).image FiniteFamilyEnumeration.tupleSet

def unorderedMass (N L Q : ℕ) (nonextremal : Bool) : ℝ :=
  ∑ T ∈ unorderedFamilies N Q nonextremal, infiniteJointMoment L T

theorem unordered_mass_le (N L Q : ℕ) (nonextremal : Bool) : unorderedMass N L Q nonextremal ≤ mass N L Q nonextremal :=
  sum_image_le_of_nonneg (fun T _ ↦ infiniteJointMoment_nonneg L T)

theorem uniform_unordered_full_mass (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → unorderedMass N L Q false ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_full_mass Q hQ C ε hε
  exact ⟨N₀, hN₀, fun N hN L hband ↦ (unordered_mass_le N L Q false).trans (hu N hN L hband)⟩

theorem uniform_unordered_nonextremal_mass (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → unorderedMass N L Q true ≤ (N : ℝ) ^ (-25 / 18 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_nonextremal_mass Q hQ C ε hε
  exact ⟨N₀, hN₀, fun N hN L hband ↦ (unordered_mass_le N L Q true).trans (hu N hN L hband)⟩

end PaperP1.FixedRationalTripleMass
