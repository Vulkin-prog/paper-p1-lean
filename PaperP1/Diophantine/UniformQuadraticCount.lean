module

public import PaperP1.Diophantine.SquareQuadraticCount

@[expose] public section

/-!
# Companion T1.2: coefficient-uniform positive quadratic counts

Every threshold is chosen before the coefficients and the solution set.
The final theorem uses the literal fixed positive real exponent A₀.
-/

namespace PaperP1.UniformQuadraticCount

open Finset PellInput

theorem product_square_of_ratio_square
    {A C : ℕ} (hC : 0 < C) (hsq : IsSquare ((A : ℚ) / (C : ℚ))) :
    IsSquare ((A * C : ℕ) : ℚ) := by
  obtain ⟨q, hq⟩ := hsq
  refine ⟨q * (C : ℚ), ?_⟩
  have hCne : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hmul : (A : ℚ) = (q * q) * C := (div_eq_iff hCne).mp hq
  push_cast
  rw [hmul]
  ring

theorem positive_count_le_rpow_eventually
    (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A C H : ℕ, ∀ e : ℤ,
      0 < A → 0 < C → e ≠ 0 →
      A ≤ N ^ K → C ≤ N ^ K → H ≤ N ^ K → e.natAbs ≤ N ^ K →
      ∀ s : Finset (ℤ × ℤ),
        (∀ z ∈ s, pellBox A C e H z ∧ 0 < z.1 ∧ 0 < z.2) →
        (s.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Np, hp⟩ := PolynomialPellCount.pellBox_atMost_rpow_eventually K ε hε
  obtain ⟨Nd, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually (2 * K) ε hε
  refine ⟨max Np Nd, ?_⟩
  intro N hN A C H e hA hC he hAN hCN hHN heN s hs
  by_cases hsq : IsSquare ((A * C : ℕ) : ℚ)
  · have hcount := QuadraticCount.square_positive_count_le_divisors hA hC he hsq s
      (fun z hz => ⟨(hs z hz).1.1, (hs z hz).2⟩)
    have hheight : ((A : ℤ) * e).natAbs ≤ N ^ (2 * K) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      calc
        A * e.natAbs ≤ N ^ K * N ^ K := Nat.mul_le_mul hAN heN
        _ = N ^ (2 * K) := by rw [← pow_add, ← two_mul]
    have hdiv := hd N ((le_max_right _ _).trans hN) _ hheight
    exact (by exact_mod_cast hcount : (s.card : ℝ) ≤
      (((A : ℤ) * e).natAbs.divisors.card : ℝ)).trans hdiv
  · have hratio : ¬ IsSquare ((A : ℚ) / (C : ℚ)) :=
      fun h => hsq (product_square_of_ratio_square hC h)
    exact hp N ((le_max_left _ _).trans hN) A C H e hA hC hratio he
      hAN hCN hHN heN s (fun z hz => (hs z hz).1)

/-- The exact finite set of positive integer solutions in an integral box. -/
noncomputable def positiveQuadraticSolutions
    (A C : ℕ) (e : ℤ) (H : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc 1 (H : ℤ)) ×ˢ Finset.Icc 1 (H : ℤ)).filter
    (pellEquation A C e)

theorem mem_positiveQuadraticSolutions
    {A C H : ℕ} {e : ℤ} {z : ℤ × ℤ} :
    z ∈ positiveQuadraticSolutions A C e H ↔
      pellBox A C e H z ∧ 0 < z.1 ∧ 0 < z.2 := by
  classical
  simp only [positiveQuadraticSolutions, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, pellBox]
  constructor
  · rintro ⟨⟨⟨hx1, hxH⟩, ⟨hy1, hyH⟩⟩, heq⟩
    refine ⟨⟨heq, ?_, ?_⟩, by omega, by omega⟩
    · have hcast : (z.1.natAbs : ℤ) ≤ (H : ℤ) := by
        rw [Int.natAbs_of_nonneg (by omega)]
        exact hxH
      exact_mod_cast hcast
    · have hcast : (z.2.natAbs : ℤ) ≤ (H : ℤ) := by
        rw [Int.natAbs_of_nonneg (by omega)]
        exact hyH
      exact_mod_cast hcast
  · rintro ⟨⟨heq, hxH, hyH⟩, hx, hy⟩
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, heq⟩
    · have hcast : (z.1.natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast hxH
      rwa [Int.natAbs_of_nonneg hx.le] at hcast
    · have hcast : (z.2.natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast hyH
      rwa [Int.natAbs_of_nonneg hy.le] at hcast

/-- Actual cardinality form at every fixed polynomial height with an
integer exponent. -/
theorem cardinality_le_rpow_eventually
    (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A C H : ℕ, ∀ e : ℤ,
      0 < A → 0 < C → e ≠ 0 →
      A ≤ N ^ K → C ≤ N ^ K → H ≤ N ^ K → e.natAbs ≤ N ^ K →
      ((positiveQuadraticSolutions A C e H).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := positive_count_le_rpow_eventually K ε hε
  refine ⟨N₀, ?_⟩
  intro N hN A C H e hA hC he hAN hCN hHN heN
  exact hN₀ N hN A C H e hA hC he hAN hCN hHN heN _
    (fun _ hz => mem_positiveQuadraticSolutions.mp hz)

/-- The floor convention is exactly the literal real-height restriction on
positive integral coordinates. -/
theorem mem_positiveQuadraticSolutions_real_height
    {A C : ℕ} {e : ℤ} {X : ℝ} (hX : 0 ≤ X) {z : ℤ × ℤ} :
    z ∈ positiveQuadraticSolutions A C e ⌊X⌋₊ ↔
      pellEquation A C e z ∧ 0 < z.1 ∧ 0 < z.2 ∧
        (z.1 : ℝ) ≤ X ∧ (z.2 : ℝ) ≤ X := by
  rw [mem_positiveQuadraticSolutions]
  constructor
  · rintro ⟨⟨heq, hx, hy⟩, hx0, hy0⟩
    refine ⟨heq, hx0, hy0, ?_, ?_⟩
    · have hcast := (Nat.le_floor_iff hX).mp hx
      simpa only [Nat.cast_natAbs, Int.cast_abs,
        abs_of_pos (by exact_mod_cast hx0 : (0 : ℝ) < z.1)] using hcast
    · have hcast := (Nat.le_floor_iff hX).mp hy
      simpa only [Nat.cast_natAbs, Int.cast_abs,
        abs_of_pos (by exact_mod_cast hy0 : (0 : ℝ) < z.2)] using hcast
  · rintro ⟨heq, hx0, hy0, hx, hy⟩
    refine ⟨⟨heq, ?_, ?_⟩, hx0, hy0⟩
    · apply (Nat.le_floor_iff hX).mpr
      simpa only [Nat.cast_natAbs, Int.cast_abs,
        abs_of_pos (by exact_mod_cast hx0 : (0 : ℝ) < z.1)] using hx
    · apply (Nat.le_floor_iff hX).mpr
      simpa only [Nat.cast_natAbs, Int.cast_abs,
        abs_of_pos (by exact_mod_cast hy0 : (0 : ℝ) < z.2)] using hy

/-- Full companion T1.2: for every fixed real A₀ > 0 and ε > 0, the
eventual N^ε bound is uniform over all coefficients and positive solutions
in the N^A₀ box. The natural floor represents the exact integer height. -/
theorem uniform_quadratic_equation_count
    (A₀ : ℝ) (_hA₀ : 0 < A₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A C : ℕ, ∀ e : ℤ,
      0 < A → 0 < C → e ≠ 0 →
      (A : ℝ) ≤ (N : ℝ) ^ A₀ →
      (C : ℝ) ≤ (N : ℝ) ^ A₀ →
      |(e : ℝ)| ≤ (N : ℝ) ^ A₀ →
      ((positiveQuadraticSolutions A C e ⌊(N : ℝ) ^ A₀⌋₊).card : ℝ) ≤
        (N : ℝ) ^ ε := by
  obtain ⟨Ncore, hcore⟩ := cardinality_le_rpow_eventually ⌈A₀⌉₊ ε hε
  refine ⟨max Ncore 1, ?_⟩
  intro N hN A C e hA hC he hAN hCN heN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right Ncore 1).trans hN
  have hpow : (N : ℝ) ^ A₀ ≤ ((N ^ ⌈A₀⌉₊ : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hNone (Nat.le_ceil A₀)
  have hAe : A ≤ N ^ ⌈A₀⌉₊ := by exact_mod_cast hAN.trans hpow
  have hCe : C ≤ N ^ ⌈A₀⌉₊ := by exact_mod_cast hCN.trans hpow
  have hee : e.natAbs ≤ N ^ ⌈A₀⌉₊ := by
    have hcast : (e.natAbs : ℝ) ≤ ((N ^ ⌈A₀⌉₊ : ℕ) : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using heN.trans hpow
    exact_mod_cast hcast
  have hHe : ⌊(N : ℝ) ^ A₀⌋₊ ≤ N ^ ⌈A₀⌉₊ := by
    exact_mod_cast (Nat.floor_le (Real.rpow_nonneg (by positivity) _)).trans hpow
  exact hcore N ((le_max_left _ _).trans hN) A C _ e hA hC he hAe hCe hHe hee

end PaperP1.UniformQuadraticCount

