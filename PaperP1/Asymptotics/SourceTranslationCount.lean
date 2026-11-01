module

public import PaperP1.Arithmetic.ActualSourceTranslations
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Uniform actual source-translation counts with explicit dyadic leading constants -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceTranslationCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.DyadicEndpointPairs
  PaperP1.ActualSourceTranslations

theorem uniform_counts (C : ℝ) {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      |((sourcePairs N a b L i j).card : ℚ) - (N : ℚ) * (2 / (b : ℚ) - 1 / (a : ℚ))| ≤
        3 * ((L + 1 : ℕ) : ℚ) ∧
      |((symmetricSources N a b L i j).card : ℚ) - (N : ℚ) * coefficient a b| ≤
        6 * ((L + 1 : ℕ) : ℚ) := by
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C
    ((a + b + 1 : ℕ) : ℝ) (by positivity) 1
  refine ⟨max Ngeom Npoly, ?_⟩
  intro N hN L hcrit i j
  obtain ⟨hNtwo, _, _, _, _, _⟩ := hgeom N ((le_max_left _ _).trans hN) L hcrit
  have hpolyNat : (a + b + 1) * (L + 1) < N := by
    have h := hpoly N ((le_max_right _ _).trans hN) L hcrit
    norm_num only [pow_one] at h
    exact_mod_cast h
  have hlarge : (a + b) * (L + 1) < N := by nlinarith only [hpolyNat]
  exact simple_errors hNtwo ha hab hinterior hcop hlarge i j

theorem all_heights (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ a b : ℕ,
      0 < a → a < b → b < 2 * a → a.Coprime b → b ≤ (L + 1) ^ 3 → ∀ i j : Fin (L + 1),
      |((sourcePairs N a b L i j).card : ℚ) - (N : ℚ) * (2 / (b : ℚ) - 1 / (a : ℚ))| ≤
        3 * ((L + 1 : ℕ) : ℚ) ∧
      |((symmetricSources N a b L i j).card : ℚ) - (N : ℚ) * coefficient a b| ≤
        6 * ((L + 1 : ℕ) : ℚ) := by
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C 3 (by norm_num) 4
  refine ⟨max Ngeom Npoly, ?_⟩
  intro N hN L hcrit a b ha hab hinterior hcop hheight i j
  have hNtwo := (hgeom N ((le_max_left _ _).trans hN) L hcrit).1
  have hpolyNat : 3 * (L + 1) ^ 4 < N := by
    exact_mod_cast hpoly N ((le_max_right _ _).trans hN) L hcrit
  have hcoeff : a + b ≤ 2 * (L + 1) ^ 3 := by omega
  have hmul := Nat.mul_le_mul_right (L + 1) hcoeff
  have hpower : (L + 1) ^ 3 * (L + 1) = (L + 1) ^ 4 := by ring
  have hlarge : (a + b) * (L + 1) < N := by nlinarith only [hmul, hpower, hpolyNat]
  exact simple_errors hNtwo ha hab hinterior hcop hlarge i j

theorem leading_counts (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      |((symmetricSources N 2 3 L i j).card : ℚ) - (N : ℚ) / 3| ≤ 6 * ((L + 1 : ℕ) : ℚ) ∧
      |((symmetricSources N 3 4 L i j).card : ℚ) - (N : ℚ) / 3| ≤ 6 * ((L + 1 : ℕ) : ℚ) := by
  obtain ⟨N23, h23⟩ := uniform_counts C (a := 2) (b := 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨N34, h34⟩ := uniform_counts C (a := 3) (b := 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨max N23 N34, ?_⟩
  intro N hN L hcrit i j
  have hleft := (h23 N ((le_max_left _ _).trans hN) L hcrit i j).2
  have hright := (h34 N ((le_max_right _ _).trans hN) L hcrit i j).2
  constructor
  · simpa only [leading_coefficients.1, mul_one_div] using hleft
  · simpa only [leading_coefficients.2, mul_one_div] using hright

end PaperP1.SourceTranslationCount
