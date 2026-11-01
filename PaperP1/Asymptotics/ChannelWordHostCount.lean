module

public import PaperP1.Arithmetic.ChannelWordHosts
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Positive and predecessor-signed channel word hosts with one height-uniform threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelWordHostCount

open Finset PaperP1.ChannelSumIdentity PaperP1.ActualSourceTranslations PaperP1.ChannelWordHosts

theorem all_heights (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ a b : ℕ,
      0 < a → a < b → b < 2 * a → a.Coprime b → b ≤ (L + 1) ^ 3 →
      |unsignedHosts N L a b - (N : ℚ) * coefficient a b * (unsigned L a b : ℤ)| ≤
        6 * ((L + 1 : ℕ) : ℚ) * (unsigned L a b : ℤ) ∧
      |signedHosts N L a b - (N : ℚ) * coefficient a b * (signed L a b : ℤ)| ≤
        6 * ((L + 1 : ℕ) : ℚ) * (unsigned L a b : ℤ) := by
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C 3 (by norm_num) 4
  refine ⟨max Ngeom Npoly, ?_⟩
  intro N hN L hcrit a b ha hab hinterior hcop hheight
  have hNtwo := (hgeom N ((le_max_left _ _).trans hN) L hcrit).1
  have hpolyNat : 3 * (L + 1) ^ 4 < N := by
    exact_mod_cast hpoly N ((le_max_right _ _).trans hN) L hcrit
  have hcoeff : a + b ≤ 2 * (L + 1) ^ 3 := by omega
  have hmul := Nat.mul_le_mul_right (L + 1) hcoeff
  have hpower : (L + 1) ^ 3 * (L + 1) = (L + 1) ^ 4 := by ring
  have hlarge : (a + b) * (L + 1) < N := by nlinarith only [hmul, hpower, hpolyNat]
  exact ⟨unsigned_error hNtwo ha hab hinterior hcop hlarge,
    signed_error hNtwo ha hab hinterior hcop hlarge⟩

end PaperP1.ChannelWordHostCount
