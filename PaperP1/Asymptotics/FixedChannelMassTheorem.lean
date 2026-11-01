module

public import PaperP1.Asymptotics.PrivateChannelMassPhase
public import PaperP1.Model.RealPrivateChannelSources

/-! # Companion T2.5 for the literal separated family and a fixed real prime cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelMassTheorem

open PaperP1.RealPrivateChannelSources PaperP1.PrivateChannelMassRate
  PaperP1.ChannelMainTermBounds

theorem eventual_mass_eq (C D : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        separatedChannelMass N D a b L = realChannelMass N D a b L := by
  obtain ⟨Ngeom, hgeom⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Nlarge, hlarge⟩ := PaperP1.CriticalPolynomialScale.polynomial_lt_scale
    C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max Ngeom Nlarge, ?_⟩
  intro N hN L hcrit
  have hNtwo := (hgeom N (by omega) L hcrit).1
  have hlargeN : (a + b) * (L + 1) < N := by
    have h := hlarge N (by omega) L hcrit
    simp only [pow_one] at h
    exact_mod_cast h
  exact separated_mass_eq D hNtwo ha hab hcop hlargeN hD

theorem strong_error (C D : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hD : 2 * (b : ℝ) ≤ D) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |separatedChannelMass N D a b L - mainTerm N L a b| ≤
          massConstant C b * ((L + 1 : ℕ) : ℝ) ^ 2 / N := by
  have hD0 : 0 ≤ D := (by positivity : (0 : ℝ) ≤ 2 * (b : ℝ)).trans hD
  obtain ⟨Nmass, hmass⟩ := mass_error_square_log C ⌈D⌉₊ a b ha hab hinterior hcop
  obtain ⟨Neq, heq⟩ := eventual_mass_eq C D a b ha hab hcop hD0
  refine ⟨max Nmass Neq, ?_⟩
  intro N hN L hcrit
  obtain ⟨hcut, hupper⟩ := cutoff_bounds D b L hD
  rw [heq N (by omega) L hcrit, real_channel_mass_eq N D a b L hD0]
  exact hmass N (by omega) L (cutoff D L) hcrit hcut hupper

theorem source_error (C D : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hD : 2 * (b : ℝ) ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |separatedChannelMass N D a b L - mainTerm N L a b| ≤ (N : ℝ) ^ (-1 + ε) := by
  have hD0 : 0 ≤ D := (by positivity : (0 : ℝ) ≤ 2 * (b : ℝ)).trans hD
  obtain ⟨Nmass, hmass⟩ := mass_error_rpow C ⌈D⌉₊ a b ha hab hinterior hcop ε hε
  obtain ⟨Neq, heq⟩ := eventual_mass_eq C D a b ha hab hcop hD0
  refine ⟨max Nmass Neq, ?_⟩
  intro N hN L hcrit
  obtain ⟨hcut, hupper⟩ := cutoff_bounds D b L hD
  rw [heq N (by omega) L hcrit, real_channel_mass_eq N D a b L hD0]
  exact hmass N (by omega) L (cutoff D L) hcrit hcut hupper

theorem source_positive_phase (C D : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hD : 2 * (b : ℝ) ≤ D) :
    ∃ c k : ℝ, 0 < c ∧ 0 < k ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        c * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ separatedChannelMass N D a b L ∧
        separatedChannelMass N D a b L ≤ k * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
  have hD0 : 0 ≤ D := (by positivity : (0 : ℝ) ≤ 2 * (b : ℝ)).trans hD
  obtain ⟨c, k, hc, hk, Nmass, hmass⟩ :=
    PaperP1.PrivateChannelMassPhase.positive_phase C ⌈D⌉₊ a b ha hab hinterior hcop
  obtain ⟨Neq, heq⟩ := eventual_mass_eq C D a b ha hab hcop hD0
  refine ⟨c, k, hc, hk, max Nmass Neq, ?_⟩
  intro N hN L hcrit
  obtain ⟨hcut, hupper⟩ := cutoff_bounds D b L hD
  rw [heq N (by omega) L hcrit, real_channel_mass_eq N D a b L hD0]
  exact hmass N (by omega) L (cutoff D L) hcrit hcut hupper

def Conclusion (C D : ℝ) (a b : ℕ) : Prop :=
  3 ≤ b ∧
  (∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |separatedChannelMass N D a b L - mainTerm N L a b| ≤
        massConstant C b * ((L + 1 : ℕ) : ℝ) ^ 2 / N) ∧
  (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |separatedChannelMass N D a b L - mainTerm N L a b| ≤ (N : ℝ) ^ (-1 + ε)) ∧
  (∃ c k : ℝ, 0 < c ∧ 0 < k ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      c * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ separatedChannelMass N D a b L ∧
      separatedChannelMass N D a b L ≤ k * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)))

theorem companion_T2_5 (C D : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hD : 2 * (b : ℝ) ≤ D) : Conclusion C D a b := by
  refine ⟨by omega, strong_error C D a b ha hab hinterior hcop hD, ?_,
    source_positive_phase C D a b ha hab hinterior hcop hD⟩
  intro ε hε
  exact source_error C D a b ha hab hinterior hcop hD ε hε

end PaperP1.FixedChannelMassTheorem
