module

public import PaperP1.Affine.StartSystem
public import PaperP1.Affine.RealProbability

/-!
# Exact finite-cylinder probabilities of run starts

The marginal is zero for an inconsistent affine prescription. Otherwise it is
the inverse power of two determined by the effective row rank. No local
rigidity or nominal-marginal substitution is used here.
-/

@[expose] public noncomputable section

open PaperP1.Algebra PaperP1.Probability PaperP1.Affine

namespace PaperP1.Model

/-- Effective rank of the actual run-start equations in a prime cylinder. -/
def startRank (M x L : ℕ) : ℕ :=
  Module.finrank 𝔽₂ (LinearMap.range (startSystem M x L))

theorem exactMarginal_start_eq_affineMass (M x L : ℕ) (hL : 0 < L) :
    exactMarginal (cylinderProbability M) (fun y => startIndicator y L) x =
      uniformSolutionMass (startSystem M x L) (startRhs L) := by
  classical
  unfold exactMarginal cylinderProbability uniformSolutionMass
  congr 1
  funext ω
  have hiff := startSystem_eq_startRhs_iff (M := M) (x := x) ω hL
  by_cases h : startSystem M x L ω = startRhs L
  · simp [indicatorValue, startIndicator, h, hiff.mp h]
  · simp [indicatorValue, startIndicator, h, mt hiff.mpr h]

theorem exactMarginal_start_of_compatible (M x L : ℕ) (hL : 0 < L)
    (h : Compatible (startSystem M x L) (startRhs L)) :
    exactMarginal (cylinderProbability M) (fun y => startIndicator y L) x =
      (2 ^ startRank M x L : ℝ)⁻¹ := by
  rw [exactMarginal_start_eq_affineMass M x L hL]
  exact uniformSolutionMass_of_compatible _ _ h

theorem exactMarginal_start_of_not_compatible (M x L : ℕ) (hL : 0 < L)
    (h : ¬Compatible (startSystem M x L) (startRhs L)) :
    exactMarginal (cylinderProbability M) (fun y => startIndicator y L) x = 0 := by
  rw [exactMarginal_start_eq_affineMass M x L hL]
  exact uniformSolutionMass_of_not_compatible _ _ h

theorem exactMarginal_start_pos_iff (M x L : ℕ) (hL : 0 < L) :
    0 < exactMarginal (cylinderProbability M) (fun y => startIndicator y L) x ↔
      Compatible (startSystem M x L) (startRhs L) := by
  rw [exactMarginal_start_eq_affineMass M x L hL, uniformSolutionMass_pos_iff]

theorem dyadicMarginal_of_compatible (N L x : ℕ) (hL : 0 < L)
    (h : Compatible (startSystem (dyadicCutoff N L) x L) (startRhs L)) :
    dyadicMarginal N L x = (2 ^ startRank (dyadicCutoff N L) x L : ℝ)⁻¹ :=
  exactMarginal_start_of_compatible _ _ _ hL h

theorem dyadicMarginal_of_not_compatible (N L x : ℕ) (hL : 0 < L)
    (h : ¬Compatible (startSystem (dyadicCutoff N L) x L) (startRhs L)) :
    dyadicMarginal N L x = 0 :=
  exactMarginal_start_of_not_compatible _ _ _ hL h

theorem dyadicMarginal_pos_iff (N L x : ℕ) (hL : 0 < L) :
    0 < dyadicMarginal N L x ↔
      Compatible (startSystem (dyadicCutoff N L) x L) (startRhs L) :=
  exactMarginal_start_pos_iff _ _ _ hL

end PaperP1.Model
