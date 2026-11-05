module

public import PaperP1.Analysis.PolynomialVelocitySmooth
public import PaperP1.Analysis.MonomialWronskianExceptions
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Genuine local regular pieces at actual nonsingular real curve points

The polynomial ODE supplies the trajectory. Continuity retains a nonzero
velocity coordinate on a smaller interval, and the defining equation persists.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalRegularTangentPiece

open Set Filter MvPolynomial PolynomialTangentTrajectory NonstationaryTangentImage
  PolynomialVelocitySmooth MonomialWronskianExceptions
open scoped Topology

theorem exists_trajectory (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) (t₀ : ℝ) :
    ∃ φ : Fin 2 → ℝ → ℝ, position φ t₀ = z ∧ ∃ ε : ℝ, 0 < ε ∧
      Trajectory P φ (Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨α, hα, ε, hε, hder⟩ := (contDiff_velocity P 1).contDiffAt
    |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (x₀ := z) t₀
  refine ⟨(fun i t ↦ α t i), hα, ε, hε, ?_⟩
  intro t ht i
  exact (hasDerivAt_pi.mp (hder t ht)) i

theorem exists_regular_piece (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hreg : ∃ i, velocity P z i ≠ 0) :
    ∃ r : RegularPiece P, 0 ∈ Ioo r.left r.right ∧ position r.path 0 = z := by
  obtain ⟨φ, hφzero, ε, hε, hφ⟩ := exists_trajectory P z 0
  obtain ⟨i, hi⟩ := hreg
  have hzeroMem : 0 ∈ Ioo (0 - ε) (0 + ε) := ⟨by linarith, by linarith⟩
  have hc : ContinuousAt (position φ) 0 :=
    (continuousOn_position P φ _ hφ).continuousAt (isOpen_Ioo.mem_nhds hzeroMem)
  have hv : ContinuousAt (fun t ↦ velocity P (position φ t) i) 0 :=
    ((contDiff_pi.mp (contDiff_velocity P 1) i).continuous.continuousAt).comp hc
  have hn : velocity P (position φ 0) i ≠ 0 := by rw [hφzero]; exact hi
  have hnb : {t : ℝ | t ∈ Ioo (0 - ε) (0 + ε) ∧ velocity P (position φ t) i ≠ 0} ∈ 𝓝 0 :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds hzeroMem) (hv.eventually_ne hn)
  obtain ⟨a, b, h₀, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnb
  have htraj : Trajectory P φ (Ioo a b) := fun t ht ↦ hφ t (hsub ht).1
  have hpzero : eval (position φ 0) P = 0 := by rw [hφzero]; exact hzero
  let r : RegularPiece P :=
    ⟨a, b, h₀.1.trans h₀.2, φ, htraj, equation_zero P φ a b htraj 0 h₀ hpzero,
      fun t ht ↦ ⟨i, (hsub ht).2⟩⟩
  exact ⟨r, h₀, hφzero⟩

theorem exists_piece_at_nonsingular (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hgradient : ∃ i : Fin 2, eval z (pderiv i P) ≠ 0) :
    ∃ r : RegularPiece P, 0 ∈ Ioo r.left r.right ∧ position r.path 0 = z := by
  apply exists_regular_piece P z hzero
  obtain ⟨i, hi⟩ := hgradient
  fin_cases i
  · refine ⟨1, ?_⟩
    simpa [velocity] using neg_ne_zero.mpr hi
  · refine ⟨0, ?_⟩
    simpa [velocity] using hi

end PaperP1.LocalRegularTangentPiece
