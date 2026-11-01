module

public import PaperP1.Asymptotics.PrimeCylinderDivergence
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Data.Nat.Prime.Infinite

/-! # The literal extended-real liminf along the unbounded odd-prime filter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeCylinderLiminf

open Filter PaperP1.PrimeCylinderDivergence

def oddPrimeIndices : Filter ℕ := atTop ⊓ principal {q | Nat.Prime q ∧ 2 < q}

theorem oddPrimeIndices_neBot : NeBot oddPrimeIndices := by
  apply atTop_basis.inf_principal_neBot_iff.mpr
  intro n _
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max n 3)
  exact ⟨p, by exact ⟨by simpa only [Set.mem_Ici] using (le_max_left n 3).trans hp,
    hprime, by omega⟩⟩

theorem lowerRate_liminf (t : ℝ) :
    liminf (fun q ↦ (lowerRate t q : EReal)) oddPrimeIndices = ((t - 2) * Real.log 2 : ℝ) := by
  have : NeBot oddPrimeIndices := oddPrimeIndices_neBot
  have hlim : Tendsto (fun q ↦ (lowerRate t q : EReal)) oddPrimeIndices
      (nhds (((t - 2) * Real.log 2 : ℝ) : EReal)) :=
    (EReal.tendsto_coe.mpr (lowerRate_tendsto t)).mono_left (show oddPrimeIndices ≤ atTop from inf_le_left)
  exact hlim.liminf_eq

theorem companion_T19_7_liminf (t : ℝ) (ht : 2 < t) :
    (0 : EReal) < ((t - 2) * Real.log 2 : ℝ) ∧
      (((t - 2) * Real.log 2 : ℝ) : EReal) ≤
        liminf (fun q ↦ (positiveRate t q : EReal)) oddPrimeIndices ∧
      (((t - 2) * Real.log 2 : ℝ) : EReal) ≤
        liminf (fun q ↦ (totalRate t q : EReal)) oddPrimeIndices := by
  refine ⟨by exact_mod_cast threshold_positive ht, ?_, ?_⟩
  · rw [← lowerRate_liminf t]
    have hle : ∀ᶠ q in oddPrimeIndices, (lowerRate t q : EReal) ≤ positiveRate t q := by
      rw [oddPrimeIndices, eventually_inf_principal]
      exact Eventually.of_forall fun q hq ↦ by exact_mod_cast lowerRate_le_positive hq.1 t (by linarith)
    exact liminf_le_liminf hle
  · rw [← lowerRate_liminf t]
    have hle : ∀ᶠ q in oddPrimeIndices, (lowerRate t q : EReal) ≤ totalRate t q := by
      rw [oddPrimeIndices, eventually_inf_principal]
      exact Eventually.of_forall fun q hq ↦ by exact_mod_cast lowerRate_le_total hq.1 t (by linarith)
    exact liminf_le_liminf hle

end PaperP1.PrimeCylinderLiminf
