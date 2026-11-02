module

public import PaperP1.Probability.HermiteReference
public import PaperP1.Probability.PoissonExponential

/-! # Actual exponential moments of the compound and Hermite references -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompoundPoissonExponential

open PaperP1.PoissonSequence PaperP1.PoissonExponential PaperP1.CompoundPoissonSeries

theorem hasSum_joint_exp (j : ℕ) (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasSum (fun z : ℕ × ℕ ↦ PoissonProduct.joint a b z * Real.exp (t * ((z.1 + j * z.2 : ℕ) : ℝ)))
      (Real.exp (a * (Real.exp t - 1) + b * (Real.exp ((j : ℝ) * t) - 1))) := by
  have hA := hasSum_mass_exp a t
  have hB := hasSum_mass_exp b ((j : ℝ) * t)
  have hs : Summable (fun z : ℕ × ℕ ↦ (mass a z.1 * Real.exp (t * z.1)) *
      (mass b z.2 * Real.exp (((j : ℝ) * t) * z.2))) :=
    hA.summable.mul_of_nonneg hB.summable
      (fun k ↦ mul_nonneg (PoissonPartialSums.mass_nonneg ha k) (Real.exp_pos _).le)
      (fun k ↦ mul_nonneg (PoissonPartialSums.mass_nonneg hb k) (Real.exp_pos _).le)
  have h := hA.mul hB hs
  rw [← Real.exp_add] at h
  convert h using 1
  funext z
  have hid : Real.exp (t * ((z.1 + j * z.2 : ℕ) : ℝ)) =
      Real.exp (t * z.1) * Real.exp (((j : ℝ) * t) * z.2) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hid]
  unfold PoissonProduct.joint
  ring

theorem hasSum_law_exp (j : ℕ) (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasSum (fun k : ℕ ↦ AtomicProbability.realMass (law j a b ha hb) k * Real.exp (t * k))
      (Real.exp (a * (Real.exp t - 1) + b * (Real.exp ((j : ℝ) * t) - 1))) := by
  have h := PushforwardMass.hasSum_map (hasSum_joint_exp j a b t ha hb)
    (fun z : ℕ × ℕ ↦ z.1 + j * z.2)
  have heq (k : ℕ) : PushforwardMass.map (fun z : ℕ × ℕ ↦ z.1 + j * z.2)
      (fun z ↦ PoissonProduct.joint a b z * Real.exp (t * ((z.1 + j * z.2 : ℕ) : ℝ))) k =
        AtomicProbability.realMass (law j a b ha hb) k * Real.exp (t * k) := by
    simpa only [realMass_law] using PushforwardMass.map_mul
      (fun z : ℕ × ℕ ↦ z.1 + j * z.2) (PoissonProduct.joint a b)
      (fun k : ℕ ↦ Real.exp (t * k)) k
  convert h using 1
  funext k
  exact (heq k).symm

theorem hasSum_hermite_exp (μ α t : ℝ) (hα : 0 ≤ α) (hαμ : α ≤ μ) :
    HasSum (fun k : ℕ ↦ AtomicProbability.realMass (HermiteReference.law μ α hα hαμ) k * Real.exp (t * k))
      (Real.exp (μ * (Real.exp t - 1) + (α / 2) * (Real.exp t - 1) ^ 2)) := by
  have h := hasSum_law_exp 2 (μ - α) (α / 2) t (sub_nonneg.mpr hαμ) (by positivity)
  have heq : (μ - α) * (Real.exp t - 1) + (α / 2) * (Real.exp ((2 : ℝ) * t) - 1) =
      μ * (Real.exp t - 1) + (α / 2) * (Real.exp t - 1) ^ 2 := by
    rw [show (2 : ℝ) * t = t + t by ring, Real.exp_add]
    ring
  simpa only [Nat.cast_ofNat, heq, HermiteReference.law] using h

end PaperP1.CompoundPoissonExponential
