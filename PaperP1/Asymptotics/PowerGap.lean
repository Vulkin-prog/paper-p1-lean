module

public import PaperP1.Asymptotics.HalfCountSchedule

/-! # A fixed power gap absorbs every prescribed positive tolerance -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.PowerGap

theorem small (u v η : ℝ) (huv : u < v) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (N : ℝ) ^ u ≤ η * (N : ℝ) ^ v := by
  obtain ⟨NF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption η⁻¹ u (v - u) (by linarith)
  refine ⟨NF, ?_⟩
  intro N hN
  have h := mul_le_mul_of_nonneg_left (hF N hN) hη.le
  rw [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul] at h
  simpa only [show u + (v - u) = v by ring] using h

end PaperP1.PowerGap
