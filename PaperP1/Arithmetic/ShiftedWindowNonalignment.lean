module

public import PaperP1.Arithmetic.ActualOffsetNonalignment
public import PaperP1.Arithmetic.AsymmetricEnvelopeGraph

/-! # The exact compressed-center exclusion controls the whole shifted interval of actual radius R -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedWindowNonalignment

open PaperP1.NormalizedUnitCount PaperP1.AsymmetricEnvelopeGraph

theorem of_compressed {x y L R D : ℕ} (hx : R < x) (hy : R < y)
    (hR : R ≤ D * (L + 1)) (hcap : 2 * R ≤ (L + 1) ^ 3)
    (hno : ¬CompressedTargetAlignment.Aligned D x y L) :
    ActualOffsetNonalignment.NoExact (start x R) (start y R) (2 * R) := by
  intro u₁ u₂ v₁ v₂ hne he
  apply hno
  let p : ℤ × ℤ := ((R : ℤ) - u₁.val, (R : ℤ) - v₁.val)
  let q : ℤ × ℤ := ((R : ℤ) - u₂.val, (R : ℤ) - v₂.val)
  have hoff (i : Fin (2 * R + 1)) : |(R : ℤ) - i.val| ≤ (R : ℤ) := by
    have hi := i.isLt
    rw [abs_le]
    omega
  have hp : |p.1| ≤ (R : ℤ) ∧ |p.2| ≤ (R : ℤ) := ⟨hoff u₁, hoff v₁⟩
  have hq : |q.1| ≤ (R : ℤ) ∧ |q.2| ≤ (R : ℤ) := ⟨hoff u₂, hoff v₂⟩
  have hpq : p ≠ q := by
    intro hh
    apply hne
    apply Prod.ext
    · have h := congrArg Prod.fst hh
      dsimp [p, q, offset] at h ⊢
      omega
    · have h := congrArg Prod.snd hh
      dsimp [p, q, offset] at h ⊢
      omega
  have hxc : ((start x R : ℕ) : ℤ) = (x : ℤ) - R + 1 := by
    simp only [start, Nat.cast_add, Nat.cast_one, Nat.cast_sub hx.le]
  have hyc : ((start y R : ℕ) : ℤ) = (y : ℤ) - R + 1 := by
    simp only [start, Nat.cast_add, Nat.cast_one, Nat.cast_sub hy.le]
  have hcross : (q.1 - p.1) * ((y : ℤ) - p.2) =
      (q.2 - p.2) * ((x : ℤ) - p.1) := by
    rw [hxc, hyc] at he
    dsimp [offset] at he
    dsimp [p, q]
    nlinarith only [he]
  obtain ⟨a, b, ha, hb, hcop, haR, hbR, hd⟩ :=
    BoundedPointAlignment.alignment_of_cross R (x : ℤ) (y : ℤ) p q
      (by exact_mod_cast hx) (by exact_mod_cast hy) hp hq hpq hcross
  refine ⟨a, b, ha, hb, hcop, haR.trans hcap, hbR.trans hcap, ?_⟩
  rw [abs_sub_comm]
  exact hd.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hR)
    (Nat.cast_nonneg (α := ℤ) (a + b)))

end PaperP1.ShiftedWindowNonalignment
