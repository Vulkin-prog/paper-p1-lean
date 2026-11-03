module

public import PaperP1.Algebra.UniformRationalInterpolation
public import PaperP1.Diophantine.IntegralRationalGraphBound

/-! # A grid-uniform bound for integral points on a reduced rational graph with nonconstant denominator -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GridRationalGraphBound

open Polynomial PaperP1.IntegralRationalInterpolation

def bound (a B : ℕ) : ℕ := heightBound a B + (2 * a).factorial * (heightBound a B) ^ (2 * a)

theorem integral_point (a B : ℕ) (hB : 1 ≤ B) (x y : Fin (2 * a + 1) → ℤ)
    (hinj : Function.Injective x) (hx : ∀ j, (x j).natAbs ≤ B) (hy : ∀ j, (y j).natAbs ≤ B)
    (p q : ℚ[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hqpos : 0 < q.natDegree) (hgrid : ∀ j, p.eval (x j : ℚ) = (y j : ℚ) * q.eval (x j : ℚ))
    (X Y : ℤ) (hpoint : p.eval (X : ℚ) = (Y : ℚ) * q.eval (X : ℚ)) : X.natAbs ≤ bound a B := by
  obtain ⟨P, Q, _, hP, hQ, hpc, hqc, hcopZ, _, δ, hδ, hpδ, hqδ⟩ :=
    UniformRationalInterpolation.exists_integral_presentation a B hB x y hinj hx hy p q hq0 hcop hdegree hgrid
  have hQdegree : Q.natDegree = q.natDegree :=
    (natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective Q).symm.trans
      (by rw [hqδ, natDegree_C_mul hδ])
  have hpointQ : (P.map (Int.castRingHom ℚ)).eval (X : ℚ) =
      (Y : ℚ) * (Q.map (Int.castRingHom ℚ)).eval (X : ℚ) := by
    rw [hpδ, hqδ]
    simp only [eval_mul, eval_C]
    rw [hpoint]
    ring
  have hpointZ : P.eval X = Y * Q.eval X := by
    apply (Int.cast_injective (α := ℚ))
    change (Int.castRingHom ℚ) (P.eval X) = (Int.castRingHom ℚ) (Y * Q.eval X)
    rw [map_mul, ← eval_map_apply, ← eval_map_apply]
    exact hpointQ
  have hBpos : 0 < B := by omega
  have hM : 1 ≤ heightBound a B := by
    apply Nat.succ_le_of_lt
    unfold heightBound
    positivity
  exact IntegralRationalGraphBound.abscissa_bound a (heightBound a B) hM P Q hP hQ
    (hQdegree.symm ▸ hqpos) hpc hqc hcopZ X Y hpointZ

theorem bound_le_polynomial (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B) :
    bound a B ≤
      ((3 * ((2 * a + 1) + 1)) ^ (2 * a + 1) +
        (2 * a).factorial * ((3 * ((2 * a + 1) + 1)) ^ (2 * a + 1)) ^ (2 * a)) *
      B ^ (((a + 1) * (2 * a + 1)) * (2 * a)) := by
  let C := (3 * ((2 * a + 1) + 1)) ^ (2 * a + 1)
  let E := (a + 1) * (2 * a + 1)
  have he : E ≤ E * (2 * a) := Nat.le_mul_of_pos_right E (by omega)
  change bound a B ≤ (C + (2 * a).factorial * C ^ (2 * a)) * B ^ (E * (2 * a))
  have hheight : heightBound a B = C * B ^ E := heightBound_eq a B
  have hpow : (C * B ^ E) ^ (2 * a) = C ^ (2 * a) * B ^ (E * (2 * a)) :=
    (mul_pow C (B ^ E) (2 * a)).trans
      (congrArg (fun z ↦ C ^ (2 * a) * z) (pow_mul B E (2 * a)).symm)
  calc
    bound a B = C * B ^ E + (2 * a).factorial * (C ^ (2 * a) * B ^ (E * (2 * a))) := by
      rw [bound, hheight]
      exact congrArg (fun z ↦ C * B ^ E + (2 * a).factorial * z) hpow
    _ ≤ C * B ^ (E * (2 * a)) + (2 * a).factorial * (C ^ (2 * a) * B ^ (E * (2 * a))) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left C (Nat.pow_le_pow_right hB he)) _
    _ = _ := by ring

end PaperP1.GridRationalGraphBound
