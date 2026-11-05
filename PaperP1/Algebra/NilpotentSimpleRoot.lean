module

public import PaperP1.Algebra.PowerSeriesSimpleRoot

/-! # Simple-root existence and uniqueness modulo a nilpotent ideal

Nilpotence makes the completion condition a finite eventual-constancy fact.
The existing nonmonic lifting theorem then applies without a new Newton proof.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NilpotentSimpleRoot

open Polynomial

variable {R : Type*} [CommRing R]

theorem complete_of_pow_eq_bot (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥) : IsAdicComplete I R where
  haus' := by
    intro x hx
    have h := hx N
    simpa only [hN, Submodule.bot_smul, SModEq.bot] using h
  prec' := by
    intro f hf
    refine ⟨f N, ?_⟩
    intro n
    by_cases hn : n ≤ N
    · exact hf hn
    · have he : f N = f n := by
        have h := hf (show N ≤ n by omega)
        simpa only [hN, Submodule.bot_smul, SModEq.bot] using h
      rw [he]

theorem exists_root (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥) (f : R[X]) (a₀ : R)
    (hroot : f.eval a₀ ∈ I) (hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.eval a = 0 ∧ a - a₀ ∈ I := by
  let : IsAdicComplete I R := complete_of_pow_eq_bot I N hN
  exact PaperP1.PowerSeriesSimpleRoot.adic_simple_root I f a₀ hroot hder

theorem unique_root (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥) (f : R[X]) (a b : R)
    (ha : f.eval a = 0) (hb : f.eval b = 0) (hab : a - b ∈ I)
    (hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval b))) : a = b := by
  let : IsAdicComplete I R := complete_of_pow_eq_bot I N hN
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
  obtain ⟨c, hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add f b (a - b)
  have he : b + (a - b) = a := by ring
  rw [he, ha, hb, add_zero] at hc
  let u := c * (a - b) + f.derivative.eval b
  have hz : Ideal.Quotient.mk I (a - b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hab
  have huq : IsUnit (Ideal.Quotient.mk I u) := by
    simpa only [u, map_add, map_mul, hz, mul_zero, zero_add] using hder
  have hu : IsUnit u := IsUnit.of_map (Ideal.Quotient.mk I) u huq
  have hp : (a - b) * u = 0 := by
    calc
      (a - b) * u = c * (a - b) ^ 2 + f.derivative.eval b * (a - b) := by dsimp [u]; ring
      _ = 0 := hc
  apply sub_eq_zero.mp
  exact hu.mul_left_eq_zero.mp hp

end PaperP1.NilpotentSimpleRoot
