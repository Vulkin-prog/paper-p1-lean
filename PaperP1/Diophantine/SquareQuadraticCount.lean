module

public import PaperP1.Diophantine.PolynomialPellCount

@[expose] public section

/-!
# The square-coefficient branch of companion T1.2

Positive solutions of A u² - C v² = e inject into the positive divisors of
|Ae| when AC is square. The finite bound is independent of the solution height.
-/

namespace PaperP1.QuadraticCount

open Finset PellInput

theorem square_factor_identity
    {A C r : ℕ} {e : ℤ} {s : ℤ × ℤ}
    (hr : A * C = r * r) (heq : pellEquation A C e s) :
    ((A : ℤ) * s.1 - (r : ℤ) * s.2) *
        ((A : ℤ) * s.1 + (r : ℤ) * s.2) = (A : ℤ) * e := by
  have hrz : (A : ℤ) * C = (r : ℤ) * r := by exact_mod_cast hr
  dsimp [pellEquation] at heq
  nlinarith [hrz]

theorem square_positive_count_le_divisors
    {A C : ℕ} {e : ℤ} (hA : 0 < A) (hC : 0 < C) (he : e ≠ 0)
    (hsquare : IsSquare ((A * C : ℕ) : ℚ))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ z ∈ s, pellEquation A C e z ∧ 0 < z.1 ∧ 0 < z.2) :
    s.card ≤ ((A : ℤ) * e).natAbs.divisors.card := by
  classical
  obtain ⟨r, hr⟩ := Rat.isSquare_natCast_iff.mp hsquare
  have hrpos : 0 < r := by
    have hAC := Nat.mul_pos hA hC
    nlinarith [hr]
  let f : ℤ × ℤ → ℕ := fun z => ((A : ℤ) * z.1 + (r : ℤ) * z.2).natAbs
  have hplus : ∀ z ∈ s, 0 < (A : ℤ) * z.1 + (r : ℤ) * z.2 := by
    intro z hz
    exact add_pos (mul_pos (by exact_mod_cast hA) (hs z hz).2.1)
      (mul_pos (by exact_mod_cast hrpos) (hs z hz).2.2)
  have hfactor : ∀ z ∈ s,
      ((A : ℤ) * z.1 - (r : ℤ) * z.2) *
        ((A : ℤ) * z.1 + (r : ℤ) * z.2) = (A : ℤ) * e := by
    intro z hz
    exact square_factor_identity hr (hs z hz).1
  have hne : (A : ℤ) * e ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hA.ne') he
  have himage : s.image f ⊆ ((A : ℤ) * e).natAbs.divisors := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
    apply Nat.mem_divisors.mpr
    refine ⟨?_, Int.natAbs_ne_zero.mpr hne⟩
    have hdvd : (A : ℤ) * z.1 + (r : ℤ) * z.2 ∣ (A : ℤ) * e :=
      ⟨(A : ℤ) * z.1 - (r : ℤ) * z.2, by
        simpa only [mul_comm] using (hfactor z hz).symm⟩
    exact Int.natAbs_dvd_natAbs.mpr hdvd
  have hinj : Set.InjOn f (s : Set (ℤ × ℤ)) := by
    intro z hz w hw heq
    have hplusEq :
        (A : ℤ) * z.1 + (r : ℤ) * z.2 =
          (A : ℤ) * w.1 + (r : ℤ) * w.2 := by
      have hcast := congrArg (fun n : ℕ => (n : ℤ)) heq
      simpa only [f, Int.natAbs_of_nonneg (hplus z hz).le,
        Int.natAbs_of_nonneg (hplus w hw).le] using hcast
    have hminusEq :
        (A : ℤ) * z.1 - (r : ℤ) * z.2 =
          (A : ℤ) * w.1 - (r : ℤ) * w.2 := by
      apply mul_right_cancel₀ (ne_of_gt (hplus w hw))
      rw [← hplusEq, hfactor z hz, hplusEq, hfactor w hw]
    have hfirst : (A : ℤ) * z.1 = (A : ℤ) * w.1 := by linarith
    have hsecond : (r : ℤ) * z.2 = (r : ℤ) * w.2 := by linarith
    exact Prod.ext
      (mul_left_cancel₀ (by exact_mod_cast hA.ne') hfirst)
      (mul_left_cancel₀ (by exact_mod_cast hrpos.ne') hsecond)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card himage

end PaperP1.QuadraticCount

