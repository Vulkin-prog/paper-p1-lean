module

public import PaperP1.Arithmetic.TwoWitnessPolynomial
public import PaperP1.Arithmetic.WordNormCertificate

/-! # Companion T9.5, including the actual degree-four field norm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoWitnessTheorem

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree
  PaperP1.FormalWordPolynomials PaperP1.BiquadraticWordNorm
open scoped symmDiff

theorem integer_radius {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (I J K L : Finset ℤ) (hind : Independent I J K L)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (N : ℝ) (x y : ℤ) (hx : N ≤ (x : ℝ)) (hy : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : ((B : ℝ) + 1) ^ (1200 * q) < N)
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y)) :
    ∃ Q : Fin 4 → ℤ[X][X], ∃ R : ℤ[X][X],
      (∀ E : ℤ[X][X], (∀ χ, E ∣ Q χ) → IsUnit E) ∧ (∃ χ, Q χ ≠ 0) ∧
      (∀ χ, BivariateHeight.height (Q χ) ≤ (B + 1) ^ (275 * q)) ∧
      R = normPolynomial I J K L Q ∧ R ≠ 0 ∧ R.evalEval x y = 0 ∧
      degreeX R ≤ 12 * q ∧ degreeY R ≤ 12 * q ∧ totalDegree R ≤ 24 * q ∧
      BivariateHeight.height R ≤ (B + 1) ^ (1200 * q) ∧
      WordNormCertificate.Certificate I J K L Q R := by
  obtain ⟨Q, R, hp, hQ, hheight, hR, hne, hpoint, hdx, hdy, hdt, hRH⟩ :=
    TwoWitnessPolynomial.exists_polynomial B hq hqB hr hs I J K L hind hI hJ hK hL
      hcx hcy N x y hx hy hx₂ hy₂ hlarge h₁ h₂
  refine ⟨Q, R, hp, hQ, hheight, hR, hne, hpoint, hdx, hdy, hdt, hRH, ?_⟩
  rw [hR]
  exact WordNormCertificate.certificate I J K L hind Q hQ

theorem floor_offset (B : ℝ) (hB : 0 ≤ B) (i : ℤ) (hi : |(i : ℝ)| ≤ B) :
    |i| ≤ (⌊B⌋₊ : ℤ) := by
  rw [Int.abs_eq_natAbs]
  have hcast : (i.natAbs : ℝ) = |(i : ℝ)| := by
    cases i with
    | ofNat n => simp
    | negSucc n =>
      simp
      rw [abs_of_nonpos (by have := Nat.cast_nonneg n (α := ℝ); linarith)]
      ring
  have hn : i.natAbs ≤ ⌊B⌋₊ := (Nat.le_floor_iff hB).mpr (by rwa [hcast])
  exact_mod_cast hn

theorem real_radius {q : ℕ} {r s : Fin 3 → ℕ} (B : ℝ) (hq : 1 ≤ q) (hqB : (q : ℝ) ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (I J K L : Finset ℤ) (hind : Independent I J K L)
    (hI : ∀ i ∈ I, |(i : ℝ)| ≤ B) (hJ : ∀ j ∈ J, |(j : ℝ)| ≤ B)
    (hK : ∀ i ∈ K, |(i : ℝ)| ≤ B) (hL : ∀ j ∈ L, |(j : ℝ)| ≤ B)
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (N : ℝ) (x y : ℤ) (hx : N ≤ (x : ℝ)) (hy : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : (B + 1) ^ (1200 * q) < N)
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y)) :
    ∃ Q : Fin 4 → ℤ[X][X], ∃ R : ℤ[X][X],
      (∀ E : ℤ[X][X], (∀ χ, E ∣ Q χ) → IsUnit E) ∧ (∃ χ, Q χ ≠ 0) ∧
      (∀ χ, (BivariateHeight.height (Q χ) : ℝ) ≤ (B + 1) ^ (275 * q)) ∧
      R = normPolynomial I J K L Q ∧ R ≠ 0 ∧ R.evalEval x y = 0 ∧
      degreeX R ≤ 12 * q ∧ degreeY R ≤ 12 * q ∧ totalDegree R ≤ 24 * q ∧
      (BivariateHeight.height R : ℝ) ≤ (B + 1) ^ (1200 * q) ∧
      WordNormCertificate.Certificate I J K L Q R := by
  have hB : 0 ≤ B := (Nat.cast_nonneg q).trans hqB
  have hqfloor : q ≤ ⌊B⌋₊ := (Nat.le_floor_iff hB).mpr hqB
  have hpow (e : ℕ) : ((⌊B⌋₊ : ℝ) + 1) ^ e ≤ (B + 1) ^ e :=
    pow_le_pow_left₀ (by positivity) (show (⌊B⌋₊ : ℝ) + 1 ≤ B + 1 by linarith [Nat.floor_le hB]) e
  obtain ⟨Q, R, hp, hQ, hheight, hR, hne, hpoint, hdx, hdy, hdt, hRH, hcert⟩ :=
    integer_radius ⌊B⌋₊ hq hqfloor hr hs I J K L hind
      (fun i hi ↦ floor_offset B hB i (hI i hi))
      (fun j hj ↦ floor_offset B hB j (hJ j hj))
      (fun i hi ↦ floor_offset B hB i (hK i hi))
      (fun j hj ↦ floor_offset B hB j (hL j hj))
      hcx hcy N x y hx hy hx₂ hy₂ ((hpow _).trans_lt hlarge) h₁ h₂
  refine ⟨Q, R, hp, hQ, ?_, hR, hne, hpoint, hdx, hdy, hdt, ?_, hcert⟩
  · intro χ
    exact (by exact_mod_cast hheight χ : (BivariateHeight.height (Q χ) : ℝ) ≤
      ((⌊B⌋₊ : ℝ) + 1) ^ (275 * q)).trans (hpow _)
  · exact (by exact_mod_cast hRH : (BivariateHeight.height R : ℝ) ≤
      ((⌊B⌋₊ : ℝ) + 1) ^ (1200 * q)).trans (hpow _)

theorem companion_T9_5 {r s : Fin 3 → ℕ} (B q : ℝ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, (r i : ℝ) ≤ q) (hs : ∀ i, (s i : ℝ) ≤ q)
    (I J K L : Finset ℤ) (hind : Independent I J K L)
    (hI : ∀ i ∈ I, |(i : ℝ)| ≤ B) (hJ : ∀ j ∈ J, |(j : ℝ)| ≤ B)
    (hK : ∀ i ∈ K, |(i : ℝ)| ≤ B) (hL : ∀ j ∈ L, |(j : ℝ)| ≤ B)
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (N : ℝ) (x y : ℤ) (hx : N ≤ (x : ℝ)) (hy : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : (B + 1) ^ (1200 * q) < N)
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y)) :
    ∃ Q : Fin 4 → ℤ[X][X], ∃ R : ℤ[X][X],
      (∀ E : ℤ[X][X], (∀ χ, E ∣ Q χ) → IsUnit E) ∧ (∃ χ, Q χ ≠ 0) ∧
      (∀ χ, (BivariateHeight.height (Q χ) : ℝ) ≤ (B + 1) ^ (275 * q)) ∧
      R = normPolynomial I J K L Q ∧ R ≠ 0 ∧ R.evalEval x y = 0 ∧
      degreeX R ≤ 12 * ⌊q⌋₊ ∧ degreeY R ≤ 12 * ⌊q⌋₊ ∧ totalDegree R ≤ 24 * ⌊q⌋₊ ∧
      (BivariateHeight.height R : ℝ) ≤ (B + 1) ^ (1200 * q) ∧
      WordNormCertificate.Certificate I J K L Q R := by
  have hq₀ : 0 ≤ q := by linarith
  have hB : 1 ≤ B + 1 := by linarith
  have hqf : 1 ≤ ⌊q⌋₊ := (Nat.le_floor_iff hq₀).mpr (by simpa using hq)
  have hpow (e : ℕ) : (B + 1) ^ (e * ⌊q⌋₊) ≤ (B + 1) ^ ((e : ℝ) * q) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hB
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hq₀) (Nat.cast_nonneg e)
  obtain ⟨Q, R, hp, hQ, hheight, hR, hne, hpoint, hdx, hdy, hdt, hRH, hcert⟩ :=
    real_radius B hqf ((Nat.floor_le hq₀).trans hqB)
      (fun i ↦ (Nat.le_floor_iff hq₀).mpr (hr i)) (fun i ↦ (Nat.le_floor_iff hq₀).mpr (hs i))
      I J K L hind hI hJ hK hL hcx hcy N x y hx hy hx₂ hy₂
      ((hpow 1200).trans_lt hlarge) h₁ h₂
  exact ⟨Q, R, hp, hQ, fun χ ↦ (hheight χ).trans (hpow 275), hR, hne, hpoint,
    hdx, hdy, hdt, hRH.trans (hpow 1200), hcert⟩

end PaperP1.TwoWitnessTheorem
