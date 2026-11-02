module

public import PaperP1.Arithmetic.TwoWitnessFromSupports
public import PaperP1.Arithmetic.FormalWordEncoding
public import Mathlib.Tactic.Choose

/-! # The common curve for an actual bounded independent even word basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonCurveTheorem

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree PaperP1.BivariateHeight
  PaperP1.FormalWordPolynomials PaperP1.BiquadraticWordNorm PaperP1.CurveWordMap

local instance : CommRing ℤ[X][X] := inferInstance
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

structure Certificate (V : Submodule (ZMod 2) Words) where
  polynomial : ℤ[X][X]
  irreducible : Irreducible polynomial
  primitive : polynomial.IsPrimitive
  integerPrimitive : ∀ n : ℤ, C (C n) ∣ polynomial → IsUnit n
  degreeX_pos : 0 < degreeX polynomial
  degreeY_pos : 0 < degreeY polynomial
  image_rank :
    let : Fact (Irreducible polynomial) := ⟨irreducible⟩
    Module.finrank (ZMod 2) (V.map (classMap polynomial degreeX_pos degreeY_pos)) ≤ 1

theorem point_threshold (B q : ℕ) (N : ℝ) (x : ℤ) (hx : N ≤ (x : ℝ))
    (hlarge : ((B : ℝ) + 1) ^ (1000000 * q ^ 2) < N) :
    (B + 1) ^ (1000000 * q ^ 2) < x.natAbs := by
  have habs : (x : ℝ) ≤ (x.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using le_abs_self (x : ℝ)
  have h : (((B + 1) ^ (1000000 * q ^ 2) : ℕ) : ℝ) < (x.natAbs : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    exact hlarge.trans_le (hx.trans habs)
  exact_mod_cast h

theorem integer_parameters {t : ℕ} (ht : 2 ≤ t) (V : Submodule (ZMod 2) Words)
    (b : Module.Basis (Fin t) (ZMod 2) V) (I J : Fin t → Finset ℤ)
    (hwords : ∀ i, (b i : Words) = (encode (I i), encode (J i)))
    (B q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hevenI : ∀ i, Even (I i).card) (hevenJ : ∀ i, Even (J i).card)
    (hcardI : ∀ i, (I i).card ≤ 2 * q) (hcardJ : ∀ i, (J i).card ≤ 2 * q)
    (hI : ∀ i u, u ∈ I i → |u| ≤ (B : ℤ)) (hJ : ∀ i v, v ∈ J i → |v| ≤ (B : ℤ))
    (N : ℝ) (x y : ℤ) (hx : N ≤ (x : ℝ)) (hy : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : ((B : ℝ) + 1) ^ (1000000 * q ^ 2) < N)
    (hsquare : ∀ i, IsSquare ((wordOver ℤ (I i) (J i)).evalEval x y)) :
    ∃ cert : Certificate V, cert.polynomial.evalEval x y = 0 ∧
      totalDegree cert.polynomial ≤ 48 * q ∧ height cert.polynomial ≤ (B + 1) ^ (2472 * q) := by
  classical
  let E := {ij : Fin t × Fin t // ij.1 ≠ ij.2}
  have hexists (e : E) := TwoWitnessFromSupports.exists_norm B q hq hqB
    (I e.val.1) (J e.val.1) (I e.val.2) (J e.val.2)
    (FormalWordEncoding.basis_independent V b I J hwords e.val.1 e.val.2 e.property)
    ⟨hevenI _, hevenJ _, hevenI _, hevenJ _⟩ ⟨hcardI _, hcardJ _, hcardI _, hcardJ _⟩
    (hI _) (hJ _) (hI _) (hJ _) N x y hx hy hx₂ hy₂ hlarge (hsquare _) (hsquare _)
  choose A hprimitive _hA _hAH hne hzero hdx hdy _hdt hH _hcertificate using hexists
  let P : E → ℤ[X][X] := fun e ↦ normPolynomial (I e.val.1) (J e.val.1) (I e.val.2) (J e.val.2) (A e)
  let i₀ : Fin t := ⟨0, by omega⟩
  let i₁ : Fin t := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [i₀, i₁] at hv
    omega
  let e₀ : E := ⟨(i₀, i₁), hi⟩
  obtain ⟨C₀, hC, hprimitiveC, hIntPrimitive, hdiv, hpoint, hCx, hCy, _hCdx, _hCdy, hCtotal, hCH⟩ :=
    CommonCurveFamily.exists_curve P e₀ (hne e₀) B q hq hqB hdx hdy hH x y hzero
      (point_threshold B q N x hx hlarge) (point_threshold B q N y hy hlarge)
  let : Fact (Irreducible C₀) := ⟨hC⟩
  let fullA : Fin t → Fin t → Fin 4 → ℤ[X][X] := fun i j ↦
    if h : i ≠ j then A ⟨(i, j), h⟩ else fun _ ↦ 0
  have hprim (i j : Fin t) (hij : i ≠ j) :
      ∀ D : ℤ[X][X], (∀ χ, D ∣ fullA i j χ) → IsUnit D := by
    simpa [fullA, hij] using hprimitive ⟨(i, j), hij⟩
  have hdivfull (i j : Fin t) (hij : i ≠ j) :
      C₀ ∣ normPolynomial (I i) (J i) (I j) (J j) (fullA i j) := by
    simpa [fullA, hij, P] using hdiv ⟨(i, j), hij⟩
  have hrank := CurveWordMap.image_rank_le_one C₀ hCx hCy V b I J hwords fullA hprim hdivfull
  refine ⟨⟨C₀, hC, hprimitiveC, hIntPrimitive, hCx, hCy, hrank⟩, hpoint, hCtotal, hCH⟩

theorem even_card_floor (E : Finset ℤ) (heven : Even E.card) (q : ℝ) (hq : 0 ≤ q)
    (hcard : (E.card : ℝ) ≤ 2 * q) : E.card ≤ 2 * ⌊q⌋₊ := by
  have he := EvenWordRanks.twice_halfCard E heven
  have hcast : (E.card : ℝ) = 2 * (EvenWordRanks.halfCard E : ℝ) := by exact_mod_cast he
  have hhalf : (EvenWordRanks.halfCard E : ℝ) ≤ q := by linarith
  have hf : EvenWordRanks.halfCard E ≤ ⌊q⌋₊ := (Nat.le_floor_iff hq).mpr hhalf
  rw [he]
  exact Nat.mul_le_mul_left 2 hf

theorem article_13_2 {t : ℕ} (ht : 2 ≤ t) (V : Submodule (ZMod 2) Words)
    (b : Module.Basis (Fin t) (ZMod 2) V) (I J : Fin t → Finset ℤ)
    (hwords : ∀ i, (b i : Words) = (encode (I i), encode (J i)))
    (B q : ℝ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hevenI : ∀ i, Even (I i).card) (hevenJ : ∀ i, Even (J i).card)
    (hcardI : ∀ i, ((I i).card : ℝ) ≤ 2 * q) (hcardJ : ∀ i, ((J i).card : ℝ) ≤ 2 * q)
    (hI : ∀ i u, u ∈ I i → |(u : ℝ)| ≤ B) (hJ : ∀ i v, v ∈ J i → |(v : ℝ)| ≤ B)
    (N : ℝ) (x y : ℤ) (hx : N ≤ (x : ℝ)) (hy : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : (B + 1) ^ (1000000 * q ^ 2) < N)
    (hsquare : ∀ i, IsSquare ((wordOver ℤ (I i) (J i)).evalEval x y)) :
    ∃ cert : Certificate V, cert.polynomial.evalEval x y = 0 ∧
      (totalDegree cert.polynomial : ℝ) ≤ 48 * q ∧
      (height cert.polynomial : ℝ) ≤ (B + 1) ^ (1000000 * q) := by
  have hq₀ : 0 ≤ q := by linarith
  have hB₀ : 0 ≤ B := hq₀.trans hqB
  have hbase : 1 ≤ B + 1 := by linarith
  have hqf : 1 ≤ ⌊q⌋₊ := (Nat.le_floor_iff hq₀).mpr (by simpa using hq)
  have hqfB : ⌊q⌋₊ ≤ ⌊B⌋₊ := (Nat.le_floor_iff hB₀).mpr ((Nat.floor_le hq₀).trans hqB)
  have hbasepow (e : ℕ) : ((⌊B⌋₊ : ℝ) + 1) ^ e ≤ (B + 1) ^ e :=
    pow_le_pow_left₀ (by positivity) (show (⌊B⌋₊ : ℝ) + 1 ≤ B + 1 by linarith [Nat.floor_le hB₀]) e
  have hsq : (⌊q⌋₊ : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hq₀) 2
  have hqpow : (B + 1) ^ (1000000 * ⌊q⌋₊ ^ 2) ≤ (B + 1) ^ (1000000 * q ^ 2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hbase
    push_cast
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  obtain ⟨cert, hpoint, hdegree, hheight⟩ := integer_parameters ht V b I J hwords ⌊B⌋₊ ⌊q⌋₊ hqf hqfB
    hevenI hevenJ (fun i ↦ even_card_floor (I i) (hevenI i) q hq₀ (hcardI i))
    (fun i ↦ even_card_floor (J i) (hevenJ i) q hq₀ (hcardJ i))
    (fun i u hu ↦ TwoWitnessTheorem.floor_offset B hB₀ u (hI i u hu))
    (fun i v hv ↦ TwoWitnessTheorem.floor_offset B hB₀ v (hJ i v hv))
    N x y hx hy hx₂ hy₂ (((hbasepow _).trans hqpow).trans_lt hlarge) hsquare
  refine ⟨cert, hpoint, ?_, ?_⟩
  · have hd : (totalDegree cert.polynomial : ℝ) ≤ 48 * (⌊q⌋₊ : ℝ) := by exact_mod_cast hdegree
    exact hd.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hq₀) (by norm_num))
  · have hh : (height cert.polynomial : ℝ) ≤ ((⌊B⌋₊ : ℝ) + 1) ^ (2472 * ⌊q⌋₊) := by exact_mod_cast hheight
    have he : (B + 1) ^ (2472 * ⌊q⌋₊) ≤ (B + 1) ^ (1000000 * q) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hbase
      push_cast
      calc
        (2472 : ℝ) * (⌊q⌋₊ : ℝ) ≤ 2472 * q := mul_le_mul_of_nonneg_left (Nat.floor_le hq₀) (by norm_num)
        _ ≤ 1000000 * q := mul_le_mul_of_nonneg_right (by norm_num) hq₀
    exact (hh.trans (hbasepow _)).trans he

end PaperP1.CommonCurveTheorem
