module

public import PaperP1.Algebra.MonicP3LastChart
public import Mathlib.Algebra.CharP.Algebra
public import PaperP1.Arithmetic.P3UniversalGoodReduction
public import PaperP1.Algebra.FieldExtensionPolynomialIrreducibility

/-! # The original scalar-multiple integer model has a height-controlled monic irreducible full-degree reduction

The normalization coefficient is the literal integer coefficient of the
pure primitive-variable monomial. Its size is bounded by the original
coefficient height. Combined with the actual Noether certificate it gives
a uniform polynomial-height certificate for all affine polynomial properties.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IntegerProjectedModelNormalization
open Polynomial MvPolynomial PaperP1.MonicP3LastChart

def topCoefficient (Q : MvPolynomial (Fin 4) ℤ) (d : ℕ) : ℤ :=
  Q.coeff ((0 : Fin 3 →₀ ℕ).cons d)

theorem model_coefficients (d : ℕ) (Q : MvPolynomial (Fin 4) ℤ) (q : MvPolynomial (Fin 4) ℚ)
    (a : ℚ) (ha : a ≠ 0) (hq : q.IsHomogeneous d) (hm : (finSuccEquiv ℚ 3 q).Monic)
    (hmodel : MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q) :
    (topCoefficient Q d : ℚ) = a ∧ topCoefficient Q d ≠ 0 ∧
    (finSuccEquiv ℤ 3 Q).coeff d = MvPolynomial.C (topCoefficient Q d) ∧
    ∀ i : ℕ, d < i → (finSuccEquiv ℤ 3 Q).coeff i = 0 := by
  let φ : MvPolynomial (Fin 3) ℤ →+* MvPolynomial (Fin 3) ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let T := finSuccEquiv ℤ 3 Q
  have hmap : T.map φ = Polynomial.C (MvPolynomial.C a) * finSuccEquiv ℚ 3 q := by
    have hh := finSucc_map (Int.castRingHom ℚ) 3 Q
    rw [hmodel, map_mul, finSucc_C] at hh
    exact hh.symm
  have hcoef (i : ℕ) : φ (T.coeff i) = MvPolynomial.C a * (finSuccEquiv ℚ 3 q).coeff i := by
    have hh := congrArg (fun P : (MvPolynomial (Fin 3) ℚ)[X] ↦ P.coeff i) hmap
    simpa only [Polynomial.coeff_map, Polynomial.coeff_C_mul] using hh
  have hdegree : (finSuccEquiv ℚ 3 q).natDegree = d :=
    PaperP1.HomogeneousLastChartIrreducible.outer_degree 3 q hq hm
  have hqd : (finSuccEquiv ℚ 3 q).coeff d = 1 := by
    rw [← hdegree]
    exact hm.coeff_natDegree
  have htop := hcoef d
  rw [hqd, mul_one] at htop
  have hb : (T.coeff d).coeff 0 = topCoefficient Q d := finSuccEquiv_coeff_coeff (0 : Fin 3 →₀ ℕ) Q d
  have hcast : (topCoefficient Q d : ℚ) = a := by
    change (Int.castRingHom ℚ) (topCoefficient Q d) = a
    have hh := congrArg (fun B : MvPolynomial (Fin 3) ℚ ↦ B.coeff 0) htop
    change (MvPolynomial.map (Int.castRingHom ℚ) (T.coeff d)).coeff 0 = (MvPolynomial.C a).coeff 0 at hh
    simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_C, ite_true, hb] using hh
  refine ⟨hcast, ?_, ?_, ?_⟩
  · intro hz
    apply ha
    rw [← hcast, hz, Int.cast_zero]
  · apply MvPolynomial.map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
    change φ (T.coeff d) = MvPolynomial.map (Int.castRingHom ℚ) (MvPolynomial.C (topCoefficient Q d))
    rw [htop, MvPolynomial.map_C]
    exact congrArg MvPolynomial.C hcast.symm
  · intro i hi
    have hh := hcoef i
    have hz : (finSuccEquiv ℚ 3 q).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [hdegree])
    rw [hz, mul_zero] at hh
    exact MvPolynomial.map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
      (hh.trans (map_zero φ).symm)

theorem topCoefficient_height (Q : MvPolynomial (Fin 4) ℤ) (d A : ℕ)
    (hcoef : ∀ m, |Q.coeff m| ≤ (A : ℤ)) : (topCoefficient Q d).natAbs ≤ A := by
  have hh : ((topCoefficient Q d).natAbs : ℤ) ≤ (A : ℤ) := by
    simpa only [Int.natCast_natAbs, topCoefficient] using hcoef ((0 : Fin 3 →₀ ℕ).cons d)
  exact_mod_cast hh

def normalized (F : Type*) [Field F] (Q : MvPolynomial (Fin 4) ℤ) (b : ℤ) : MvPolynomial (Fin 4) F :=
  MvPolynomial.C (b : F)⁻¹ * MvPolynomial.map (Int.castRingHom F) Q

theorem normalized_monic_degree (F : Type*) [Field F] (Q : MvPolynomial (Fin 4) ℤ) (d : ℕ) (b : ℤ)
    (hb : (b : F) ≠ 0) (htop : (finSuccEquiv ℤ 3 Q).coeff d = MvPolynomial.C b)
    (habove : ∀ i : ℕ, d < i → (finSuccEquiv ℤ 3 Q).coeff i = 0) :
    (finSuccEquiv F 3 (normalized F Q b)).Monic ∧
      (finSuccEquiv F 3 (normalized F Q b)).natDegree = d := by
  let T := finSuccEquiv F 3 (normalized F Q b)
  have hmap : T = Polynomial.C (MvPolynomial.C (b : F)⁻¹) *
      (finSuccEquiv ℤ 3 Q).map (MvPolynomial.map (Int.castRingHom F)) := by
    dsimp only [T]
    rw [normalized, map_mul, finSucc_C, finSucc_map]
  have hcoef (i : ℕ) : T.coeff i = MvPolynomial.C (b : F)⁻¹ *
      MvPolynomial.map (Int.castRingHom F) ((finSuccEquiv ℤ 3 Q).coeff i) := by
    rw [hmap, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  have ht : T.coeff d = 1 := by
    rw [hcoef, htop, MvPolynomial.map_C, ← MvPolynomial.C_mul]
    change MvPolynomial.C ((b : F)⁻¹ * (b : F)) = 1
    rw [inv_mul_cancel₀ hb, MvPolynomial.C_1]
  have hle : T.natDegree ≤ d := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [hcoef, habove i hi, map_zero, mul_zero]
  exact ⟨Polynomial.monic_of_degree_le d (Polynomial.degree_le_of_natDegree_le hle) ht,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [ht]; exact one_ne_zero)⟩

theorem normalized_homogeneous (F : Type*) [Field F] (Q : MvPolynomial (Fin 4) ℤ) (b : ℤ)
    (d : ℕ) (hQ : Q.IsHomogeneous d) : (normalized F Q b).IsHomogeneous d := by
  simpa only [normalized, Nat.zero_add] using (MvPolynomial.isHomogeneous_C (R := F) (Fin 4) ((b : F)⁻¹)).mul (hQ.map (Int.castRingHom F))

theorem normalized_irreducible (F : Type*) [Field F] (Q : MvPolynomial (Fin 4) ℤ) (b : ℤ)
    (hb : (b : F) ≠ 0) (hQ : Irreducible (MvPolynomial.map (Int.castRingHom F) Q)) :
    Irreducible (normalized F Q b) := by
  have hu : IsUnit (MvPolynomial.C (b : F)⁻¹ : MvPolynomial (Fin 4) F) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hb)).map MvPolynomial.C
  exact ((prime_isUnit_mul hu).mpr hQ.prime).irreducible

theorem model_monic_reduction (F : Type*) [Field F] (d : ℕ)
    (Q : MvPolynomial (Fin 4) ℤ) (q : MvPolynomial (Fin 4) ℚ)
    (a : ℚ) (ha : a ≠ 0) (hq : q.IsHomogeneous d) (hm : (finSuccEquiv ℚ 3 q).Monic)
    (hmodel : MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q)
    (hb : (topCoefficient Q d : F) ≠ 0) :
    (finSuccEquiv F 3 (normalized F Q (topCoefficient Q d))).Monic ∧
      (finSuccEquiv F 3 (normalized F Q (topCoefficient Q d))).natDegree = d := by
  have hh := model_coefficients d Q q a ha hq hm hmodel
  exact normalized_monic_degree F Q d (topCoefficient Q d) hb hh.2.2.1 hh.2.2.2

theorem affine_model_properties (F : Type*) [Field F] (d : ℕ) (hd : 0 < d)
    (Q : MvPolynomial (Fin 4) ℤ) (hQ : Q.IsHomogeneous d) (q : MvPolynomial (Fin 4) ℚ)
    (a : ℚ) (ha : a ≠ 0) (hq : q.IsHomogeneous d) (hm : (finSuccEquiv ℚ 3 q).Monic)
    (hmodel : MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q)
    (hb : (topCoefficient Q d : F) ≠ 0) (hirr : Irreducible (MvPolynomial.map (Int.castRingHom F) Q)) :
    let P := PaperP1.MonicP3LastChart.chart (normalized F Q (topCoefficient Q d))
    P.Monic ∧ P.natDegree = d ∧ Irreducible P ∧ ∀ i, (P.coeff i).totalDegree ≤ d := by
  have hhom := normalized_homogeneous F Q (topCoefficient Q d) d hQ
  have hmono := (model_monic_reduction F d Q q a ha hq hm hmodel hb).1
  have hi := normalized_irreducible F Q (topCoefficient Q d) hb hirr
  exact ⟨PaperP1.MonicP3LastChart.monic _ hmono, PaperP1.MonicP3LastChart.natDegree _ hhom hmono,
    PaperP1.MonicP3LastChart.irreducible _ hi hd hhom hmono,
    PaperP1.MonicP3LastChart.coefficient_degree _ hhom⟩

theorem good_prime_affine_properties (d : ℕ) (hd : 0 < d)
    (Q : MvPolynomial (Fin 4) ℤ) (hQ : Q.IsHomogeneous d) (q : MvPolynomial (Fin 4) ℚ)
    (a : ℚ) (ha : a ≠ 0) (hq : q.IsHomogeneous d) (hm : (finSuccEquiv ℚ 3 q).Monic)
    (hmodel : MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q)
    (z : ℤ) (hz : PaperP1.P3UniversalGoodReduction.Certificate Q z)
    (p : ℕ) (hp : p.Prime) (hnotz : ¬ (p : ℤ) ∣ z) (hnotb : ¬ (p : ℤ) ∣ topCoefficient Q d) :
    letI : Fact p.Prime := ⟨hp⟩
    let P := PaperP1.MonicP3LastChart.chart (normalized (ZMod p) Q (topCoefficient Q d))
    P.Monic ∧ P.natDegree = d ∧ Irreducible P ∧ ∀ i, (P.coeff i).totalDegree ≤ d := by
  let : Fact p.Prime := ⟨hp⟩
  have hb : (topCoefficient Q d : ZMod p) ≠ 0 := fun hh ↦
    hnotb ((ZMod.intCast_zmod_eq_zero_iff_dvd (topCoefficient Q d) p).mp hh)
  have hg := PaperP1.P3UniversalGoodReduction.geometric_reduction Q z hz p hp hnotz
  have hi := PaperP1.FieldExtensionPolynomialIrreducibility.irreducible_of_map
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) (MvPolynomial.map (Int.castRingHom (ZMod p)) Q) hg
  exact affine_model_properties (ZMod p) d hd Q hQ q a ha hq hm hmodel hb hi

theorem bounded_model_certificate (d : ℕ) (hd : 0 < d) :
    ∃ T N : ℕ, 0 < T ∧ ∀ A : ℕ, 0 < A → ∀ Q : MvPolynomial (Fin 4) ℤ,
      Q.IsHomogeneous d →
      Irreducible (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) Q)) →
      (∀ m, |Q.coeff m| ≤ (A : ℤ)) →
      ∀ (q : MvPolynomial (Fin 4) ℚ) (a : ℚ), a ≠ 0 → q.IsHomogeneous d →
      (finSuccEquiv ℚ 3 q).Monic →
      MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q →
      ∃ B : ℤ, B ≠ 0 ∧ B.natAbs ≤ T * A ^ N ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬ (p : ℤ) ∣ B →
          letI : Fact p.Prime := ⟨hp⟩
          let P := PaperP1.MonicP3LastChart.chart (normalized (ZMod p) Q (topCoefficient Q d))
          P.Monic ∧ P.natDegree = d ∧ Irreducible P ∧ ∀ i, (P.coeff i).totalDegree ≤ d := by
  obtain ⟨T, N, hT, hTN⟩ := PaperP1.P3UniversalGoodReduction.bounded_certificate d
  refine ⟨T, N+1, hT, ?_⟩
  intro A hA Q hQ hgeom hcoef q a ha hq hm hmodel
  obtain ⟨z, hz0, hzbound, hz⟩ := hTN A hA Q hQ hgeom hcoef
  have hb0 := (model_coefficients d Q q a ha hq hm hmodel).2.1
  let B := topCoefficient Q d * z
  have hbound : B.natAbs ≤ T * A ^ (N+1) := by
    change (topCoefficient Q d * z).natAbs ≤ _
    rw [Int.natAbs_mul]
    calc
      (topCoefficient Q d).natAbs * z.natAbs ≤ A * (T * A ^ N) :=
        Nat.mul_le_mul (topCoefficient_height Q d A hcoef) hzbound
      _ = T * A ^ (N+1) := by rw [pow_succ]; ring
  refine ⟨B, mul_ne_zero hb0 hz0, hbound, ?_⟩
  intro p hp hnot
  have hnotb : ¬ (p : ℤ) ∣ topCoefficient Q d := fun hh ↦ hnot (dvd_mul_of_dvd_left hh z)
  have hnotz : ¬ (p : ℤ) ∣ z := fun hh ↦ hnot (dvd_mul_of_dvd_right hh (topCoefficient Q d))
  exact good_prime_affine_properties d hd Q hQ q a ha hq hm hmodel z hz p hp hnotz hnotb

end PaperP1.IntegerProjectedModelNormalization
