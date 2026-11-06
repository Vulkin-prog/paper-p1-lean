module

public import PaperP1.Algebra.HyperellipticTangentDerivation
public import PaperP1.Algebra.HyperellipticOddDegreeNorm
public import PaperP1.Algebra.PolynomialCommonRootFactor
public import PaperP1.Algebra.PrimeCharacteristicDerivationOrder

/-! # Actual tangent vanishings at the two points force twice the root multiplicity in the norm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticNormMultiplicity

open Polynomial HyperellipticPolynomialAlgebra HyperellipticTangentDerivation
open DerivationPowerEvaluation
open scoped QuadraticAlgebra

variable {F : Type*} [Field F]

theorem exists_common_factor (f : F[X]) (z : CurveRing f) (hz : z ≠ 0) (x : F) :
    ∃ (n : ℕ) (u : CurveRing f),
      z = (algebraMap F[X] (CurveRing f) (X - C x)) ^ n * u ∧
      (u.re.eval x ≠ 0 ∨ u.im.eval x ≠ 0) := by
  have hpair : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_cases hre : z.re = 0
    · right
      intro him
      exact hz ((zero_iff f z).mpr ⟨hre, him⟩)
    · exact Or.inl hre
  obtain ⟨n, A, B, hA, hB, hres⟩ := PolynomialCommonRootFactor.exists_factor z.re z.im hpair x
  refine ⟨n, ⟨A, B⟩, ?_, hres⟩
  apply QuadraticAlgebra.ext
  · rw [base_power_mul_re]
    exact hA
  · rw [base_power_mul_im]
    exact hB

theorem norm_power_dvd (p : ℕ) [CharP F p] (hp : p.Prime) (h2 : (2 : F) ≠ 0)
    (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x) (hyn : y ≠ 0)
    (z : CurveRing f) (m : ℕ) (hm : m ≤ p)
    (hplus : ∀ r < m, evaluation f x y hy (iter (tangent f) r z) = 0)
    (hminus : ∀ r < m, evaluation f x (-y) (by simpa only [neg_sq] using hy)
      (iter (tangent f) r z) = 0) :
    (X - C x) ^ (2 * m) ∣ QuadraticAlgebra.norm z := by
  by_cases hz : z = 0
  · rw [hz, QuadraticAlgebra.norm_zero]
    exact dvd_zero _
  obtain ⟨n, u, hfactor, hres⟩ := exists_common_factor f z hz x
  have horder_for (v : F) (hv : v ^ 2 = f.eval x) (hvn : v ≠ 0)
      (hu : evaluation f x v hv u ≠ 0)
      (hvanish : ∀ r < m, evaluation f x v hv (iter (tangent f) r z) = 0) : m ≤ n := by
    have ha : evaluation f x v hv (algebraMap F[X] (CurveRing f) (X - C x)) = 0 := by
      rw [evaluation_base]
      simp
    have hDa : evaluation f x v hv
        (tangent f (algebraMap F[X] (CurveRing f) (X - C x))) ≠ 0 := by
      rw [evaluation_tangent_base]
      simpa only [derivative_sub, derivative_X, derivative_C, sub_zero, eval_one, mul_one] using
        mul_ne_zero h2 hvn
    apply PrimeCharacteristicDerivationOrder.power_order_lower_bound p hp (tangent f)
      (evaluation f x v hv) (algebraMap F[X] (CurveRing f) (X - C x)) u ha hDa hu m n hm
    intro r hr
    rw [← hfactor]
    exact hvanish r hr
  have hmn : m ≤ n := by
    rcases exists_nonzero_sign f x y hy h2 hyn u hres with hpos | hneg
    · exact horder_for y hy hyn hpos hplus
    · exact horder_for (-y) (by simpa only [neg_sq] using hy) (neg_ne_zero.mpr hyn) hneg hminus
  have hnorm : QuadraticAlgebra.norm z = (X - C x) ^ (2 * n) * QuadraticAlgebra.norm u := by
    rw [hfactor, map_mul, map_pow, QuadraticAlgebra.norm_algebraMap, ← pow_mul]
  exact (pow_dvd_pow (X - C x) (Nat.mul_le_mul_left 2 hmn)).trans ⟨QuadraticAlgebra.norm u, hnorm⟩

theorem norm_root_multiplicity (p : ℕ) [CharP F p] (hp : p.Prime) (h2 : (2 : F) ≠ 0)
    (f : F[X]) (hodd : Odd f.natDegree) (x y : F) (hy : y ^ 2 = f.eval x) (hyn : y ≠ 0)
    (z : CurveRing f) (hz : z ≠ 0) (m : ℕ) (hm : m ≤ p)
    (hplus : ∀ r < m, evaluation f x y hy (iter (tangent f) r z) = 0)
    (hminus : ∀ r < m, evaluation f x (-y) (by simpa only [neg_sq] using hy)
      (iter (tangent f) r z) = 0) :
    2 * m ≤ rootMultiplicity x (QuadraticAlgebra.norm z) :=
  (le_rootMultiplicity_iff (HyperellipticOddDegreeNorm.norm_ne_zero f hodd z hz)).mpr
    (norm_power_dvd p hp h2 f x y hy hyn z m hm hplus hminus)

end PaperP1.HyperellipticNormMultiplicity
