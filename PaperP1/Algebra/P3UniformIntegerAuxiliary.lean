module

public import PaperP1.Algebra.P3UniformSmoothAuxiliary
public import PaperP1.Algebra.HomogeneousGradientSection
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # A fixed actual partial derivative restores every original point to the quantitative global auxiliary equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3UniformIntegerAuxiliary

open MvPolynomial Finset
open scoped Classical

theorem uniform_degree (d : ℕ) (hd : 0 < d) (D β : ℝ) (hD : 0 < D) (hβ : 0 < β)
    (hmargin : Real.sqrt (D / (d : ℝ)) < β) (T₀ c₀ T₁ c₁ Kmin : ℕ)
    (hT₀ : 0 < T₀) (hT₁ : 0 < T₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H → ∀ A : ℕ, 0 < A → A ≤ T₁ * H ^ c₁ →
      ∀ P : MvPolynomial (Fin 4) ℤ, P ≠ 0 → P.IsHomogeneous d →
        ¬X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P → Irreducible (map (Int.castRingHom ℚ) P) →
        (∀ m, |P.coeff m| ≤ (A : ℤ)) →
      ∀ z : ℤ, z ≠ 0 → z.natAbs ≤ T₀ * H ^ c₀ →
        (∀ p : ℕ, p.Prime → Kmin ≤ p → ¬(p : ℤ) ∣ z →
          (Fintype.card (P3CanonicalSmoothResidues.Class p P) : ℝ) ≤ D * (p : ℝ) ^ 2) →
      ∀ U : Finset (Fin 4 → ℤ), (∀ v ∈ U, v 3 = 1) →
        (∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ)) → (∀ v ∈ U, eval v P = 0) →
      ∃ (e : ℕ) (G : MvPolynomial (Fin 4) ℤ), d ≤ e ∧ G.IsHomogeneous e ∧
        ¬map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧
        (∀ v ∈ U, eval v G = 0) ∧ (e : ℝ) ≤ C * (H : ℝ) ^ β := by
  obtain ⟨C, hCpos, hC⟩ := P3UniformSmoothAuxiliary.uniform_degree d hd D β hD hβ hmargin
    T₀ c₀ T₁ c₁ Kmin hT₀ hT₁
  refine ⟨C + ((d - 1 : ℕ) : ℝ), by positivity, ?_⟩
  intro H hH A hA hAbound P hP0 hhom hnot hirr hcoef z hz hzbound hclass U hnormal hheight hroots
  obtain ⟨k, _hRhom, _hR0, hRnot⟩ := HomogeneousGradientSection.exists_partial_not_mem
    d hd (map (Int.castRingHom ℚ) P) (hhom.map _) hirr.ne_zero
  rw [pderiv_map] at hRnot
  have hRnotDiv : ¬map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) (pderiv k P) :=
    fun hh ↦ hRnot (Ideal.mem_span_singleton.mpr hh)
  let V := U.filter (fun v ↦ eval v (pderiv k P) ≠ 0)
  obtain ⟨e, G, hed, hGe, hGnot, hGzero, hebound⟩ := hC H hH A hA hAbound P hP0 hhom hnot hcoef
    z hz hzbound hclass V
    (fun v hv ↦ hnormal v (mem_filter.mp hv).1)
    (fun v hv i ↦ hheight v (mem_filter.mp hv).1 i)
    (fun v hv ↦ hroots v (mem_filter.mp hv).1)
    (fun v hv ↦ ⟨k, (mem_filter.mp hv).2⟩)
  refine ⟨(d - 1) + e, pderiv k P * G, by omega, hhom.pderiv.mul hGe, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact hirr.prime.not_dvd_mul hRnotDiv hGnot
  · intro v hv
    rw [map_mul]
    by_cases hR : eval v (pderiv k P) = 0
    · rw [hR, zero_mul]
    · rw [hGzero v (mem_filter.mpr ⟨hv, hR⟩), mul_zero]
  · have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hp := Real.one_le_rpow hHR hβ.le
    have hsmall : ((d - 1 : ℕ) : ℝ) ≤ ((d - 1 : ℕ) : ℝ) * (H : ℝ) ^ β := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (d - 1))
    calc
      (((d - 1) + e : ℕ) : ℝ) = ((d - 1 : ℕ) : ℝ) + (e : ℝ) := Nat.cast_add _ _
      _ ≤ ((d - 1 : ℕ) : ℝ) * (H : ℝ) ^ β + C * (H : ℝ) ^ β := add_le_add hsmall hebound
      _ = _ := by ring

end PaperP1.P3UniformIntegerAuxiliary
