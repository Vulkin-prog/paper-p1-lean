module

public import PaperP1.Geometry.ProjectiveCurveData
public import PaperP1.Arithmetic.NormalizedIntegerPoints
public import PaperP1.Arithmetic.UniformAffineCurvePointCount

/-! # One explicit uniform curve-count property for every actual projective coordinate chart

`UniformBound` is an explicit proposition, not an axiom. It records the translation
from Pila's uniform affine curve theorem to actual prime ideals, linear Hilbert
polynomials and normalized coordinate charts. The treatment of curves integral
over Q without geometric integrality is included in this precise property.
Sources: Pila, Astérisque 228 (1995), Theorem A,
https://www.numdam.org/item/AST_1995__228__183_0.pdf ; and Salberger,
https://arxiv.org/pdf/2311.05561v1 , Lemma 3, for the integral projective curve
formulation in P3. Every consequence here takes the property as an argument.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformNormalizedCurvePointCount

open PaperP1.ProjectiveCurveData PaperP1.NormalizedIntegerPoints

def UniformBound (nmax M : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧
    ∀ (σ : Type) [Finite σ], Nat.card σ ≤ nmax → ∀ Γ : Curve σ, Γ.degree ≤ (M : ℚ) →
    ∀ (z : σ) (H : ℕ), 1 ≤ H →
      ((points Γ.ideal z H).card : ℝ) ≤ A * (H : ℝ) ^ (1 / (Γ.degree : ℝ) + δ)

theorem above_degree_bound (nmax M : ℕ) (e : ℚ) (he : 0 < e) (hPila : UniformBound nmax M)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (σ : Type) [Finite σ], Nat.card σ ≤ nmax →
      ∀ Γ : Curve σ, Γ.degree ≤ (M : ℚ) → e ≤ Γ.degree → ∀ (z : σ) (H : ℕ), 1 ≤ H →
      ((points Γ.ideal z H).card : ℝ) ≤ A * (H : ℝ) ^ (1 / (e : ℝ) + δ) := by
  obtain ⟨A, hA, hcount⟩ := hPila δ hδ
  refine ⟨A, hA, ?_⟩
  intro σ _ hdim Γ hM hdegree z H hH
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hdegreeR : (e : ℝ) ≤ Γ.degree := by exact_mod_cast hdegree
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  exact (hcount σ hdim Γ hM z H hH).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hHreal
      (add_le_add (one_div_le_one_div_of_le heR hdegreeR) (le_refl δ))) hA.le)

theorem ordinary_points (k : ℕ) (Q : Ideal (MvPolynomial (Fin 3 ⊕ Fin k) ℚ)) (H : ℕ) :
    points Q (Sum.inl (2 : Fin 3)) H = OrdinaryIntegerPoints.curvePoints Q H := by
  classical
  ext v
  rw [mem_points, OrdinaryIntegerPoints.mem_curvePoints]
  rfl

theorem ordinary_specialization (kmax M : ℕ) (hPila : UniformBound (kmax + 3) M) :
    UniformAffineCurvePointCount.UniformBound kmax M := by
  intro δ hδ
  obtain ⟨A, hA, hcount⟩ := hPila δ hδ
  refine ⟨A, hA, ?_⟩
  intro k hk c D I J Γ hM H hH
  let Δ : Curve (Fin 3 ⊕ Fin k) :=
    ⟨Γ.ideal, Γ.prime, Γ.homogeneous, (Γ.degree : ℚ), by exact_mod_cast Γ.degree_pos,
      Γ.constant, Γ.hilbert⟩
  have hdim : Nat.card (Fin 3 ⊕ Fin k) ≤ kmax + 3 := by
    rw [Nat.card_sum, Nat.card_fin, Nat.card_fin]
    omega
  have hdegree : Δ.degree ≤ (M : ℚ) := by change (Γ.degree : ℚ) ≤ (M : ℚ); exact_mod_cast hM
  have hbound := hcount (Fin 3 ⊕ Fin k) hdim Δ hdegree (Sum.inl 2) H hH
  simpa only [Δ, ordinary_points, Rat.cast_natCast] using hbound

end PaperP1.UniformNormalizedCurvePointCount
