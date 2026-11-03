module

public import PaperP1.Algebra.SquareLineMatching
public import PaperP1.Arithmetic.AffineGridAlignment

/-! # Functional squares from disjoint split words force actual host alignment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareLineFamilyAlignment

open Polynomial

theorem of_two_squares (B : ℕ) (X Y : ℤ) (α β : ℚ)
    (c₀ c₁ : ℚ) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (I₀ I₁ J₀ J₁ : Finset ℤ) (hdisj : Disjoint I₀ I₁)
    (hne₀ : I₀.Nonempty) (hne₁ : I₁.Nonempty)
    (hI₀ : ∀ i ∈ I₀, i.natAbs ≤ B) (hI₁ : ∀ i ∈ I₁, i.natAbs ≤ B)
    (hJ₀ : ∀ j ∈ J₀, j.natAbs ≤ B) (hJ₁ : ∀ j ∈ J₁, j.natAbs ≤ B)
    (hsq₀ : IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X])
      (SquareLineMatching.lineRestriction c₀ I₀ J₀ α β)))
    (hsq₁ : IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X])
      (SquareLineMatching.lineRestriction c₁ I₁ J₁ α β)))
    (hX : (B : ℤ) < X) (hY : (B : ℤ) < Y)
    (hhost : (Y : ℚ) = α * (X : ℚ) + β) : AffineGridAlignment.Aligned B X Y := by
  obtain ⟨i₀, hi₀⟩ := hne₀
  obtain ⟨i₁, hi₁⟩ := hne₁
  obtain ⟨j₀, hj₀, hline₀⟩ :=
    SquareLineMatching.function_matches_offset c₀ hc₀ I₀ J₀ α β hsq₀ i₀ hi₀
  obtain ⟨j₁, hj₁, hline₁⟩ :=
    SquareLineMatching.function_matches_offset c₁ hc₁ I₁ J₁ α β hsq₁ i₁ hi₁
  have hbound (i : ℤ) (hi : i.natAbs ≤ B) : |-i| ≤ (B : ℤ) := by
    simpa only [abs_neg, Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).mpr hi
  apply AffineGridAlignment.of_affine_grid B X Y (-i₀, -j₀) (-i₁, -j₁) hX hY
    ⟨hbound i₀ (hI₀ i₀ hi₀), hbound j₀ (hJ₀ j₀ hj₀)⟩
    ⟨hbound i₁ (hI₁ i₁ hi₁), hbound j₁ (hJ₁ j₁ hj₁)⟩
  · intro heq
    have hi : i₀ = i₁ := neg_injective (congrArg Prod.fst heq)
    exact Finset.disjoint_left.mp hdisj hi₀ (hi.symm ▸ hi₁)
  · simpa only [Int.cast_neg] using (show -(j₀ : ℚ) = α * -(i₀ : ℚ) + β by linarith)
  · simpa only [Int.cast_neg] using (show -(j₁ : ℚ) = α * -(i₁ : ℚ) + β by linarith)
  · exact hhost

theorem of_family {n : ℕ} (hn : 2 ≤ n) (B : ℕ) (X Y : ℤ) (α β : ℚ)
    (c : Fin n → ℚ) (hc : ∀ ν, c ν ≠ 0) (I J : Fin n → Finset ℤ)
    (hdisj : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ))
    (hne : ∀ ν, (I ν).Nonempty)
    (hI : ∀ ν i, i ∈ I ν → i.natAbs ≤ B)
    (hJ : ∀ ν j, j ∈ J ν → j.natAbs ≤ B)
    (hsq : ∀ ν, IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X])
      (SquareLineMatching.lineRestriction (c ν) (I ν) (J ν) α β)))
    (hX : (B : ℤ) < X) (hY : (B : ℤ) < Y)
    (hhost : (Y : ℚ) = α * (X : ℚ) + β) : AffineGridAlignment.Aligned B X Y := by
  let ν₀ : Fin n := ⟨0, by omega⟩
  let ν₁ : Fin n := ⟨1, by omega⟩
  exact of_two_squares B X Y α β (c ν₀) (c ν₁) (hc ν₀) (hc ν₁)
    (I ν₀) (I ν₁) (J ν₀) (J ν₁) (hdisj (by simp [ν₀, ν₁]))
    (hne ν₀) (hne ν₁) (hI ν₀) (hI ν₁) (hJ ν₀) (hJ ν₁)
    (hsq ν₀) (hsq ν₁) hX hY hhost

theorem vertical_not_square (B : ℕ) (X : ℤ) (c : ℚ) (hc : c ≠ 0)
    (I J : Finset ℤ) (hneJ : J.Nonempty)
    (hI : ∀ i ∈ I, i.natAbs ≤ B) (hX : (B : ℤ) < X) :
    ¬ IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X])
      (C c * C ((FormalWordPolynomials.linearOver ℚ I).eval (X : ℚ)) *
        FormalWordPolynomials.linearOver ℚ J)) := by
  intro hsq
  have heq : SquareLineMatching.lineRestriction c J I 0 (X : ℚ) =
      C c * C ((FormalWordPolynomials.linearOver ℚ I).eval (X : ℚ)) *
        FormalWordPolynomials.linearOver ℚ J := by
    simp only [SquareLineMatching.lineRestriction, C_0, zero_mul, zero_add, comp_C]
    ring
  rw [← heq] at hsq
  obtain ⟨j, hj⟩ := hneJ
  obtain ⟨i, hi, he⟩ := SquareLineMatching.function_matches_offset c hc J I 0 (X : ℚ) hsq j hj
  have hb : |i| ≤ (B : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).mpr (hI i hi)
  have hp : 0 < X + i := by have := neg_abs_le i; omega
  have hpQ : (0 : ℚ) < (X : ℚ) + (i : ℚ) := by exact_mod_cast hp
  simp only [zero_mul] at he
  linarith

end PaperP1.SquareLineFamilyAlignment
