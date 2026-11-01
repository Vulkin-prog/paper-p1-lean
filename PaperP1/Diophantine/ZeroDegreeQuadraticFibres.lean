module

public import PaperP1.Diophantine.PrimitiveHomogeneousZeros
public import PaperP1.Diophantine.BidegreeOneFibreCount
public import PaperP1.Diophantine.UniformQuadraticCount
public import PaperP1.Asymptotics.UniformReal

/-! # The degree-zero-in-(d,e) auxiliary case of the determinant argument -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ZeroDegreeQuadraticFibres

open Finset PaperP1.PrimitiveDirections PaperP1.BidegreeOneFibreCount

structure Valid (c₁ c₂ : ℕ) (h : ℤ) (H : ℕ) (s : Point) : Prop where
  first_pos : ∀ i, 0 < s.1 i
  second_pos : ∀ i, 0 < s.2 i
  first_height : ∀ i, (s.1 i).natAbs ≤ H
  second_height : ∀ i, (s.2 i).natAbs ≤ H
  primitive : (s.2 0).natAbs.Coprime (s.2 1).natAbs
  equation : (c₂ : ℤ) * s.1 1 ^ 2 * s.2 0 - (c₁ : ℤ) * s.1 0 ^ 2 * s.2 1 = h

def encode (s : Point) : ℤ × ℤ := (s.1 1, s.1 0)

theorem encode_injective_on_fibre (S : Finset Point) (t : Pair) :
    Set.InjOn encode (↑(S.filter fun s ↦ s.2 = t) : Set Point) := by
  intro x hx y hy hxy
  have hx2 := (mem_filter.mp hx).2
  have hy2 := (mem_filter.mp hy).2
  apply Prod.ext
  · funext i
    fin_cases i
    · exact congrArg Prod.snd hxy
    · exact congrArg Prod.fst hxy
  · exact hx2.trans hy2.symm

theorem quadratic_fibre_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ c₁ c₂ H : ℕ, ∀ h : ℤ,
      0 < c₁ → 0 < c₂ → h ≠ 0 → c₁ ≤ N ^ K → c₂ ≤ N ^ K →
      H ≤ N ^ K → h.natAbs ≤ N ^ K → ∀ S : Finset Point,
        (∀ s ∈ S, Valid c₁ c₂ h H s) → ∀ t ∈ S.image Prod.snd,
          ((S.filter fun s ↦ s.2 = t).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nq, hNq⟩ := PaperP1.UniformQuadraticCount.positive_count_le_rpow_eventually (2 * K) ε hε
  refine ⟨max 1 Nq, ?_⟩
  intro N hN c₁ c₂ H h hc₁ hc₂ hh h₁ h₂ hH hhN S hS t ht
  obtain ⟨s₀, hs₀, rfl⟩ := mem_image.mp ht
  have hv := hS s₀ hs₀
  let A := c₂ * (s₀.2 0).natAbs
  let C := c₁ * (s₀.2 1).natAbs
  have hA : 0 < A := Nat.mul_pos hc₂ (Int.natAbs_pos.mpr (hv.second_pos 0).ne')
  have hC : 0 < C := Nat.mul_pos hc₁ (Int.natAbs_pos.mpr (hv.second_pos 1).ne')
  have hApow : A ≤ N ^ (2 * K) := by
    calc
      _ ≤ N ^ K * N ^ K := Nat.mul_le_mul h₂ ((hv.second_height 0).trans hH)
      _ = _ := by rw [← pow_add, ← two_mul]
  have hCpow : C ≤ N ^ (2 * K) := by
    calc
      _ ≤ N ^ K * N ^ K := Nat.mul_le_mul h₁ ((hv.second_height 1).trans hH)
      _ = _ := by rw [← pow_add, ← two_mul]
  have hpow : N ^ K ≤ N ^ (2 * K) := Nat.pow_le_pow_right (by omega) (by omega)
  have hAcast : (A : ℤ) = (c₂ : ℤ) * s₀.2 0 := by
    dsimp [A]
    rw [Int.natCast_natAbs, abs_of_pos (hv.second_pos 0)]
  have hCcast : (C : ℤ) = (c₁ : ℤ) * s₀.2 1 := by
    dsimp [C]
    rw [Int.natCast_natAbs, abs_of_pos (hv.second_pos 1)]
  classical
  have hcard := card_image_iff.mpr (encode_injective_on_fibre S s₀.2)
  rw [← hcard]
  apply hNq N (by omega) A C H h hA hC hh hApow hCpow (hH.trans hpow) (hhN.trans hpow)
  intro z hz
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hz
  have hsf := (mem_filter.mp hs).1
  have hst := (mem_filter.mp hs).2
  have hvalid := hS s hsf
  refine ⟨⟨?_, hvalid.first_height 1, hvalid.first_height 0⟩,
    hvalid.first_pos 1, hvalid.first_pos 0⟩
  unfold PaperP1.PellInput.pellEquation encode
  rw [hAcast, hCcast]
  have heq := hvalid.equation
  rw [hst] at heq
  linear_combination heq

theorem auxiliary_zero_count (k K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ c₁ c₂ H : ℕ, ∀ h : ℤ,
      0 < c₁ → 0 < c₂ → h ≠ 0 → c₁ ≤ N ^ K → c₂ ≤ N ^ K →
      H ≤ N ^ K → h.natAbs ≤ N ^ K →
        ∀ F : MvPolynomial (Fin 2) ℤ, F.IsHomogeneous k → F ≠ 0 →
          ∀ S : Finset Point, (∀ s ∈ S, Valid c₁ c₂ h H s) →
            (∀ s ∈ S, MvPolynomial.eval s.2 F = 0) → (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nq, hNq⟩ := quadratic_fibre_count K (ε / 2) (by positivity)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) (2 * (k + 1)))
    (ε / 2) (by positivity)
  refine ⟨max 1 (max Nq Nc), ?_⟩
  intro N hN c₁ c₂ H h hc₁ hc₂ hh h₁ h₂ hH hhN F hF hF0 S hS hzero
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprojection : (S.image Prod.snd).card ≤ 2 * (k + 1) := by
    apply PaperP1.PrimitiveHomogeneousZeros.primitive_card F hF hF0
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
      exact (hS s hs).primitive
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
      exact hzero s hs
  have hconstant : (2 * (k + 1) : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  calc
    (S.card : ℝ) = ∑ t ∈ S.image Prod.snd, ((S.filter fun s ↦ s.2 = t).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_image Prod.snd S
    _ ≤ ∑ _t ∈ S.image Prod.snd, (N : ℝ) ^ (ε / 2) := by
      apply sum_le_sum
      intro t ht
      exact hNq N (by omega) c₁ c₂ H h hc₁ hc₂ hh h₁ h₂ hH hhN S hS t ht
    _ = ((S.image Prod.snd).card : ℝ) * (N : ℝ) ^ (ε / 2) := by simp
    _ ≤ (2 * (k + 1) : ℝ) * (N : ℝ) ^ (ε / 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn.le _)
      exact_mod_cast hprojection
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ ε := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.ZeroDegreeQuadraticFibres
