module

public import PaperP1.Diophantine.ImaginaryNormOne
public import PaperP1.Arithmetic.DivisorSubpolynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Signed imaginary norm counts via actual maximal-order ideals

Every principal ideal fibre injects into the actual integral norm-one elements.
This avoids a squarefree reduction and any comparison with a nonmaximal order.
The final count has no coordinate-height restriction and is uniform in D>0.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ImaginaryQuadraticCount

open Finset Filter ImaginaryQuadraticOrder

variable (D : ℕ) [Fact (0 < D)]

def idealOf (m : ℤ) (z : ℤ × ℤ) :
    {I : Ideal (OK D) // I ∣ Ideal.span ({(m : OK D)} : Set (OK D))} := by
  by_cases hz : z.1 ^ 2 + (D : ℤ) * z.2 ^ 2 = m
  · refine ⟨Ideal.span ({alpha D z} : Set (OK D)), ?_⟩
    refine ⟨Ideal.span ({beta D z} : Set (OK D)), ?_⟩
    rw [Ideal.span_singleton_mul_span_singleton, alpha_mul_beta D hz]
  · exact ⟨⊤, by simp⟩

theorem idealOf_eq {m : ℤ} {z : ℤ × ℤ}
    (hz : z.1 ^ 2 + (D : ℤ) * z.2 ^ 2 = m) :
    (idealOf D m z).val = Ideal.span ({alpha D z} : Set (OK D)) := by
  simp only [idealOf, dite_eq_left hz]

theorem same_principal_ideal_gives_norm_one {m : ℤ} (hm : m ≠ 0)
    {z w : ℤ × ℤ}
    (hz : z.1 ^ 2 + (D : ℤ) * z.2 ^ 2 = m)
    (hw : w.1 ^ 2 + (D : ℤ) * w.2 ^ 2 = m)
    (hi : Ideal.span ({alpha D z} : Set (OK D)) =
      Ideal.span ({alpha D w} : Set (OK D))) :
    ∃ u : OK D, alpha D z * u = alpha D w ∧ Algebra.norm ℚ (u : QD D) = 1 := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hi
  refine ⟨(u : OK D), hu, ?_⟩
  have hn := congrArg (fun x : OK D ↦ Algebra.norm ℚ (x : QD D)) hu
  change Algebra.norm ℚ ((alpha D z : QD D) * ((u : OK D) : QD D)) =
    Algebra.norm ℚ (alpha D w : QD D) at hn
  rw [map_mul, norm_alpha, norm_alpha, hz, hw] at hn
  apply mul_left_cancel₀ (show (m : ℚ) ≠ 0 by exact_mod_cast hm)
  simpa only [mul_one] using hn

theorem principal_fibre_card {m : ℤ} (hm : m ≠ 0) (base : ℤ × ℤ)
    (hb : base.1 ^ 2 + (D : ℤ) * base.2 ^ 2 = m) (T : Finset (ℤ × ℤ))
    (hT : ∀ z ∈ T, z.1 ^ 2 + (D : ℤ) * z.2 ^ 2 = m)
    (hi : ∀ z ∈ T, Ideal.span ({alpha D base} : Set (OK D)) =
      Ideal.span ({alpha D z} : Set (OK D))) : T.card ≤ 10 := by
  classical
  let f : {z : ℤ × ℤ // z ∈ T} → OK D := fun z ↦ Classical.choose
    (same_principal_ideal_gives_norm_one D hm hb (hT z z.property) (hi z z.property))
  have hf_spec : ∀ z : {z : ℤ × ℤ // z ∈ T},
      alpha D base * f z = alpha D z ∧ Algebra.norm ℚ (f z : QD D) = 1 := by
    intro z
    exact Classical.choose_spec
      (same_principal_ideal_gives_norm_one D hm hb (hT z z.property) (hi z z.property))
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    apply alpha_injective D
    rw [← (hf_spec z).1, ← (hf_spec w).1, he]
  have hc := ImaginaryNormOne.norm_one_card D (T.attach.image f) (by
    intro u hu
    obtain ⟨z, _hz, rfl⟩ := mem_image.mp hu
    exact (hf_spec z).2)
  simpa only [card_image_of_injective _ hf, card_attach] using hc

theorem norm_card_tau_sq {m : ℤ} (hm : m ≠ 0) (S : Finset (ℤ × ℤ))
    (hS : ∀ z ∈ S, z.1 ^ 2 + (D : ℤ) * z.2 ^ 2 = m) :
    S.card ≤ 10 * m.natAbs.divisors.card ^ 2 := by
  classical
  let IdealDivisor :=
    {I : Ideal (OK D) // I ∣ Ideal.span ({(m : OK D)} : Set (OK D))}
  let : Fintype IdealDivisor := UniqueFactorizationMonoid.fintypeSubtypeDvd
    (Ideal.span ({(m : OK D)} : Set (OK D))) (by
      rw [Ideal.zero_eq_bot]
      exact mt Ideal.span_singleton_eq_bot.mp (Int.cast_ne_zero.mpr hm))
  have hfibre : ∀ i : IdealDivisor, (S.filter (fun z ↦ idealOf D m z = i)).card ≤ 10 := by
    intro i
    by_cases hi : (S.filter (fun z ↦ idealOf D m z = i)).Nonempty
    · obtain ⟨base, hb⟩ := hi
      have hbS := (mem_filter.mp hb).1
      apply principal_fibre_card D hm base (hS base hbS)
      · intro z hz
        exact hS z (mem_filter.mp hz).1
      · intro z hz
        have hsame : idealOf D m base = idealOf D m z :=
          (mem_filter.mp hb).2.trans (mem_filter.mp hz).2.symm
        have hval := congrArg Subtype.val hsame
        simpa only [idealOf_eq D (hS base hbS),
          idealOf_eq D (hS z (mem_filter.mp hz).1)] using hval
    · rw [not_nonempty_iff_eq_empty.mp hi]
      simp
  have hpartition : S.card =
      ∑ i : IdealDivisor, (S.filter (fun z ↦ idealOf D m z = i)).card := by
    simpa using card_eq_sum_card_fiberwise (s := S) (t := univ) (f := idealOf D m)
      (by intro z hz; simp)
  have hcount : Fintype.card IdealDivisor ≤ m.natAbs.divisors.card ^ 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      QuadraticIdealDivisors.quadraticIdealDivisorTauSq (QD D) m hm
  calc
    S.card = _ := hpartition
    _ ≤ ∑ _i : IdealDivisor, 10 := sum_le_sum (fun i _hi ↦ hfibre i)
    _ = 10 * Fintype.card IdealDivisor := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left 10 hcount

omit [Fact (0 < D)] in
theorem count_le_rpow_eventually (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D : ℕ, ∀ m : ℤ, 0 < D → m ≠ 0 → m.natAbs ≤ N ^ K →
      ∀ S : Finset (ℤ × ℤ), (∀ z ∈ S, z.1 ^ 2 + (D : ℤ) * z.2 ^ 2 = m) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nd, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually K (ε / 4)
    (by positivity)
  have ht := ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (10 : ℝ))
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp ht
  refine ⟨max 2 (max Nd Nc), ?_⟩
  intro N hN D m hD hm hmN S hS
  let : Fact (0 < D) := ⟨hD⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdiv := hd N (by omega) m.natAbs hmN
  have hsq : (m.natAbs.divisors.card : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ ((N : ℝ) ^ (ε / 4)) ^ 2 := pow_le_pow_left₀ (by positivity) hdiv _
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; ring
  have hcard : (S.card : ℝ) ≤ 10 * (m.natAbs.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast norm_card_tau_sq D hm S hS
  calc
    (S.card : ℝ) ≤ 10 * (m.natAbs.divisors.card : ℝ) ^ 2 := hcard
    _ ≤ 10 * (N : ℝ) ^ (ε / 2) := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega)) (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring

end PaperP1.ImaginaryQuadraticCount
