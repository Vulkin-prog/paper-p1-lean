module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Polynomial.Reverse
public import PaperP1.Diophantine.PrimitiveDenominators

/-! # Actual resultant divisibilities from evaluation and homogenized identities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ResultantDivisibility

open Polynomial

variable {R : Type*} [CommRing R]

theorem dvd_resultant_of_dvd_evaluations (f g : R[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hpos : m ≠ 0 ∨ n ≠ 0)
    (x q : R) (hleft : q ∣ f.eval x) (hright : q ∣ g.eval x) :
    q ∣ f.resultant g m n := by
  obtain ⟨p, t, _, _, hbezout⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hpos
  have heval := congrArg (Polynomial.eval x) hbezout
  simp only [eval_add, eval_mul, eval_C] at heval
  rw [← heval]
  exact dvd_add (dvd_mul_of_dvd_left hleft _) (dvd_mul_of_dvd_left hright _)

theorem eval_reflected_homogenize (f : R[X]) (d : ℕ) (hf : f.natDegree ≤ d) (a b : R) :
    MvPolynomial.eval ![a, b] ((f.reflect d).homogenize d) =
      MvPolynomial.eval ![b, a] (f.homogenize d) := by
  refine Polynomial.induction_with_natDegree_le
    (fun F ↦ MvPolynomial.eval ![a, b] ((F.reflect d).homogenize d) =
      MvPolynomial.eval ![b, a] (F.homogenize d)) d ?_ ?_ ?_ f hf
  · simp
  · intro k r _ hkd
    rw [reflect_C_mul_X_pow, revAt_le hkd, homogenize_C_mul, homogenize_C_mul,
      homogenize_X_pow (Nat.sub_le d k), homogenize_X_pow hkd]
    simp only [map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X,
      Matrix.cons_val_one, Matrix.cons_val_zero, Nat.sub_sub_self hkd]
    ring
  · intros
    simp_all [reflect_add, homogenize_add]

theorem homogenized_bezout (f g : R[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hpos : m ≠ 0 ∨ n ≠ 0) :
    ∃ P Q : MvPolynomial (Fin 2) R,
      f.homogenize m * P + g.homogenize n * Q =
        MvPolynomial.C (f.resultant g m n) * MvPolynomial.X 1 ^ (m + n) := by
  obtain ⟨p, t, hp, ht, hbezout⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hpos
  have hpdeg : p.natDegree ≤ n := Polynomial.natDegree_le_of_degree_le hp.le
  have htdeg : t.natDegree ≤ m := Polynomial.natDegree_le_of_degree_le ht.le
  have hm1 := Polynomial.homogenize_mul f p hf hpdeg
  have hm2 : (g * t).homogenize (m + n) = g.homogenize n * t.homogenize m := by
    simpa only [Nat.add_comm] using Polynomial.homogenize_mul g t hg htdeg
  refine ⟨p.homogenize n, t.homogenize m, ?_⟩
  have hhom := congrArg (fun F : R[X] ↦ F.homogenize (m + n)) hbezout
  simpa only [homogenize_add, hm1, hm2, homogenize_C] using hhom

theorem dvd_resultant_coordinate_power (f g : R[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hpos : m ≠ 0 ∨ n ≠ 0)
    (a b q : R)
    (hleft : q ∣ MvPolynomial.eval ![a, b] (f.homogenize m))
    (hright : q ∣ MvPolynomial.eval ![a, b] (g.homogenize n)) :
    q ∣ f.resultant g m n * b ^ (m + n) := by
  obtain ⟨P, Q, hbezout⟩ := homogenized_bezout f g m n hf hg hpos
  have heval := congrArg (MvPolynomial.eval ![a, b]) hbezout
  simp only [map_add, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X,
    Matrix.cons_val_one, Matrix.cons_val_zero] at heval
  rw [← heval]
  exact dvd_add (dvd_mul_of_dvd_left hleft _) (dvd_mul_of_dvd_left hright _)

theorem primitive_resultant_product (f g : ℤ[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (a b q : ℤ)
    (hab : a.natAbs.Coprime b.natAbs)
    (hleft : q ∣ MvPolynomial.eval ![a, b] (f.homogenize d))
    (hright : q ∣ MvPolynomial.eval ![a, b] (g.homogenize d)) :
    q ∣ f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d := by
  have hpos : d ≠ 0 ∨ d ≠ 0 := Or.inl hd.ne'
  have hforward := dvd_resultant_coordinate_power f g d d hf hg hpos a b q hleft hright
  have hfr : (f.reflect d).natDegree ≤ d := Polynomial.natDegree_reflect_le.trans_eq (max_eq_left hf)
  have hgr : (g.reflect d).natDegree ≤ d := Polynomial.natDegree_reflect_le.trans_eq (max_eq_left hg)
  have hlr : q ∣ MvPolynomial.eval ![b, a] ((f.reflect d).homogenize d) := by
    rw [eval_reflected_homogenize f d hf b a]
    exact hleft
  have hrr : q ∣ MvPolynomial.eval ![b, a] ((g.reflect d).homogenize d) := by
    rw [eval_reflected_homogenize g d hg b a]
    exact hright
  have hreverse := dvd_resultant_coordinate_power (f.reflect d) (g.reflect d) d d hfr hgr hpos b a q hlr hrr
  simpa only [mul_comm] using PaperP1.PrimitiveDenominators.dvd_product_int (d + d) (d + d) hab hreverse hforward

theorem padded_resultant_ne_zero_of_left_degree [IsDomain R] (f g : R[X]) (d : ℕ)
    (hd : 0 < d) (hf : f.natDegree = d) (hg : g.natDegree ≤ d) (hcop : IsCoprime f g) :
    f.resultant g d d ≠ 0 := by
  have hf0 : f ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hf
    omega
  have hcoeff : f.coeff d ≠ 0 := by
    rw [← hf]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf0
  have h := Polynomial.resultant_add_right_deg f g d g.natDegree (d - g.natDegree) le_rfl
  rw [Nat.add_sub_of_le hg] at h
  rw [h]
  exact mul_ne_zero (pow_ne_zero _ hcoeff) (by simpa only [hf] using Polynomial.resultant_ne_zero f g hcop)

theorem padded_resultant_ne_zero [IsDomain R] (f g : R[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hfull : f.natDegree = d ∨ g.natDegree = d) (hcop : IsCoprime f g) :
    f.resultant g d d ≠ 0 := by
  rcases hfull with hfull | hfull
  · exact padded_resultant_ne_zero_of_left_degree f g d hd hfull hg hcop
  · rw [Polynomial.resultant_comm f g d d]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (padded_resultant_ne_zero_of_left_degree g f d hd hfull hf hcop.symm)

theorem integer_padded_resultant_ne_zero (f g : ℤ[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hfull : f.natDegree = d ∨ g.natDegree = d)
    (hcop : IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))) :
    f.resultant g d d ≠ 0 := by
  let φ := Int.castRingHom ℚ
  have hdf : (f.map φ).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (by exact Int.cast_injective) f
  have hdg : (g.map φ).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (by exact Int.cast_injective) g
  have hres := padded_resultant_ne_zero (f.map φ) (g.map φ) d hd
    (by simpa only [hdf] using hf) (by simpa only [hdg] using hg)
    (by simpa only [hdf, hdg] using hfull) hcop
  intro hz
  rw [Polynomial.resultant_map_map, hz, map_zero] at hres
  exact hres rfl

theorem finite_denominator_count (f g : ℤ[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hR : f.resultant g d d ≠ 0)
    (hR' : (f.reflect d).resultant (g.reflect d) d d ≠ 0)
    (S : Finset ℤ)
    (hS : ∀ q ∈ S, q ≠ 0 ∧ ∃ a b : ℤ, a.natAbs.Coprime b.natAbs ∧
      q ∣ MvPolynomial.eval ![a, b] (f.homogenize d) ∧
      q ∣ MvPolynomial.eval ![a, b] (g.homogenize d)) :
    S.card ≤ 2 * (f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d).natAbs.divisors.card := by
  have hsub : S ⊆ PaperP1.PrimitiveDenominators.signedDivisors
      (f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d) := by
    intro q hq
    obtain ⟨_, a, b, hab, hleft, hright⟩ := hS q hq
    exact PaperP1.PrimitiveDenominators.mem_signedDivisors (mul_ne_zero hR hR')
      (primitive_resultant_product f g d hd hf hg a b q hab hleft hright)
  exact (Finset.card_le_card hsub).trans (PaperP1.PrimitiveDenominators.signedDivisors_card _)

theorem polynomial_height_denominator_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X], ∀ d : ℕ, 0 < d → f.natDegree ≤ d → g.natDegree ≤ d →
      f.resultant g d d ≠ 0 → (f.reflect d).resultant (g.reflect d) d d ≠ 0 →
      (f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d).natAbs ≤ N ^ K →
      ∀ S : Finset ℤ,
        (∀ q ∈ S, q ≠ 0 ∧ ∃ a b : ℤ, a.natAbs.Coprime b.natAbs ∧
          q ∣ MvPolynomial.eval ![a, b] (f.homogenize d) ∧
          q ∣ MvPolynomial.eval ![a, b] (g.homogenize d)) → (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nd, hNd⟩ := PaperP1.DivisorSubpolynomial.card_divisors_le_rpow_eventually K (ε / 2) (by positivity)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) 2) (ε / 2) (by positivity)
  refine ⟨max 1 (max Nd Nc), ?_⟩
  intro N hN f g d hd hf hg hR hR' hheight S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  have hdiv := hNd N (by omega) _ hheight
  calc
    _ ≤ 2 * ((f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d).natAbs.divisors.card : ℝ) := by
      exact_mod_cast finite_denominator_count f g d hd hf hg hR hR' S hS
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := mul_le_mul hc hdiv (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.ResultantDivisibility
