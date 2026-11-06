module

public import PaperP1.Arithmetic.HyperellipticOddDegreePointEstimate

/-! # Unconditional uniform relative cancellation for every bounded odd-degree polynomial

Compare the literal quadratic-curve point count with its nonsquare scalar twist.
Both point-count estimates are already internal proofs. This gives a weak
relative error, with a threshold before all primes and all coefficients.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.HyperellipticOddDegreeCharacterEstimate
open Polynomial Finset
open PaperP1.HyperellipticFiniteFieldPoints
open scoped Classical

theorem twisted_sum {F : Type*} [Field F] [Fintype F] (f : F[X]) (u : F) :
    (∑ x : F, quadraticChar F ((C u * f).eval x)) =
      quadraticChar F u * ∑ x : F, quadraticChar F (f.eval x) := by
  simp only [eval_mul, eval_C, map_mul, Finset.mul_sum]

theorem uniform_absolute (D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ f : (ZMod p)[X], Odd f.natDegree → f.natDegree ≤ D →
        |((∑ x : ZMod p, quadraticChar (ZMod p) (f.eval x) : ℤ) : ℝ)| ≤ η * p := by
  classical
  obtain ⟨K, hK⟩ := PaperP1.HyperellipticOddDegreePointEstimate.uniform_degree_cap D η hη
  refine ⟨max 3 K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro f hodd hD
  have hdec : (fun a b : ZMod p ↦ Classical.propDecidable (a = b)) = ZMod.decidableEq p := Subsingleton.elim _ _
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  obtain ⟨u, hu⟩ := quadraticChar_exists_neg_one hchar
  have hun : u ≠ 0 := by
    intro hz
    rw [hz, quadraticChar_zero] at hu
    norm_num at hu
  have htwdeg : (C u * f).natDegree = f.natDegree := natDegree_C_mul hun
  have htwodd : Odd (C u * f).natDegree := htwdeg.symm ▸ hodd
  have htwD : (C u * f).natDegree ≤ D := htwdeg.symm ▸ hD
  have hfcount := hK p hp (by omega) f hodd hD
  have htcount := hK p hp (by omega) (C u * f) htwodd htwD
  have hcount (P : (ZMod p)[X]) : ((points P).card : ℝ) = (p : ℝ) +
      ((∑ x : ZMod p, quadraticChar (ZMod p) (P.eval x) : ℤ) : ℝ) := by
    have hh := character_cardinality hchar P
    rw [ZMod.card, hdec] at hh
    exact_mod_cast hh
  have htw : (∑ x : ZMod p, quadraticChar (ZMod p) ((C u * f).eval x)) =
      -(∑ x : ZMod p, quadraticChar (ZMod p) (f.eval x)) := by
    have ht := twisted_sum (F := ZMod p) f u
    rw [hdec, hu, neg_one_mul] at ht
    exact ht
  rw [hcount f] at hfcount
  rw [hcount (C u * f), htw, Int.cast_neg] at htcount
  apply abs_le.mpr
  constructor <;> nlinarith only [hfcount, htcount]
end PaperP1.HyperellipticOddDegreeCharacterEstimate
