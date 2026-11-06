module

public import PaperP1.Algebra.PolynomialEvaluationCongruence
public import PaperP1.Algebra.NormalizedP3SurfaceDeterminant
public import Mathlib.Data.ZMod.Basic

/-! # Canonical finite smooth classes and literal integer representatives of original normalized surface points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CanonicalSmoothResidues

open MvPolynomial Finset
open scoped Classical

def representative {p : ℕ} (r : Fin 3 → Fin p) : Fin 4 → ℤ :=
  Fin.snoc (fun k ↦ ((r k).val : ℤ)) 1

def Good (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (r : Fin 3 → Fin p) : Prop :=
  (p : ℤ) ∣ eval (representative r) P ∧
    ∃ k, ¬(p : ℤ) ∣ eval (representative r) (pderiv k P)

abbrev Class (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) :=
  {r : Fin 3 → Fin p // Good p P r}

def residue (p : ℕ) (hp : 0 < p) (v : Fin 4 → ℤ) : Fin 3 → Fin p :=
  haveI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  fun k ↦ ⟨(v k.castSucc : ZMod p).val, ZMod.val_lt _⟩

def classification (p : ℕ) (hp : 0 < p) (P : MvPolynomial (Fin 4) ℤ)
    (v : Fin 4 → ℤ) : Option (Class p P) :=
  if h : Good p P (residue p hp v) then some ⟨residue p hp v, h⟩ else none

theorem representative_last {p : ℕ} (r : Fin 3 → Fin p) : representative r 3 = 1 :=
  Fin.snoc_last _ _

theorem residue_congruence (p : ℕ) (hp : 0 < p) (v : Fin 4 → ℤ) (hv : v 3 = 1) :
    ∀ k, (p : ℤ) ∣ v k - representative (residue p hp v) k := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  intro k
  cases k using Fin.lastCases with
  | last =>
    have hvlast : v (Fin.last 3) = 1 := hv
    rw [hvlast]
    change (p : ℤ) ∣ 1 - 1
    simp
  | cast k =>
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [representative, Fin.snoc_castSucc]
    change ((v k.castSucc - ((v k.castSucc : ZMod p).val : ℤ) : ℤ) : ZMod p) = 0
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]

theorem good_iff (p : ℕ) (hp : 0 < p) (P : MvPolynomial (Fin 4) ℤ)
    (v : Fin 4 → ℤ) (hv : v 3 = 1) (hroot : eval v P = 0) :
    Good p P (residue p hp v) ↔ ∃ k, ¬(p : ℤ) ∣ eval v (pderiv k P) := by
  have hc := residue_congruence p hp v hv
  have he (F : MvPolynomial (Fin 4) ℤ) :=
    PolynomialEvaluationCongruence.dvd_evaluation_iff (p : ℤ) v
      (representative (residue p hp v)) hc F
  have hP : (p : ℤ) ∣ eval (representative (residue p hp v)) P := by
    apply (he P).mp
    rw [hroot]
    exact dvd_zero _
  simp only [Good, hP, true_and]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, fun hd ↦ hk ((he (pderiv k P)).mp hd)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, fun hd ↦ hk ((he (pderiv k P)).mpr hd)⟩

theorem classification_none_iff (p : ℕ) (hp : 0 < p) (P : MvPolynomial (Fin 4) ℤ)
    (v : Fin 4 → ℤ) (hv : v 3 = 1) (hroot : eval v P = 0) :
    classification p hp P v = none ↔ ∀ k, (p : ℤ) ∣ eval v (pderiv k P) := by
  rw [classification]
  split_ifs with h
  · simp only [false_iff]
    obtain ⟨k, hk⟩ := (good_iff p hp P v hv hroot).mp h
    exact fun hall ↦ hk (hall k)
  · simp only [true_iff]
    have hh : ¬∃ k, ¬(p : ℤ) ∣ eval v (pderiv k P) :=
      fun hgrad ↦ h ((good_iff p hp P v hv hroot).mpr hgrad)
    simpa only [not_exists, not_not] using hh

theorem classification_congruence (p : ℕ) (hp : 0 < p) (P : MvPolynomial (Fin 4) ℤ)
    (v : Fin 4 → ℤ) (hv : v 3 = 1) (c : Class p P)
    (hc : classification p hp P v = some c) :
    ∀ k, (p : ℤ) ∣ v k - representative c.val k := by
  unfold classification at hc
  split_ifs at hc with h
  · have he : (⟨residue p hp v, h⟩ : Class p P) = c := Option.some.inj hc
    subst c
    exact residue_congruence p hp v hv

theorem card_le (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) : Fintype.card (Class p P) ≤ p ^ 3 := by
  calc
    _ ≤ Fintype.card (Fin 3 → Fin p) := Fintype.card_subtype_le _
    _ = _ := by simp

end PaperP1.P3CanonicalSmoothResidues
