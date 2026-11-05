module

public import PaperP1.Algebra.TotalDegreeMonomialFamily

/-! # Concrete initial monomial Wronskians and a controlled exceptional set

All coefficient independence and degree allowances are supplied internally.
The only trajectory data are a genuine nonstationary curve interval.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MonomialWronskianExceptions

open MvPolynomial Finset Set TotalDegreeMonomials TotalDegreeMonomialFamily
  PolynomialTangentTrajectory NonstationaryTangentImage CurvePolynomialWronskianNonvanishing

structure RegularPiece (P : MvPolynomial (Fin 2) ℝ) where
  left : ℝ
  right : ℝ
  ordered : left < right
  path : Fin 2 → ℝ → ℝ
  trajectory : Trajectory P path (Ioo left right)
  equation : ∀ t ∈ Ioo left right, eval (position path t) P = 0
  nonstationary : ∀ t ∈ Ioo left right, ∃ i, velocity P (position path t) i ≠ 0

def initialFamily (k n : ℕ) (hn : n ≤ Fintype.card (Index k)) : Fin n → MvPolynomial (Fin 2) ℝ :=
  fun i ↦ family k (Fin.castLE hn i)

def exceptionalPoints (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) : Set (Fin 2 → ℝ) :=
  {z | eval z P = 0 ∧ ∃ j : Fin (Fintype.card (Index k)),
    eval z (PolynomialTangentWronskian.wronskian P (j.val + 1)
      (initialFamily k (j.val + 1) (Nat.succ_le_of_lt j.isLt))) = 0}

theorem initial_degree (k n : ℕ) (hn : n ≤ Fintype.card (Index k)) :
    ∀ i, (initialFamily k n hn i).totalDegree ≤ k :=
  fun i ↦ basis_degree (enumeration k (Fin.castLE hn i))

theorem initial_combination_ne_zero (k n : ℕ) (hn : n ≤ Fintype.card (Index k))
    (c : Fin n → ℝ) (hc : c ≠ 0) : polynomialCombination (initialFamily k n hn) c ≠ 0 :=
  combination_ne_zero k n (fun i ↦ enumeration k (Fin.castLE hn i))
    ((enumeration k).injective.comp (Fin.castLE_injective hn)) c hc

theorem initial_not_dvd (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : k < P.totalDegree) (r : RegularPiece P)
    (n : ℕ) (hn : n ≤ Fintype.card (Index k)) :
    ¬P ∣ PolynomialTangentWronskian.wronskian P n (initialFamily k n hn) :=
  wronskian_not_dvd P hP n k hk _ (initial_degree k n hn) (initial_combination_ne_zero k n hn)
    r.path r.left r.right r.ordered r.trajectory r.equation r.nonstationary

theorem initial_zero_card (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : k < P.totalDegree) (r : RegularPiece P)
    (n : ℕ) (hn : n ≤ Fintype.card (Index k)) (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, eval z P = 0 ∧
      eval z (PolynomialTangentWronskian.wronskian P n (initialFamily k n hn)) = 0) :
    S.card ≤ 2 * P.totalDegree ^ 2 * (k + 1) ^ 4 := by
  have hc := exceptional_card P hP n k hk _ (initial_degree k n hn) (initial_combination_ne_zero k n hn)
    r.path r.left r.right r.ordered r.trajectory r.equation r.nonstationary S hS
  have ht : n * (n - 1) / 2 ≤ n ^ 2 := by
    calc
      _ ≤ n * (n - 1) := Nat.div_le_self _ _
      _ ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le n 1)
      _ = _ := (pow_two n).symm
  have hnm : n ≤ (k + 1) ^ 2 := hn.trans (index_card_le k)
  have hm : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hnp : n + 1 ≤ 2 * (k + 1) ^ 2 := by omega
  have hprod : n * (n + 1) ≤ 2 * (k + 1) ^ 4 := by
    calc
      _ ≤ (k + 1) ^ 2 * (2 * (k + 1) ^ 2) := Nat.mul_le_mul hnm hnp
      _ = _ := by ring
  calc
    _ ≤ P.totalDegree * (n * k + (n * (n - 1) / 2) * P.totalDegree) := hc
    _ ≤ P.totalDegree * (n * P.totalDegree + n ^ 2 * P.totalDegree) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hk.le) (Nat.mul_le_mul_right _ ht))
    _ = P.totalDegree ^ 2 * (n * (n + 1)) := by ring
    _ ≤ P.totalDegree ^ 2 * (2 * (k + 1) ^ 4) := Nat.mul_le_mul_left _ hprod
    _ = _ := by ring

theorem exceptional_population_card (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : k < P.totalDegree) (r : RegularPiece P) (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, z ∈ exceptionalPoints P k) :
    S.card ≤ 2 * P.totalDegree ^ 2 * (k + 1) ^ 6 := by
  classical
  let T (j : Fin (Fintype.card (Index k))) := S.filter (fun z ↦
    eval z (PolynomialTangentWronskian.wronskian P (j.val + 1)
      (initialFamily k (j.val + 1) (Nat.succ_le_of_lt j.isLt))) = 0)
  have hsub : S ⊆ Finset.univ.biUnion T := by
    intro z hz
    obtain ⟨j, hj⟩ := (hS z hz).2
    exact mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨hz, hj⟩⟩
  have hc (j : Fin (Fintype.card (Index k))) : (T j).card ≤ 2 * P.totalDegree ^ 2 * (k + 1) ^ 4 := by
    apply initial_zero_card P hP k hk r (j.val + 1) (Nat.succ_le_of_lt j.isLt) (T j)
    intro z hz
    exact ⟨(hS z (mem_filter.mp hz).1).1, (mem_filter.mp hz).2⟩
  calc
    _ ≤ (Finset.univ.biUnion T).card := card_le_card hsub
    _ ≤ ∑ j, (T j).card := card_biUnion_le
    _ ≤ ∑ _j : Fin (Fintype.card (Index k)), 2 * P.totalDegree ^ 2 * (k + 1) ^ 4 :=
      sum_le_sum (fun j _hj ↦ hc j)
    _ = Fintype.card (Index k) * (2 * P.totalDegree ^ 2 * (k + 1) ^ 4) := by simp
    _ ≤ (k + 1) ^ 2 * (2 * P.totalDegree ^ 2 * (k + 1) ^ 4) := Nat.mul_le_mul_right _ (index_card_le k)
    _ = _ := by ring

theorem exists_exceptional_finset (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : k < P.totalDegree) (r : RegularPiece P) :
    ∃ E : Finset (Fin 2 → ℝ), (∀ z, z ∈ E ↔ z ∈ exceptionalPoints P k) ∧
      E.card ≤ 2 * P.totalDegree ^ 2 * (k + 1) ^ 6 := by
  classical
  have hf : (exceptionalPoints P k).Finite := by
    by_contra hbad
    have hInf : (exceptionalPoints P k).Infinite := hbad
    obtain ⟨S, hS, hcard⟩ := hInf.exists_subset_card_eq (2 * P.totalDegree ^ 2 * (k + 1) ^ 6 + 1)
    have hc := exceptional_population_card P hP k hk r S (fun z hz ↦ hS hz)
    omega
  refine ⟨hf.toFinset, fun z ↦ hf.mem_toFinset, ?_⟩
  exact exceptional_population_card P hP k hk r hf.toFinset (fun z hz ↦ hf.mem_toFinset.mp hz)

end PaperP1.MonomialWronskianExceptions
