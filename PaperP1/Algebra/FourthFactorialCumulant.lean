module

public import PaperP1.Algebra.CenteredCardConvolution

/-! # The exact fourth factorial-cumulant identity with heterogeneous marginals -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.FourthFactorialCumulant

open Finset PaperP1.SubsetPowerSums

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

def total (c : Finset ι → R) (G : Finset ι) (r : ℕ) : R := ∑ I ∈ G.powersetCard r, c I

def weighted (p : ι → R) (c : Finset ι → R) (G : Finset ι) (r : ℕ) : R :=
  ∑ I ∈ G.powersetCard r, c I * ∑ x ∈ I, p x

def pairSquare (p : ι → R) (c : Finset ι → R) (G : Finset ι) : R :=
  ∑ e ∈ G.powersetCard 2, c e * ((∑ x ∈ e, p x) ^ 2 - ∏ x ∈ e, p x)

def fromSubsetData (p : ι → R) (q : Finset ι → R) (G : Finset ι) : R :=
  24 * total q G 4 - 24 * (∑ x ∈ G, p x) * total q G 3 - 12 * total q G 2 ^ 2 +
    24 * (∑ x ∈ G, p x) ^ 2 * total q G 2 - 6 * (∑ x ∈ G, p x) ^ 4

theorem independent_quartic (p : ι → R) (G : Finset ι) :
    24 * elementary p G 4 - 24 * (∑ x ∈ G, p x) * elementary p G 3 -
      12 * elementary p G 2 ^ 2 + 24 * (∑ x ∈ G, p x) ^ 2 * elementary p G 2 -
      6 * (∑ x ∈ G, p x) ^ 4 = -6 * ∑ x ∈ G, (p x) ^ 4 := by
  induction G using Finset.induction_on with
  | empty => simp [elementary, powersetCard_eq_empty.mpr (by norm_num : (∅ : Finset ι).card < 4),
      powersetCard_eq_empty.mpr (by norm_num : (∅ : Finset ι).card < 3),
      powersetCard_eq_empty.mpr (by norm_num : (∅ : Finset ι).card < 2)]
  | @insert x G hx ih =>
    rw [elementary_insert p G x hx 3, elementary_insert p G x hx 2,
      elementary_insert p G x hx 1, elementary_one, sum_insert hx, sum_insert hx]
    calc
      _ = (24 * elementary p G 4 - 24 * (∑ y ∈ G, p y) * elementary p G 3 -
          12 * elementary p G 2 ^ 2 + 24 * (∑ y ∈ G, p y) ^ 2 * elementary p G 2 -
          6 * (∑ y ∈ G, p y) ^ 4) - 6 * (p x) ^ 4 := by ring
      _ = _ := by rw [ih]; ring

theorem pair_deletion (G e : Finset ι) (p : ι → R) (hsub : e ⊆ G) (he : e.card = 2) :
    elementary p (G \ e) 2 = elementary p G 2 - (∑ x ∈ e, p x) * (∑ x ∈ G, p x) +
      (∑ x ∈ e, p x) ^ 2 - ∏ x ∈ e, p x := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  let E := G \ {x, y}
  have hxG : x ∈ G := hsub (mem_insert_self _ _)
  have hyG : y ∈ G := hsub (mem_insert_of_mem (mem_singleton_self _))
  have hxE : x ∉ E := by simp [E]
  have hyE : y ∉ E := by simp [E]
  have hxin : x ∉ insert y E := by simp only [mem_insert, not_or]; exact ⟨hxy, hxE⟩
  have hG : G = insert x (insert y E) := by
    ext z
    constructor
    · intro hz
      by_cases hzx : z = x
      · exact mem_insert.mpr (Or.inl hzx)
      · by_cases hzy : z = y
        · exact mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl hzy)))
        · exact mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr
            (mem_sdiff.mpr ⟨hz, by simp only [mem_insert, mem_singleton]; tauto⟩))))
    · intro hz
      rcases mem_insert.mp hz with rfl | hz
      · exact hxG
      · rcases mem_insert.mp hz with rfl | hz
        · exact hyG
        · exact (mem_sdiff.mp hz).1
  have hsum : (∑ z ∈ G, p z) = p x + p y + ∑ z ∈ E, p z := by
    conv_lhs => rw [hG]
    rw [sum_insert hxin, sum_insert hyE]
    ring
  have he2 : elementary p G 2 = elementary p E 2 +
      (p x + p y) * (∑ z ∈ E, p z) + p x * p y := by
    conv_lhs => rw [hG]
    rw [elementary_insert p (insert y E) x hxin 1, elementary_insert p E y hyE 1,
      elementary_one, elementary_one, sum_insert hyE]
    ring
  rw [sum_pair hxy, prod_pair hxy, hsum, he2]
  change elementary p E 2 = _
  ring

theorem weighted_pair_deletion (G : Finset ι) (p : ι → R) (c : Finset ι → R) :
    (∑ e ∈ G.powersetCard 2, c e * elementary p (G \ e) 2) =
      elementary p G 2 * total c G 2 - (∑ x ∈ G, p x) * weighted p c G 2 + pairSquare p c G := by
  calc
    _ = ∑ e ∈ G.powersetCard 2, (c e * elementary p G 2 -
        (c e * ∑ x ∈ e, p x) * (∑ x ∈ G, p x) + c e * ((∑ x ∈ e, p x) ^ 2 - ∏ x ∈ e, p x)) := by
      apply sum_congr rfl
      intro e he
      rw [pair_deletion G e p (mem_powersetCard.mp he).1 (mem_powersetCard.mp he).2]
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul]
      unfold total weighted pairSquare
      ring

theorem weighted_complement (G : Finset ι) (p : ι → R) (c : Finset ι → R) (r : ℕ) :
    (∑ I ∈ G.powersetCard r, c I * ∑ x ∈ G \ I, p x) =
      (∑ x ∈ G, p x) * total c G r - weighted p c G r := by
  calc
    _ = ∑ I ∈ G.powersetCard r, (c I * (∑ x ∈ G, p x) - c I * ∑ x ∈ I, p x) := by
      apply sum_congr rfl
      intro I hI
      rw [sum_sdiff_eq_sub (mem_powersetCard.mp hI).1]
      ring
    _ = _ := by rw [sum_sub_distrib, ← sum_mul]; unfold total weighted; ring

theorem pairSquare_eq (G : Finset ι) (p : ι → R) (c : Finset ι → R) :
    pairSquare p c G = ∑ e ∈ G.powersetCard 2,
      ((∑ x ∈ e, (p x) ^ 2) + ∏ x ∈ e, p x) * c e := by
  apply sum_congr rfl
  intro e he
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp he).2
  rw [sum_pair hxy, sum_pair hxy, prod_pair hxy]
  ring

theorem exact_formula (G : Finset ι) (p : ι → R) (q c : Finset ι → R)
    (hq : ∀ I ⊆ G, q I = ∑ D ∈ I.powerset, c D * ∏ x ∈ I \ D, p x)
    (h0 : c ∅ = 1) (h1 : ∀ x, c {x} = 0) :
    fromSubsetData p q G = 24 * total c G 4 - 12 * total c G 2 ^ 2 -
      24 * weighted p c G 3 + 24 * pairSquare p c G - 6 * ∑ x ∈ G, (p x) ^ 4 := by
  have h2 := CenteredCardConvolution.two G p q c hq h0 h1
  have h3 := CenteredCardConvolution.three G p q c hq h0 h1
  have h4 := CenteredCardConvolution.four G p q c hq h0 h1
  rw [weighted_complement] at h3
  rw [weighted_pair_deletion, weighted_complement] at h4
  unfold fromSubsetData total
  rw [h2, h3, h4]
  change _ = 24 * total c G 4 - 12 * total c G 2 ^ 2 -
    24 * weighted p c G 3 + 24 * pairSquare p c G - 6 * ∑ x ∈ G, (p x) ^ 4
  calc
    _ = (24 * elementary p G 4 - 24 * (∑ x ∈ G, p x) * elementary p G 3 -
        12 * elementary p G 2 ^ 2 + 24 * (∑ x ∈ G, p x) ^ 2 * elementary p G 2 -
        6 * (∑ x ∈ G, p x) ^ 4) + 24 * total c G 4 - 12 * total c G 2 ^ 2 -
        24 * weighted p c G 3 + 24 * pairSquare p c G := by unfold total; ring
    _ = _ := by rw [independent_quartic]; ring

end PaperP1.FourthFactorialCumulant
