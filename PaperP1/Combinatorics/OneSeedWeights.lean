module

public import PaperP1.Combinatorics.DistinguishedSeedWeights

/-! # All multiplicities for one inserted or erased distinguished centre

No disjointness between the distinguished centre and the original family is
assumed. The finite bound retains both possible reconstruction maps.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneSeedWeights

open Finset

variable {κ : Type*} [DecidableEq κ]

theorem fixed_centre (a : κ) (T F : Finset (Finset κ)) (m : ℝ) (hm : 0 ≤ m)
    (hF : ∀ I ∈ F, insert a I ∈ T ∨ I.erase a ∈ T) :
    (∑ I ∈ F, m ^ (I.card + 1)) ≤
      ∑ J ∈ T, ((if a ∈ J then (1 : ℝ) else 0) + 2 * m + m ^ 2) * m ^ J.card := by
  classical
  let E := T.image (fun J ↦ J.erase a)
  let A := T.image (insert a)
  have hsub : F ⊆ T ∪ E ∪ A := by
    intro I hI
    rcases hF I hI with hi | he
    · by_cases ha : a ∈ I
      · exact mem_union_left _ (mem_union_left _ (by simpa only [insert_eq_of_mem ha] using hi))
      · apply mem_union_left
        apply mem_union_right
        exact mem_image.mpr ⟨insert a I, hi, erase_insert ha⟩
    · by_cases ha : a ∈ I
      · exact mem_union_right _ (mem_image.mpr ⟨I.erase a, he, insert_erase ha⟩)
      · exact mem_union_left _ (mem_union_left _ (by simpa only [erase_eq_of_notMem ha] using he))
  have hs := sum_le_sum_of_subset_of_nonneg hsub
    (fun I _ _ ↦ pow_nonneg hm (I.card + 1))
  have hu₁ := GraphStarWeights.sum_union_le_nonneg T E (fun I : Finset κ ↦ m ^ (I.card + 1))
    (fun _ ↦ pow_nonneg hm _)
  have hu₂ := GraphStarWeights.sum_union_le_nonneg (T ∪ E) A (fun I : Finset κ ↦ m ^ (I.card + 1))
    (fun _ ↦ pow_nonneg hm _)
  have hE : (∑ I ∈ E, m ^ (I.card + 1)) ≤ ∑ J ∈ T, m ^ ((J.erase a).card + 1) :=
    sum_image_le_of_nonneg (fun _ _ ↦ pow_nonneg hm _)
  have hA : (∑ I ∈ A, m ^ (I.card + 1)) ≤ ∑ J ∈ T, m ^ ((insert a J).card + 1) :=
    sum_image_le_of_nonneg (fun _ _ ↦ pow_nonneg hm _)
  have ht : (∑ I ∈ F, m ^ (I.card + 1)) ≤
      (∑ J ∈ T, m ^ (J.card + 1)) + (∑ J ∈ T, m ^ ((J.erase a).card + 1)) +
        ∑ J ∈ T, m ^ ((insert a J).card + 1) := by
    linarith only [hs, hu₁, hu₂, hE, hA]
  apply ht.trans
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro J _
  by_cases ha : a ∈ J
  · have hcard : (J.erase a).card + 1 = J.card := card_erase_add_one ha
    rw [ite_eq_left ha, hcard, insert_eq_of_mem ha, pow_succ]
    nlinarith only [mul_nonneg (sq_nonneg m) (pow_nonneg hm J.card)]
  · rw [ite_eq_right ha, erase_eq_of_notMem ha, card_insert_of_notMem ha, pow_succ, pow_succ]
    ring_nf
    exact le_rfl

theorem finite_constant_bound (G : Finset κ) (T : Finset (Finset κ)) (Families : κ → Finset (Finset κ))
    (m : ℝ) (hm : 0 ≤ m) (hT : ∀ J ∈ T, J ⊆ G)
    (hF : ∀ a ∈ G, ∀ I ∈ Families a, insert a I ∈ T ∨ I.erase a ∈ T) :
    (∑ a ∈ G, ∑ I ∈ Families a, m ^ (I.card + 1)) ≤
      (1 + (G.card : ℝ) * (2 * m + m ^ 2)) * ∑ J ∈ T, (2 * m) ^ J.card := by
  classical
  have hfirst := sum_le_sum (fun a ha ↦ fixed_centre a T (Families a) m hm (hF a ha))
  apply hfirst.trans
  rw [sum_comm]
  have hsum (J : Finset κ) (hJ : J ∈ T) :
      (∑ a ∈ G, ((if a ∈ J then (1 : ℝ) else 0) + 2 * m + m ^ 2) * m ^ J.card) ≤
        (1 + (G.card : ℝ) * (2 * m + m ^ 2)) * (2 * m) ^ J.card := by
    have hfilter : G.filter (fun a ↦ a ∈ J) = J := by
      ext a
      simp only [mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hT J hJ h, h⟩⟩
    have hind : (∑ a ∈ G, if a ∈ J then (1 : ℝ) else 0) = J.card := by
      rw [← sum_filter, hfilter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
    have hcard : (J.card : ℝ) ≤ 2 ^ J.card := by
      exact_mod_cast ((Nat.lt_two_pow_self (n := J.card)).le)
    have hpow : m ^ J.card ≤ (2 * m) ^ J.card :=
      pow_le_pow_left₀ hm (by linarith only [hm]) J.card
    have hcount := mul_le_mul_of_nonneg_right hcard (pow_nonneg hm J.card)
    have htail := mul_le_mul_of_nonneg_left hpow
      (by positivity : (0 : ℝ) ≤ (G.card : ℝ) * (2 * m + m ^ 2))
    simp_rw [add_mul]
    rw [sum_add_distrib, sum_add_distrib, ← sum_mul, hind]
    simp only [sum_const, nsmul_eq_mul]
    rw [mul_pow] at htail ⊢
    nlinarith only [hcount, htail]
  calc
    _ ≤ ∑ J ∈ T, (1 + (G.card : ℝ) * (2 * m + m ^ 2)) * (2 * m) ^ J.card := sum_le_sum hsum
    _ = _ := (mul_sum _ _ _).symm

theorem heterogeneous_bound (G : Finset κ) (T : Finset (Finset κ)) (Families : κ → Finset (Finset κ))
    (p w : κ → ℝ) (m : ℝ) (hm : 0 ≤ m) (hp : ∀ x, 0 ≤ p x) (_hw : ∀ a, 0 ≤ w a)
    (hpcap : ∀ x ∈ G, p x ≤ m) (hwcap : ∀ a ∈ G, w a ≤ m)
    (hT : ∀ J ∈ T, J ⊆ G)
    (hF : ∀ a ∈ G, ∀ I ∈ Families a, I ⊆ G ∧ (insert a I ∈ T ∨ I.erase a ∈ T)) :
    (∑ a ∈ G, w a * ∑ I ∈ Families a, ∏ x ∈ I, p x) ≤
      (1 + (G.card : ℝ) * (2 * m + m ^ 2)) * ∑ J ∈ T, (2 * m) ^ J.card := by
  have hprod (a : κ) (ha : a ∈ G) (I : Finset κ) (hI : I ∈ Families a) :
      w a * (∏ x ∈ I, p x) ≤ m ^ (I.card + 1) := by
    have hh : (∏ x ∈ I, p x) ≤ m ^ I.card := by
      simpa only [prod_const] using prod_le_prod₀ (fun x _ ↦ hp x)
        (fun x hx ↦ hpcap x ((hF a ha I hI).1 hx))
    have ht := mul_le_mul (hwcap a ha) hh (prod_nonneg fun x _ ↦ hp x) hm
    simpa only [pow_succ, mul_comm] using ht
  calc
    _ = ∑ a ∈ G, ∑ I ∈ Families a, w a * ∏ x ∈ I, p x := by simp only [mul_sum]
    _ ≤ ∑ a ∈ G, ∑ I ∈ Families a, m ^ (I.card + 1) :=
      sum_le_sum fun a ha ↦ sum_le_sum (hprod a ha)
    _ ≤ _ := finite_constant_bound G T Families m hm hT (fun a ha I hI ↦ (hF a ha I hI).2)

end PaperP1.OneSeedWeights
