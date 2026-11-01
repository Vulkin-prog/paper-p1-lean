module

public import PaperP1.Combinatorics.PrimeRowComponents

/-! # Finite counts of small and large free components on actual values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeComponentCount

open Finset PaperP1.Arithmetic PaperP1.PinnedGraphResolution PaperP1.PrimeRowComponents

local instance componentCountDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance componentCountAdj (S P : Finset ℕ) : DecidableRel (graph S P).Adj := Classical.decRel _

def small (S P : Finset ℕ) (K : ℕ) : Finset (graph S P).ConnectedComponent :=
  (unpinnedComponents (graph S P) (pins S P)).filter fun c ↦ (values S P c).card ≤ K

def large (S P : Finset ℕ) (K : ℕ) : Finset (graph S P).ConnectedComponent :=
  (unpinnedComponents (graph S P) (pins S P)).filter fun c ↦ K < (values S P c).card

def listedPrime (P : Finset ℕ) (i : Fin P.card) : ℕ := (P.equivFin.symm i).val

theorem listedPrime_covers (P : Finset ℕ) (p : ℕ) : (∃ i, listedPrime P i = p) ↔ p ∈ P := by
  constructor
  · rintro ⟨i, rfl⟩
    exact (P.equivFin.symm i).property
  · intro hp
    refine ⟨P.equivFin ⟨p, hp⟩, ?_⟩
    simp only [listedPrime, Equiv.symm_apply_apply]

theorem small_count {S P : Finset ℕ} {K U R t : ℕ}
    (hrows : ∀ p, (rows S P p).card ≤ 2)
    (hlower : ∀ n ∈ S, U ≤ n) (hupper : ∀ n ∈ S, n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U) (ht : 1 ≤ t) :
    (small S P K).card < max (P.card + 1) (2 * t * 2 ^ ((P.card + 1) / t + 1)) := by
  let Q := small S P K
  let enum : Fin Q.card ≃ Q := Q.equivFin.symm
  let blocks (i : Fin Q.card) := values S P (enum i).val
  have hi (i : Fin Q.card) :
      ¬ComponentPinned (graph S P) (pins S P) (enum i).val ∧ (blocks i).card ≤ K := by
    have h := mem_filter.mp (enum i).property
    exact ⟨(mem_unpinnedComponents _).mp h.1, h.2⟩
  apply SmallComponentBound.finite_count (listedPrime P) blocks
  · exact fun i ↦ values_nonempty S P (enum i).val
  · intro i j hij
    apply values_disjoint S P
    intro heq
    exact hij (enum.injective (Subtype.ext heq))
  · exact fun i ↦ (hi i).2
  · intro i p hp
    exact free_component_parity hrows (enum i).val (hi i).1 p
      (fun hpP ↦ hp ((listedPrime_covers P p).mpr hpP))
  · intro i n hn
    exact hlower n (values_subset S P (enum i).val hn)
  · intro i n hn
    exact hupper n (values_subset S P (enum i).val hn)
  · exact hR
  · exact hU
  · exact hgrowth
  · exact ht

theorem small_add_large (S P : Finset ℕ) (K : ℕ) :
    (small S P K).card + (large S P K).card =
      (unpinnedComponents (graph S P) (pins S P)).card := by
  have heq : small S P K ∪ large S P K = unpinnedComponents (graph S P) (pins S P) := by
    ext c
    simp only [small, large, mem_union, mem_filter]
    constructor
    · intro hc
      exact hc.elim And.left And.left
    · intro hc
      by_cases hK : (values S P c).card ≤ K
      · exact Or.inl ⟨hc, hK⟩
      · exact Or.inr ⟨hc, Nat.lt_of_not_ge hK⟩
  have hdisj : Disjoint (small S P K) (large S P K) := by
    apply disjoint_left.mpr
    intro c hc hd
    have hc' := (mem_filter.mp hc).2
    have hd' := (mem_filter.mp hd).2
    omega
  rw [← card_union_of_disjoint hdisj, heq]

theorem small_count_of_budget {S P : Finset ℕ} {K U R t A : ℕ}
    (hrows : ∀ p, (rows S P p).card ≤ 2)
    (hlower : ∀ n ∈ S, U ≤ n) (hupper : ∀ n ∈ S, n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U) (ht : 1 ≤ t)
    (hbudget : P.card + 1 ≤ A * t) :
    (small S P K).card < 2 * t * 2 ^ (A + 1) := by
  apply (small_count hrows hlower hupper hR hU hgrowth ht).trans_le
  apply max_le
  · have hpow : A ≤ 2 ^ (A + 1) :=
      (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ A))
    calc
      P.card + 1 ≤ A * t := hbudget
      _ ≤ 2 ^ (A + 1) * t := Nat.mul_le_mul_right t hpow
      _ ≤ 2 * t * 2 ^ (A + 1) := by nlinarith [Nat.zero_le (2 ^ (A + 1))]
  · have hdiv : (P.card + 1) / t ≤ A :=
      Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hbudget)
    exact Nat.mul_le_mul_left (2 * t) (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hdiv 1))

theorem large_vertex_budget (S P : Finset ℕ) (K : ℕ) :
    (K + 1) * (large S P K).card ≤ S.card := by
  calc
    _ = ∑ _c ∈ large S P K, (K + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ c ∈ large S P K, Fintype.card c.supp := by
      apply sum_le_sum
      intro c hc
      have hsize := (mem_filter.mp hc).2
      rw [← values_card S P c]
      omega
    _ ≤ ∑ c : (graph S P).ConnectedComponent, Fintype.card c.supp :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)
    _ = S.card := by rw [sum_card_component_support, Fintype.card_coe]

theorem large_count (S P : Finset ℕ) (K : ℕ) : (large S P K).card ≤ S.card / (K + 1) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < K + 1)).mpr
  simpa only [Nat.mul_comm] using large_vertex_budget S P K

end PaperP1.PrimeComponentCount
