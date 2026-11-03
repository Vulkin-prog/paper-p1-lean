module

public import PaperP1.Arithmetic.TernaryGroupCertificates

/-! # Uniform CRT counts for actual ternary groups on center-dependent sets

The finite sets in the three blocks may vary with the center. They are not
enumerated: only the bounded offsets and actual group sizes are labels.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryGroupCounts

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryTopProducts
  PaperP1.TernaryGroupCertificates PaperP1.FiniteEvenSquareClasses

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem top_product_le_height (U : Fin 3 → Finset ℕ) (H k A : ℕ)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A) :
    topProduct U H k ≤ A ^ k := by
  apply Finset.sup_le
  intro S hS
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hS
  calc
    _ ≤ ∏ _u ∈ S, A := by
      apply prod_le_prod
      intro u hu
      have hum := ((mem_active U H u).mp (hsub hu)).1
      exact (Nat.le_of_dvd (hpos 0 (u 0) (hum 0)) (group_dvd_value H u 0)).trans (hmax 0 (u 0) (hum 0))
    _ = _ := by rw [prod_const, hcard]

theorem weak_uniform (k K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ M ≥ N₀, ∀ (F : Finset (Fin 3 → ℕ))
      (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : (Fin 3 → ℕ) → ℕ)
      (base : Fin 3 → ℕ) (N R : ℕ) (T V : ℝ), 1 ≤ T → 0 ≤ V →
      (∀ X ∈ F, ∀ i, X i ∈ Ico (base i) (base i + N)) →
      (∀ X ∈ F, ∀ i, ∀ n ∈ U X i, ∀ m ∈ U X i, ((n : ℤ) - m).natAbs ≤ H X) →
      (∀ X ∈ F, ∀ i, ∀ n ∈ U X i, ((n : ℤ) - X i).natAbs ≤ R) →
      (∀ X ∈ F, T < (topProduct (U X) (H X) k : ℝ) ∧
        (topProduct (U X) (H X) k : ℝ) ≤ V ∧ topProduct (U X) (H X) k ≤ M ^ K) →
      (F.card : ℝ) ≤ (M : ℝ) ^ ε * (2 * R + 1 : ℕ) ^ (3 * k) *
        (8 * (N : ℝ) ^ 3 * T ^ (-2 : ℝ) + 4 * V) := by
  obtain ⟨N₀, hN₀, hcount⟩ := CRTProductRange.uniform_bound k K ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro M hM F U H base N R T V hT hV hbox hwidth hoff hprod
  let S : Finset ℕ := F.image fun X ↦ topProduct (U X) (H X) k
  have hS : ∀ Q ∈ S, 0 < Q ∧ T < (Q : ℝ) ∧ (Q : ℝ) ≤ V ∧ Q ≤ M ^ K := by
    intro Q hQ
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hQ
    have hp := hprod X hX
    exact ⟨by exact_mod_cast lt_of_le_of_lt (by linarith : 0 ≤ T) hp.1, hp⟩
  have hsub : F ⊆ CRTProductRange.centres k base N R S := by
    intro X hX
    have hp : 0 < topProduct (U X) (H X) k := (hS _ (mem_image_of_mem _ hX)).1
    exact mem_biUnion.mpr ⟨_, mem_image_of_mem _ hX,
      top_product_certificate X hp (hwidth X hX) (hoff X hX) base N (hbox X hX)⟩
  exact (show (F.card : ℝ) ≤ (CRTProductRange.centres k base N R S).card by
    exact_mod_cast card_le_card hsub).trans (hcount M hM base N R S T V hT hV hS)

theorem strong_uniform (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ M ≥ N₀, ∀ (F : Finset (Fin 3 → ℕ))
      (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H A : (Fin 3 → ℕ) → ℕ)
      (base : Fin 3 → ℕ) (N R : ℕ) (T V : ℝ), 1 ≤ T → 0 ≤ V →
      (∀ X ∈ F, ∀ i, X i ∈ Ico (base i) (base i + N)) →
      (∀ X ∈ F, 1 ≤ H X) →
      (∀ X ∈ F, ∀ i, ∀ n ∈ U X i, ∀ m ∈ U X i, ((n : ℤ) - m).natAbs ≤ H X) →
      (∀ X ∈ F, ∀ i, ∀ n ∈ U X i, 0 < n ∧ n ≤ A X ∧ ((n : ℤ) - X i).natAbs ≤ R) →
      (∀ X ∈ F, ∀ i, Function.Injective (data (U X i))) →
      (∀ X ∈ F, Pairwise (fun i j ↦ Disjoint (space (U X i)) (space (U X j)))) →
      (∀ X ∈ F, 6 * A X * H X ^ 2 < topProduct (U X) (H X) 3 ∧
        T ^ 3 < (topProduct (U X) (H X) 3 : ℝ) ^ 2) →
      (∀ X ∈ F, 2 * A X * (H X + 1) ≤ M ^ K ∧ (2 * A X * (H X + 1) : ℕ) ≤ V) →
      (F.card : ℝ) ≤ ((TernaryOffsetPlanes.planePool R).card : ℝ) * (2 * R + 1 : ℕ) ^ 6 *
        (2 * IntegerProductTail.productConstant 2 * (N : ℝ) ^ 2 * T ^ (-1 : ℝ) * Real.log (2 * T) +
          2 * V * (M : ℝ) ^ ε) := by
  obtain ⟨N₀, hcount⟩ := PlaneProductCover.uniform_bound K ε hε
  refine ⟨N₀, ?_⟩
  intro M hM F U H A base N R T V hT hV hbox hH hwidth hvalues hinj hdirect hlarge hupper
  have hcert : ∀ X ∈ F, ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ T < (p.1 : ℝ) * p.2 ∧
      p.1 * p.2 ≤ M ^ K ∧ (p.1 * p.2 : ℕ) ≤ V ∧
      X ∈ PlaneProductCover.pairCentres base N R (TernaryOffsetPlanes.planePool R) p := by
    intro X hX
    have hp : 0 < topProduct (U X) (H X) 3 := by
      have ht : 0 < T ^ 3 := pow_pos (by linarith) 3
      by_contra hnot
      have hz : topProduct (U X) (H X) 3 = 0 := by omega
      have hxlarge := (hlarge X hX).2
      rw [hz, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0)] at hxlarge
      exact (not_lt_of_ge ht.le) hxlarge
    obtain ⟨S, hsub, hcard, hprod⟩ := attained (U X) (H X) 3 hp
    obtain ⟨v, hv, hmem, heq⟩ := enumerate_selection (U X) (H X) 3 S hsub hcard
    have hval : group (H X) (v 0) * group (H X) (v 1) * group (H X) (v 2) =
        topProduct (U X) (H X) 3 := by
      simpa only [Fin.prod_univ_three] using heq.trans hprod.symm
    have hforcing : 6 * A X * H X ^ 2 <
        group (H X) (v 0) * group (H X) (v 1) * group (H X) (v 2) := by
      rw [hval]
      exact (hlarge X hX).1
    have htail : T ^ 3 < ((group (H X) (v 0) : ℝ) * group (H X) (v 1) * group (H X) (v 2)) ^ 2 := by
      have hreal : ((group (H X) (v 0) : ℝ) * group (H X) (v 1) * group (H X) (v 2)) =
          (topProduct (U X) (H X) 3 : ℝ) := by exact_mod_cast hval
      rw [hreal]
      exact (hlarge X hX).2
    obtain ⟨p, hp0, hp1, hpT, hpu, hpc⟩ := large_triple_certificate X (hH X hX)
      (hwidth X hX) (fun i n hn ↦ (hvalues X hX i n hn).1)
      (fun i n hn ↦ (hvalues X hX i n hn).2.1) (hinj X hX) (hdirect X hX)
      (fun i n hn ↦ (hvalues X hX i n hn).2.2) v hv
      (fun j ↦ (mem_filter.mp (hmem j)).1) hforcing T (by linarith) htail base N (hbox X hX)
    exact ⟨p, hp0, hp1, hpT, hpu.trans (hupper X hX).1,
      (show ((p.1 * p.2 : ℕ) : ℝ) ≤ (2 * A X * (H X + 1) : ℕ) by exact_mod_cast hpu).trans (hupper X hX).2,
      hpc⟩
  choose p hp using hcert
  let sizes : Finset (ℕ × ℕ) := F.attach.image fun X ↦ p X.val X.property
  have hsizes : ∀ z ∈ sizes, 0 < z.1 ∧ 0 < z.2 ∧ T < (z.1 : ℝ) * z.2 ∧
      z.1 * z.2 ≤ M ^ K ∧ (z.1 * z.2 : ℕ) ≤ V := by
    intro z hz
    obtain ⟨X, _, rfl⟩ := mem_image.mp hz
    exact ⟨(hp X.val X.property).1, (hp X.val X.property).2.1, (hp X.val X.property).2.2.1,
      (hp X.val X.property).2.2.2.1, (hp X.val X.property).2.2.2.2.1⟩
  have hsub : F ⊆ PlaneProductCover.centres base N R (TernaryOffsetPlanes.planePool R) sizes := by
    intro X hX
    exact mem_biUnion.mpr ⟨p X hX, mem_image.mpr ⟨⟨X, hX⟩, mem_attach _ _, rfl⟩, (hp X hX).2.2.2.2.2⟩
  exact (show (F.card : ℝ) ≤ (PlaneProductCover.centres base N R (TernaryOffsetPlanes.planePool R) sizes).card by
    exact_mod_cast card_le_card hsub).trans
    (hcount M hM base N R (TernaryOffsetPlanes.planePool R) sizes T V hT hV hsizes)

end PaperP1.TernaryGroupCounts
