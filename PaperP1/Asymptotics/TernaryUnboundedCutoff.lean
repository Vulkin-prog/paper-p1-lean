module

public import PaperP1.Asymptotics.TernaryGroupTheorem
public import PaperP1.Arithmetic.TernaryCutoffMonotonicity

/-! # T1.16 with no upper bound on the source prime cutoff

The source only asks that H exceed the diameters. Cap it internally at
2R+1: all actual group products can only increase, while the cap still
exceeds the diameter of every block of offsets in [-R,R].
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryUnboundedCutoff

open Finset PaperP1.TernaryTopProducts PaperP1.FiniteEvenSquareClasses

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

structure SourceConditions (N R D : ℕ) (base : Fin 3 → ℕ)
    (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : (Fin 3 → ℕ) → ℕ) (X : Fin 3 → ℕ) : Prop where
  box : ∀ i, X i ∈ Ico (base i) (base i + D * N)
  cutoff : 1 ≤ H X
  diameter : ∀ i, ∀ n ∈ U X i, ∀ m ∈ U X i, ((n : ℤ) - m).natAbs ≤ H X
  values : ∀ i, ∀ n ∈ U X i, 0 < n ∧ n ≤ D * N ∧ ((n : ℤ) - X i).natAbs ≤ R
  even_injective : ∀ i, Function.Injective (EvenImage.evenMap (K := Arithmetic.F₂) (data (U X i)))
  disjoint : Pairwise (fun i j ↦ Disjoint (space (U X i)) (space (U X j)))

theorem SourceConditions.capped {N L R D : ℕ} {base : Fin 3 → ℕ}
    {U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ} {H : (Fin 3 → ℕ) → ℕ} {X : Fin 3 → ℕ}
    (h : SourceConditions N R D base U H X) (hR : R ≤ D * (L + 1)) :
    TernaryGroupTheorem.SourceAdmissible N L R (2 * D + 1) base U
      (fun X ↦ min (H X) (2 * R + 1)) X := by
  have hD : D ≤ 2 * D + 1 := by omega
  have hDN : D * N ≤ (2 * D + 1) * N := Nat.mul_le_mul_right N hD
  refine ⟨?_, ⟨le_min h.cutoff (by omega), ?_⟩, ?_, ?_, h.even_injective, h.disjoint⟩
  · intro i
    obtain ⟨hi0, hi1⟩ := mem_Ico.mp (h.box i)
    exact mem_Ico.mpr ⟨hi0, by omega⟩
  · exact (min_le_right _ _).trans (by nlinarith)
  · intro i n hn m hm
    apply le_min (h.diameter i n hn m hm)
    have heq : (n : ℤ) - m = ((n : ℤ) - X i) - ((m : ℤ) - X i) := by ring
    rw [heq]
    exact ((Int.natAbs_sub_le _ _).trans (Nat.add_le_add (h.values i n hn).2.2 (h.values i m hm).2.2)).trans (by omega)
  · intro i n hn
    exact ⟨(h.values i n hn).1, (h.values i n hn).2.1.trans hDN, (h.values i n hn).2.2⟩

theorem companion_T1_16 (C : ℝ) (D k J : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (T : ℝ), 1 ≤ T →
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, T < (topProduct (U z.1 z.2) (H z.1 z.2) k : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 / T ^ 2 + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  obtain ⟨N₀, hN₀, hb⟩ := TernaryGroupTheorem.bounded_cutoff_patterns C (2 * D + 1) k J hk ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR α _instα F U H base T hT hlabels hadm hprod
  have hR' : R ≤ (2 * D + 1) * (L + 1) := hR.trans (Nat.mul_le_mul_right _ (by omega : D ≤ 2 * D + 1))
  apply hb N hN L R hband hR' α F U (fun a X ↦ min (H a X) (2 * R + 1)) base T hT hlabels
  · intro z hz
    exact (hadm z hz).capped hR
  · intro z hz
    exact (hprod z hz).trans_le (by
      exact_mod_cast TernaryCutoffMonotonicity.top_product_le (U z.1 z.2) k (min_le_left (H z.1 z.2) (2 * R + 1)))

def tuples {α : Type*} [DecidableEq α] (N R D k : ℕ) (I : Finset α)
    (base : α → Fin 3 → ℕ) (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
    (H : α → (Fin 3 → ℕ) → ℕ) (T : ℝ) : Finset (α × (Fin 3 → ℕ)) := by
  classical
  exact I.biUnion fun a ↦ ((CRTProductCover.box 3 (base a) (D * N)).filter fun X ↦
    SourceConditions N R D (base a) (U a) (H a) X ∧ T < (topProduct (U a X) (H a X) k : ℝ)).image fun X ↦ (a, X)

theorem mem_tuples {α : Type*} [DecidableEq α] (N R D k : ℕ) (I : Finset α)
    (base : α → Fin 3 → ℕ) (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
    (H : α → (Fin 3 → ℕ) → ℕ) (T : ℝ) (z : α × (Fin 3 → ℕ)) :
    z ∈ tuples N R D k I base U H T ↔ z.1 ∈ I ∧
      SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2 ∧
        T < (topProduct (U z.1 z.2) (H z.1 z.2) k : ℝ) := by
  classical
  constructor
  · intro hz
    obtain ⟨a, ha, hz⟩ := mem_biUnion.mp hz
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hz
    exact ⟨ha, (mem_filter.mp hX).2⟩
  · rintro ⟨ha, hadm, hprod⟩
    exact mem_biUnion.mpr ⟨z.1, ha, mem_image.mpr
      ⟨z.2, mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hadm.box, hadm, hprod⟩, Prod.eta z⟩⟩

theorem actual_tuples_bound (C : ℝ) (D k J : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (I : Finset α) (base : α → Fin 3 → ℕ)
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ) (T : ℝ),
      1 ≤ T → I.card ≤ (L + 1) ^ J →
      ((tuples N R D k I base U H T).card : ℝ) ≤
        (N : ℝ) ^ ε * ((N : ℝ) ^ 3 / T ^ 2 + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  obtain ⟨N₀, hN₀, hb⟩ := companion_T1_16 C D k J hk ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR α _instα I base U H T hT hI
  apply hb N hN L R hband hR α (tuples N R D k I base U H T) U H base T hT
  · apply (card_le_card ?_).trans hI
    intro a ha
    obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
    exact ((mem_tuples N R D k I base U H T z).mp hz).1
  · intro z hz
    exact ((mem_tuples N R D k I base U H T z).mp hz).2.1
  · intro z hz
    exact ((mem_tuples N R D k I base U H T z).mp hz).2.2

end PaperP1.TernaryUnboundedCutoff
