module

public import PaperP1.Arithmetic.EffectiveExposure
public import PaperP1.Asymptotics.ValueHeightHalfCount

/-! # Complete counts of actual finite exposure populations

The source connectedness-to-exposure bridge is a separate obligation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveExposureCount

open Finset PaperP1.EffectiveExposure

def UniformCount (r : ℕ) (a b E ε : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : Finset ℕ, ∀ blocks : Fin r → ℕ → Finset ℕ,
    (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
    (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) →
    ((population G blocks).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε)

theorem zero_count (a b E ε : ℝ) (hε : 0 < ε) : UniformCount 0 a b E ε := by
  refine ⟨2, ?_⟩
  intro N hN G blocks _ _
  have hc : ((population G blocks).card : ℝ) ≤ 1 := by exact_mod_cast zero_card G blocks
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact hc.trans (by simpa only [Nat.cast_zero, zero_div, zero_add] using Real.one_le_rpow hn hε.le)

theorem induction_step (r : ℕ) (a b E : ℝ) (ha : 0 < a) (hE : 0 ≤ E)
    (hIH : ∀ k < r + 1, ∀ ε : ℝ, 0 < ε → UniformCount k a b E ε) :
    ∀ ε : ℝ, 0 < ε → UniformCount (r + 1) a b E ε := by
  classical
  intro ε hε
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hi := fun k : Fin (r + 1) ↦ hIH k.val k.isLt η hη
  choose NI hNI using hi
  have he := fun k : Fin (r + 1) ↦ PaperP1.ValueHeightHalfCount.uniform_logarithmic_count
    (r + 1 - k.val) k.val a b E η ha hE hη
  choose NE hNE using he
  let p := ((r + 1 : ℕ) : ℝ) / 2
  obtain ⟨NF, hNF⟩ := PaperP1.HalfCountSchedule.factor_absorption
    (Fintype.card (Code (r + 1))) (p + ε / 2) (ε / 2) (by positivity)
  refine ⟨2 + NF + univ.sup NI + univ.sup NE, ?_⟩
  intro N hN G blocks hvalues hdist
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hIn : ∀ k : Fin (r + 1), NI k ≤ N := by
    intro k
    have hk : NI k ≤ univ.sup NI := le_sup (f := NI) (mem_univ k)
    omega
  have hEn : ∀ k : Fin (r + 1), NE k ≤ N := by
    intro k
    have hk : NE k ≤ univ.sup NE := le_sup (f := NE) (mem_univ k)
    omega
  have hcell : ∀ c : Code (r + 1), ((cell G blocks c).card : ℝ) ≤ (N : ℝ) ^ (p + ε / 2) := by
    intro c
    have hB : ∀ old ∈ population G (leftBlocks c blocks),
        ((PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks old)).card : ℝ) ≤
          (N : ℝ) ^ (((r + 1 - c.1.val : ℕ) : ℝ) / 2 + η) := by
      intro old hold
      have holdG := ((mem_population G (leftBlocks c blocks) old).mp hold).1
      exact hNE c.1 N (hEn c.1) old G (rightBlocks c blocks)
        (fun i ↦ leftBlocks c blocks i (old i))
        (fun i x hx v hv ↦ hvalues _ x hx v hv)
        (fun i v hv ↦ hvalues _ (old i) (holdG i) v hv)
        (fun i x hx v hv ↦ hdist _ x hx v hv)
        (fun i v hv ↦ hdist _ (old i) (holdG i) v hv)
    have hleft := hNI c.1 N (hIn c.1) G (leftBlocks c blocks)
      (fun i x hx v hv ↦ hvalues _ x hx v hv)
      (fun i x hx v hv ↦ hdist _ x hx v hv)
    have hraw := cell_count G blocks c _ hB
    have hsum : (c.1.val : ℝ) + ((r + 1 - c.1.val : ℕ) : ℝ) = ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_sub_of_le c.1.isLt.le
    calc
      _ ≤ (N : ℝ) ^ ((c.1.val : ℝ) / 2 + η) *
          (N : ℝ) ^ (((r + 1 - c.1.val : ℕ) : ℝ) / 2 + η) :=
        hraw.trans (mul_le_mul_of_nonneg_right hleft (Real.rpow_nonneg hn.le _))
      _ = _ := by
        rw [← Real.rpow_add hn]
        congr 1
        dsimp [p, η]
        nlinarith only [hsum]
  have hcover := PaperP1.FiniteCoverCount.cardinal_le (population G blocks)
    (univ : Finset (Code (r + 1))) (cell G blocks) ((N : ℝ) ^ (p + ε / 2))
    (population_cover G blocks) (fun c _ ↦ hcell c)
  calc
    _ ≤ (Fintype.card (Code (r + 1)) : ℝ) * (N : ℝ) ^ (p + ε / 2) := by
      simpa only [card_univ] using hcover
    _ ≤ (N : ℝ) ^ ((p + ε / 2) + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; dsimp [p]; ring

theorem uniform_count (r : ℕ) (a b E ε : ℝ) (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    UniformCount r a b E ε := by
  have hall : ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → UniformCount r a b E ε := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      cases r with
      | zero => exact fun ε hε ↦ zero_count a b E ε hε
      | succ r => exact induction_step r a b E ha hE ih
  exact hall r ε hε

end PaperP1.EffectiveExposureCount
