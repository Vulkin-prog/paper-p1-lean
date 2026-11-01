module

public import PaperP1.Asymptotics.HalfCountPowerBounds
public import PaperP1.Asymptotics.ShortWitnessListsCount

/-! # The full simultaneous half-count induction for actual window witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalHalfCount

open Finset PaperP1.ProjectedWindowLists PaperP1.ChosenWindowWitness
  PaperP1.HalfCountStages PaperP1.HalfCountSchedule PaperP1.HalfCountPowerBounds

def UniformCount (r s : ℕ) (a b E ε : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ old : Fin s → ℕ, ∀ G : Finset ℕ,
    0 < W → (W : ℝ) ≤ E * Real.log N →
    (∀ n ∈ G, a * N ≤ n ∧ (n : ℝ) ≤ b * N) → (∀ k, old k ∈ G) →
    ((lists (r := r) G W old).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε)

theorem cons_mem {s : ℕ} (G : Finset ℕ) (old : Fin s → ℕ) (hold : ∀ k, old k ∈ G)
    (z : ℕ) (hz : z ∈ G) : ∀ k : Fin (s + 1), (Fin.cons z old : Fin (s + 1) → ℕ) k ∈ G := by
  intro k
  exact Fin.cases hz hold k

theorem zero_count (s : ℕ) (a b E ε : ℝ) (hε : 0 < ε) : UniformCount 0 s a b E ε := by
  refine ⟨2, ?_⟩
  intro N hN W old G _ _ _ _
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc : ((lists (r := 0) G W old).card : ℝ) ≤ 1 := by exact_mod_cast zero_card G W old
  exact hc.trans (by simpa only [Nat.cast_zero, zero_div, zero_add] using Real.one_le_rpow hn hε.le)

theorem induction_step (r : ℕ) (a b E : ℝ) (ha : 0 < a) (hE : 0 ≤ E)
    (hIH : ∀ k < r + 1, ∀ s : ℕ, ∀ ε : ℝ, 0 < ε → UniformCount k s a b E ε) :
    ∀ s : ℕ, ∀ ε : ℝ, 0 < ε → UniformCount (r + 1) s a b E ε := by
  classical
  intro s ε hε
  let η := ε / 16
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨J, hJ, hstep⟩ := exists_small_step (ε / 8) (by positivity)
  let t := 5 * (r + s) + 1
  let m := t + 25
  let p := ((r + 1 : ℕ) : ℝ) / 2
  let K := 1 + 2 * (r + 1) + J * ((r + 1) * r + (r + 1) * s)
  obtain ⟨NI, hNI⟩ := hIH r (by omega) (s + 1) η hη
  obtain ⟨NP, hNP⟩ := hIH (r - 1) (by omega) (s + 1 + 1) η hη
  obtain ⟨NS, hNS⟩ := PaperP1.ShortWitnessListsCount.uniform_short_count (r + 1) s m a b E η ha hη
  obtain ⟨NX, hNX⟩ := PaperP1.HalfCountExceptionalSets.small_kernel_count a b E η ha hη
  obtain ⟨C, hC, hcompare⟩ := PaperP1.ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨NG, hNG⟩ := centre_count C η hη
  obtain ⟨NV, hNV⟩ := PaperP1.ComparableSplitProductCount.width_lt_centre C E 1
  obtain ⟨NF, hNF⟩ := factor_absorption K (p + ε / 2) (ε / 2) (by positivity)
  have hc := fun u : Fin J ↦ PaperP1.HalfCountStageConfinement.uniform_confinement
    a b (A J u.val) E η ha (exponent_ge_two J u.val u.isLt) hE hη
  choose M Nc hNc using hc
  have hgap : ((Fintype.card (Fin r) + Fintype.card (Fin s) : ℕ) : ℝ) < (t : ℝ) / 5 := by
    simp only [Fintype.card_fin]
    dsimp [t]
    push_cast
    linarith
  have hd := fun u : Fin J ↦ PaperP1.AnchorRelationCertificates.uniform_certificates
    (ν := Fin r) (κ := Fin s) C t hC (A J u.val) E η
    (by have := exponent_ge_two J u.val u.isLt; linarith) hE hη hgap
  choose Nd hNd using hd
  refine ⟨2 + NI + NP + NS + NX + NG + NV + NF + univ.sup Nc + univ.sup Nd, ?_⟩
  intro N hN W old G hW hwidth hG hold
  have hn2 : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcn : ∀ u : Fin J, Nc u ≤ N := by
    intro u
    have hu : Nc u ≤ univ.sup Nc := le_sup (f := Nc) (mem_univ u)
    omega
  have hdn : ∀ u : Fin J, Nd u ≤ N := by
    intro u
    have hu : Nd u ≤ univ.sup Nd := le_sup (f := Nd) (mem_univ u)
    omega
  have hGnat : ∀ n ∈ G, W < n ∧ n ≤ C * N := by
    intro n hnG
    have hcomp := hcompare N n (hG n hnG).1 (hG n hnG).2
    exact ⟨hNV N (by omega) n W hcomp.1 (by simpa only [Real.rpow_one] using hwidth), hcomp.2⟩
  have hone : ∀ z ∈ G, ((lists (r := r) G W (Fin.cons z old)).card : ℝ) ≤
      (N : ℝ) ^ ((r : ℝ) / 2 + η) := by
    intro z hz
    exact hNI N (by omega) W (Fin.cons z old) G hW hwidth hG (cons_mem G old hold z hz)
  have htwo : ∀ k : ℕ, r = k + 1 → ∀ z ∈ G, ∀ w ∈ G,
      ((lists (r := k) G W (Fin.cons w (Fin.cons z old))).card : ℝ) ≤
        (N : ℝ) ^ ((k : ℝ) / 2 + η) := by
    intro k hk z hz w hw
    have hrk : r - 1 = k := by omega
    subst k
    exact hNP N (by omega) W (Fin.cons w (Fin.cons z old)) G hW hwidth hG
      (cons_mem G (Fin.cons z old) (cons_mem G old hold z hz) w hw)
  let Y := fun j ↦ (Real.log N) ^ (A J j)
  have hpool : ∀ j < J, ∃ P : Finset ℕ, P ⊆ G ∧
      (P.card : ℝ) ≤ (N : ℝ) ^ (1 - x J j + η) ∧
      ∀ n ∈ survivors (r := r + 1) G N W old m t Y j, ∀ i,
        m < (chosen W old n i).card → n i ∈ P := by
    intro j hj
    cases j with
    | zero =>
      refine ⟨G, Subset.rfl, ?_, ?_⟩
      · simpa only [x_zero, sub_zero] using hNG N (by omega) G (fun n hnG ↦ (hGnat n hnG).2)
      · intro n hnS i _
        exact ((mem_lists G W old n).mp (survivor_data G N W old m t 0 Y n hnS).1).1 i
    | succ j =>
      let u : Fin J := ⟨j, by omega⟩
      refine ⟨M u N ∩ G, inter_subset_right, ?_, ?_⟩
      · have hcard : ((M u N ∩ G).card : ℝ) ≤ (M u N).card := by exact_mod_cast card_le_card inter_subset_left
        exact hcard.trans (by simpa only [u, inverse_exponent] using (hNc u N (hcn u)).1)
      · intro n hnS i hi
        exact (hNc u N (hcn u)).2 W t (r + 1) s old j Y G hwidth hG rfl n hnS i hi
  let R := (N : ℝ) ^ (p + ε / 2)
  have hsmallpower : (N : ℝ) ^ (p + η) ≤ R :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [η]; linarith)
  have hrare : (N : ℝ) ^ (p + 2 * η) ≤ R :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [η]; linarith)
  have hpair : (N : ℝ) ^ (p + step J + 3 * η) ≤ R :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [η] at *; linarith only [hstep, hε])
  have hshort : ((shortLists (r := r + 1) G W old m).card : ℝ) ≤ R :=
    (hNS N (by omega) W old G hW hwidth hG).trans hsmallpower
  have hexception : ((exceptionalLists (r := r + 1) G N W old).card : ℝ) ≤ (r + 1 : ℝ) * R := by
    have hX := hNX N (by omega) W G hW hwidth hG
    have hB := fun z (hz : z ∈ PaperP1.HalfCountExceptionalSets.smallKernelCentres G N W) ↦ hone z (mem_filter.mp hz).1
    exact (rare_coordinate_bound G _ N W old η hn2 hX hB).trans
      (mul_le_mul_of_nonneg_left hrare (by positivity))
  have hlast : ((survivors (r := r + 1) G N W old m t Y J).card : ℝ) ≤ (r + 1 : ℝ) * R := by
    let u : Fin J := ⟨J - 1, by omega⟩
    let P := M u N ∩ G
    have hlastindex : J - 1 + 1 = J := by omega
    have hexp : 1 - 1 / A J u.val + η = 1 / 2 + η := by
      rw [inverse_exponent]
      change 1 - x J (J - 1 + 1) + η = 1 / 2 + η
      rw [hlastindex, x_last J hJ]
      ring
    have hPcard : (P.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + η) := by
      have hcard : (P.card : ℝ) ≤ (M u N).card := by exact_mod_cast card_le_card inter_subset_left
      exact hcard.trans (by simpa only [hexp] using (hNc u N (hcn u)).1)
    have hP : ∀ n ∈ survivors (r := r + 1) G N W old m t Y J, ∀ i,
        m < (chosen W old n i).card → n i ∈ P := by
      intro n hnS i hi
      exact (hNc u N (hcn u)).2 W t (r + 1) s old (J - 1) Y G hwidth hG rfl n
        (by simpa only [hlastindex] using hnS) i hi
    have hcover := PaperP1.HalfCountStageReceivers.survivor_has_coordinate G N W old m t J Y P hP
    have hc : ((survivors (r := r + 1) G N W old m t Y J).card : ℝ) ≤
        (((lists (r := r + 1) G W old).filter fun n ↦ ∃ i, n i ∈ P).card : ℝ) := by
      exact_mod_cast card_le_card hcover
    exact (hc.trans (rare_coordinate_bound G P N W old η hn2 hPcard
      (fun z hz ↦ hone z (mem_inter.mp hz).2))).trans (mul_le_mul_of_nonneg_left hrare (by positivity))
  have hremoved : ∀ j < J,
      ((survivors (r := r + 1) G N W old m t Y j \ survivors G N W old m t Y (j + 1)).card : ℝ) ≤
        (((r + 1) * r + (r + 1) * s : ℕ) : ℝ) * R := by
    intro j hj
    obtain ⟨P, hPsub, hPcard, hP⟩ := hpool j hj
    let u : Fin J := ⟨j, hj⟩
    have hc := hNd u N (hdn u) W hwidth G hGnat
    have hdegree : ∀ z ∈ G,
        ((PaperP1.AnchorCertificateGraph.outgoing G (C * N) W t (Y j) z).card : ℝ) ≤ (N : ℝ) ^ (x J (j + 1) + η) ∧
        ((PaperP1.AnchorCertificateGraph.incoming G (C * N) W t (Y j) z).card : ℝ) ≤ (N : ℝ) ^ (x J (j + 1) + η) := by
      simpa only [u, Y, inverse_exponent] using hc.1
    have hraw := removed_power_bound G P N (C * N) W old hold m t j J Y η hn2 hJ hj
      hPsub hP hPcard hdegree hc.2 hone htwo
    calc
      _ ≤ (((r + 1) * r : ℕ) : ℝ) * R + (((r + 1) * s : ℕ) : ℝ) * R := hraw.trans (add_le_add
        (mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hrare (Nat.cast_nonneg _)))
      _ = _ := by push_cast; ring
  have hcount := finite_assembly G N W old m t J Y R hshort hexception hlast hremoved
  calc
    _ ≤ (K : ℝ) * R := hcount
    _ ≤ (N : ℝ) ^ ((p + ε / 2) + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; dsimp [p]; ring

theorem uniform_count (r s : ℕ) (a b E ε : ℝ) (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    UniformCount r s a b E ε := by
  have hall : ∀ r : ℕ, ∀ s : ℕ, ∀ ε : ℝ, 0 < ε → UniformCount r s a b E ε := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      cases r with
      | zero => exact fun s ε hε ↦ zero_count s a b E ε hε
      | succ r => exact induction_step r a b E ha hE ih
  exact hall r s ε hε

end PaperP1.ConditionalHalfCount
