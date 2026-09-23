module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.Sync
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Pure window facts -/

omit [Fintype V] in
/-- One attributed vote in one window round makes its validator represented. -/
theorem represented_of_vote_mem
    {pool : Round → Finset (Protocol.SGVote V)} {etaSG r k : Round}
    {v : V} {u : Protocol.SGVote V}
    (hk : k ∈ Protocol.latest_window etaSG r)
    (hu : u ∈ pool k) (hval : u.val_index = v) :
    Protocol.represented pool etaSG v r = true := by
  unfold Protocol.represented
  rw [List.any_eq_true]
  refine ⟨k, hk, ?_⟩
  unfold Protocol.holds_vote_by Protocol.sg_votes_by
  simp only [decide_eq_true_eq]
  apply Finset.card_pos.mpr
  exact ⟨u, Finset.mem_filter.mpr ⟨hu, hval⟩⟩


/-! ## Transport to a read and representation -/

/-- A projected SG vote present after an event strictly before `t` remains in
the store immediately before `t`. -/
theorem sgVote_mem_stateBeforeTime_of_post
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {w : V} {j : Nat} {e : Event V} {t : Time} {k : Round}
    {u : Protocol.SGVote V}
    (hj : rho.events[j]? = some e) (hjt : e.time < t)
    (hu : u ∈ (rho.stateBefore S (j + 1) w).st.toHealing.sg_votes k) :
    u ∈ (rho.stateBeforeTime S t w).st.toHealing.sg_votes k := by
  let N := (rho.events.filter (fun x => decide (x.time < t))).length
  have hjN : j < N := by
    by_contra hnot
    have htle : t ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S sch (t := t) (j := j) (e := e)
        (by simpa [N] using Nat.le_of_not_gt hnot) hj
    exact (not_le_of_gt hjt) htle
  change u ∈ ((rho.stateBefore S (j + 1) w).st.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  have hcarry := Proofs.HealingLemmas.stateBefore_sg_pool_subset S rho w k
    (i := j + 1) N (Nat.succ_le_of_lt hjN)
  have haN := hcarry ha
  rw [Proofs.Optimistic.stateBeforeTime_eq_take S sch t]
  change u ∈ ((rho.stateBefore S N w).st.sg_pool k).image Protocol.sgVote
  exact Finset.mem_image.mpr ⟨a, haN, hau⟩

/-- One network delay after `a_(r-1)` fits before `a_r`. The bound spends only
`Δ > 0` and the Section 7 standing condition `R ≥ 2`. -/
theorem previous_action_add_delta_le_action (S : Setup V) {r : Round}
    (hr : 0 < r) : S.a (r - 1) + S.E.Δ ≤ S.a r := by
  have hre : r - 1 + 1 = r := by
    have key : ∀ n : Nat, 0 < n → n - 1 + 1 = n := by
      intro n hn
      omega
    exact key r hr
  have ha := Proofs.HealingLemmas.a_add_rounds S (r - 1) 1
  rw [hre] at ha
  rw [ha]
  simp only [Nat.mul_one]
  have hfactor : (1 : Time) ≤ 4 * (S.hc.R : Time) := by
    have key : ∀ R : Nat, 2 ≤ R → 1 ≤ 4 * R := by
      intro R hR
      omega
    exact_mod_cast key S.hc.R S.hc.R_ge_two
  have hDelta : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have hmul : S.E.Δ * 1 ≤ S.E.Δ * (4 * (S.hc.R : Time)) :=
    Int.mul_le_mul_of_nonneg_left hfactor hDelta
  calc
    S.a (r - 1) + S.E.Δ = S.a (r - 1) + S.E.Δ * 1 := by ring
    _ ≤ S.a (r - 1) + S.E.Δ * (4 * (S.hc.R : Time)) :=
      add_le_add_right hmul _
    _ = S.a (r - 1) + 4 * S.E.Δ * (S.hc.R : Time) := by ring

end Protocol
end DecoupledConsensusModel

end
