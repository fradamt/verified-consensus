module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryProducers
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrivalStampCarrier
public import DecoupledConsensusProofs.Execution.OutageActionInputs
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryB4B5Time
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Schedule arithmetic

The SG row of any strictly earlier round is delivered a full `Δ` before the
target round's early G2 cutoff. `3 ≤ S.hc.R` is exactly what makes the
tightest instance (`k = r - 1`) hold with no slack. -/

theorem action_delta_le_early_g2 (S : Setup V) {k r : Round} (hkr : k < r)
    (hR : 3 ≤ S.hc.R) : S.a k + S.E.Δ ≤ early S.E S.hc r .g2 := by
  have hnat : k * S.hc.R + 3 ≤ r * S.hc.R := by
    have h1 : (k + 1) * S.hc.R ≤ r * S.hc.R := Nat.mul_le_mul_right _ hkr
    have h2 : (k + 1) * S.hc.R = k * S.hc.R + S.hc.R := by ring
    rw [h2] at h1
    exact le_trans (Nat.add_le_add_left hR _) h1
  have hcast : ((k * S.hc.R : Nat) : Time) + 3 ≤ ((r * S.hc.R : Nat) : Time) := by
    exact_mod_cast hnat
  have heq : early S.E S.hc r .g2 - (S.a k + S.E.Δ) =
      4 * S.E.Δ * (((r * S.hc.R : Nat) : Time) - (((k * S.hc.R : Nat) : Time) + 3)) := by
    unfold DecoupledConsensusModel.Protocol.early DecoupledConsensusModel.Protocol.opening DecoupledConsensusModel.Protocol.Phase.earlyOffset
      Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a
      Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  have hnonneg : (0 : Time) ≤ 4 * S.E.Δ *
      (((r * S.hc.R : Nat) : Time) - (((k * S.hc.R : Nat) : Time) + 3)) :=
    Int.mul_nonneg (Int.mul_nonneg (by norm_num) S.E.Δ_pos.le) (sub_nonneg.mpr hcast)
  exact sub_nonneg.mp (by rw [heq]; exact hnonneg)

theorem early_g2_lt_domain_g2 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 < domain S.E S.hc r .g2 := by
  change DecoupledConsensusModel.Protocol.opening S.E S.hc r + (-5) * S.E.Δ <
    DecoupledConsensusModel.Protocol.opening S.E S.hc r + (-1) * S.E.Δ
  refine Int.add_lt_add_left ?_ _
  calc (-5 : Time) * S.E.Δ = (-1 : Time) * S.E.Δ - 4 * S.E.Δ := by ring
    _ < (-1 : Time) * S.E.Δ := sub_lt_self _ (Int.mul_pos (by norm_num) S.E.Δ_pos)

/-! ## 2. Generalised healthy SG arrival

`Proofs.NamedSGArrival.healthy_emitted_sg_at_next_g2` fixes `r = a.round + 1` and
reads at `stateBeforeTime … (domain r.g2)`. The capture reader of
`GradedRootOnHistory` is at an event index instead, and the emitting round is
any window round, so the same proof is replayed with those two inputs open. -/

theorem healthy_emitted_sg_raw_at_index
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (cap : Time) (healthy : NamedHealthyPrefixDelivery S rho cap)
    {a : NamedAttestation V} (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    (r : Round) (hwindow : a.round ∈ Protocol.latest_window S.hc.η_SG r)
    (hearly : S.a a.round + S.E.Δ ≤ early S.E S.hc r .g2)
    (hcap : S.a a.round + S.E.Δ ≤ cap)
    (reader : V) (hreader : reader ∈ rho.honest)
    (j : Nat) (e : NamedEvent V) (hj : rho.events[j]? = some e)
    (hjt : early S.E S.hc r .g2 ≤ e.time) :
    a ∈ (NamedRun.stateBefore S rho j reader).st.sg_rows a.round ∧
      Protocol.sgVote a.erase ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBefore S rho j reader).st.core.toHealing.gradeView
        S.hc.η_SG r (early S.E S.hc r .g2) a.val_index := by
  obtain ⟨td, hlo, hhi, i, hcall⟩ :=
    healthy.broadcast a.val_index ha (.attest a) (S.a a.round) hem reader hreader hcap rfl
  have hpost := SGArrival.honest_row_after_call S rho
    core.toNamedScheduleWellFormed core.toNamedUnforgeable ha hem hcall hlo hhi
  obtain ⟨e', he', _, het⟩ := hcall.2
  have hdata : SGArrival.Data td (NamedRun.stateBefore S rho (i + 1) reader).st := by
    simpa only [het] using
      (SGArrival.data_at_event S rho core.toNamedScheduleWellFormed he' reader).2
  obtain ⟨_, stamp, hstampBound, hstamp⟩ := hdata.2 a.round a hpost
  have htdEarly : td < early S.E S.hc r .g2 := hhi.trans_le hearly
  have hij : i + 1 ≤ j := by
    by_contra hcon
    have hji : j ≤ i := by omega
    have hle := SGArrival.event_time_le rho core.sorted hj he' hji
    rw [het] at hle
    exact absurd (hjt.trans hle) (not_le.mpr htdEarly)
  obtain ⟨hheld, hstampEq⟩ :=
    SGArrival.stateBefore_sg_row_stamp_mono S rho reader hij hpost
  have hstampJ : (NamedRun.stateBefore S rho j reader).st.core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (stamp : Stamp) := hstampEq.trans hstamp
  have hoccur : occurrenceBefore
      ((NamedRun.stateBefore S rho j reader).st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (early S.E S.hc r .g2) = true := by
    simp only [hstampJ, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr (hstampBound.trans_lt htdEarly)
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j reader).1.1.1
  have hrawPool : a.erase ∈ (NamedRun.stateBefore S rho j reader).st.core.sg_pool a.round :=
    NamedAdmission.pool_view_mem _ hcoh.2.2.2.1 a hheld
  have hsg : Protocol.sgVote a.erase ∈
      (NamedRun.stateBefore S rho j reader).st.core.toHealing.gradeView.sg_votes a.round :=
    Finset.mem_image_of_mem Protocol.sgVote hrawPool
  refine ⟨hheld, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_biUnion.mpr ⟨a.round, List.mem_toFinset.mpr hwindow, hsg⟩, rfl, hoccur⟩

/-! ## 3. An honest awake validator of a window round really emits a row -/

theorem honest_awake_emits (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (w : V) (hw : w ∈ rho.honest) (k : Round)
    (hawake : (S.node w).awake k = true) (hhor : S.a k ≤ rho.horizon) :
    ∃ a : NamedAttestation V, a.val_index = w ∧ a.round = k ∧
      NamedRun.emits S rho w (.attest a) (S.a k) := by
  have htick := sch.tick_total w hw (S.a k) (Proofs.HealingLemmas.publicTime_a S k)
    (Proofs.HealingLemmas.a_nonneg S k) hhor
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  refine ⟨(Protocol.NamedDuties.attest_with
      (NamedProfile.gradeContract (actionReadFrom S (NamedRun.stateBefore S rho i w) k).cache)
      S.E S.hc (S.node w) (actionReadFrom S (NamedRun.stateBefore S rho i w) k).st
      (actionReadFrom S (NamedRun.stateBefore S rho i w) k).record).2.2, S.node_val_index w,
    OutageInputs.action_read_round S (NamedRun.stateBefore S rho i w) k, i, hi, ?_⟩
  have hemit : NamedRun.emittedAt S rho i w (S.a k) =
      (Execution.NamedNode.tick S w (NamedRun.stateBefore S rho i w) (S.a k)).2 := rfl
  rw [hemit, OutageInputs.tick_at_action S w (NamedRun.stateBefore S rho i w) k]
  dsimp only
  simp only [if_pos hawake, List.mem_singleton]

/-! ## 4. B5 provenance

The positive supporter's maximal early token is the erasure of a full named
row the capture reader holds; that row is an honest emission of a window
round, and clause (0) of the joint history puts its confirmed key's named
block below `C`. -/

/-- Every SG vote in the capture reader's grade view is the projection of a
full named row it holds. -/
theorem gradeView_vote_row (S : Setup V) (rho : NamedRun V)
    (j : Nat) (v : V) (k : Round) {u : Protocol.SGVote V}
    (hu : u ∈ (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView.sg_votes k) :
    ∃ named : NamedAttestation V,
      named ∈ (NamedRun.stateBefore S rho j v).st.sg_rows k ∧
      Protocol.sgVote named.erase = u := by
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j v).1.1.1
  change u ∈ ((NamedRun.stateBefore S rho j v).st.core.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨b, hb, hbu⟩ := Finset.mem_image.mp hu
  obtain ⟨named, hn, hne⟩ :=
    SGArrival.pool_full_witness S (NamedRun.stateBefore S rho j v).st hcoh k b hb
  exact ⟨named, hn, by rw [hne]; exact hbu⟩


/-! ## 5. B4 open

Every honest awake validator of the window emits a row at its own action, the
healthy prefix delivers the row and its confirmed body to the capture reader
before the early G2 cutoff, and the row is then a ready token there. The
orientation between the reader's finalized root at the capture and the
emitter's confirmed head is not a free premise; it is derived by a case split
on the joint history: both blocks are named run blocks below the same witness
`C` (clause (0) `SGVoteOnHistory` for the confirmed head, clause (3) for the
reader's own finalized body), hence comparable
(`ViabilityHistoryTime.named_common_chain`). One orientation is the
original delivery route; the other lands the confirmed head already among the
reader's own held bodies (`ViabilityHistoryTime.ancestor_body_mem`), but
that only dates the arrival at the reader's own (4Δ-too-late) G2-domain read.
The fix renews clause (3) a second time, at the confirmed head's own arrival
DEADLINE `d:= S.a k + Δ` instead of the domain read: the same common-chain
split against `H` runs there too, and closes with no further premise either
through `ViabilityHistoryTime.ancestor_body_mem` (applied at the earlier
read) or through `NamedHealthyHeadReady.healthy_head_body_at_read` (the
delivery route, run at `targetRead = d`). The stamp obtained at the earlier
read then transports forward to the domain read unchanged
(`NamedBlockStamp.stateBefore_body_stamp_mono`: a stamp, once written, is
never rewritten). No further premise is needed. -/


theorem awake_window_row_head (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (w : V) (hw : w ∈ rho.honest) (k : Round)
    (hawake : (S.node w).awake k = true) (hhor : S.a k ≤ rho.horizon) :
    ∃ (i : Nat) (a : NamedAttestation V) (H : NamedBlock V),
      rho.events[i]? = some (.tick w (S.a k)) ∧
      NamedRun.emits S rho w (.attest a) (S.a k) ∧
      a.val_index = w ∧ a.round = k ∧
      H ∈ (NamedRun.stateBefore S rho i w).st.bodies ∧ a.confirmed = some H.root := by
  obtain ⟨a, hval, har, hem⟩ := honest_awake_emits S rho sch w hw k hawake hhor
  obtain ⟨i, hi, -, H, hH, hkey⟩ := OutageInputs.emitted_attestation_head S rho hem
  exact ⟨i, a, H, hi, hem, hval, har, hH, hkey⟩


#print axioms awake_window_row_head
#print axioms gradeView_vote_row
#print axioms action_delta_le_early_g2
#print axioms healthy_emitted_sg_raw_at_index
#print axioms honest_awake_emits
end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryB4B5Time

end
