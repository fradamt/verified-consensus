module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedAssembly

@[expose] public section

/-!
# The base-round frozen anchor and head floor

The round-ceiling step derives its boundary thin head from the previous
ceiling record (`roundCeiling_headThin`). A first ceiling has no predecessor,
so the same floor has to come from the protocol.

The argument is provenance, not persistence. After settling every honest read
of the round selects a fresh grade-1 anchor `A`. A grade-1 block carries more
weight than the fault bound, so it has an honest supporter whose previous
Section 7 SG action vote names a carrier above `A`. That carrier is active in
its author's own action store, so the author already held a processed block `W`
with `A ⪯ W` and height at least `M - 1` a full round earlier. One post-GST
relay puts `W` in every honest frozen vote view, which makes `W` a frozen
candidate and `A` its ancestor. The Goldfish walk therefore cannot stop below
the band.

The scenario the head floor has to exclude — a grade-1 anchor delivered inside
the last delay before the vote, hence outside the frozen view — cannot occur:
the anchor's own honest supporter held it a round earlier.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Under gate off at an exact frontier read, the selected FG root is the
finalized block. -/
private theorem seedBase_fgRoot_eq_finalized
    (S : Setup V) {rho : Run V} {w : V} {read : Time} {M : Height}
    (hfrontier : (rho.storeBeforeTime S w read).h_max = M)
    (hgate : (rho.storeBeforeTime S w read).h_j + 2 ≤ M) :
    Protocol.get_fg_root (rho.storeBeforeTime S w read).toHealing.toFG =
      (rho.storeBeforeTime S w read).F := by
  have hne : ¬ (rho.storeBeforeTime S w read).h_max =
      (rho.storeBeforeTime S w read).h_j + 1 := by
    apply Nat.ne_of_gt
    rw [hfrontier]
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgate)
  simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hne]

/-- The block-admission guard for a thin run block at a gate-off target. The
target's finalized block only grows, and at the cutoff read it is already below
every run block in the frontier band. -/
theorem seedBase_thinBlock_finalizedBelow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {M : Height} {W : NamedBlock V}
    (hWrun : RunBlock S rho W)
    (hWthin : M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h)
    {w : V} (hw : w ∈ rho.honest) {cut : Time}
    (hfrontier : (rho.storeBeforeTime S w cut).h_max = M)
    (hgate : (rho.storeBeforeTime S w cut).h_j + 2 ≤ M) :
    BlockFinalizedBelowAtDeliveriesBefore S rho w W cut := by
  intro i hi
  let n := strictEventIndex rho cut
  have hstore : rho.storeBeforeTime S w cut = (rho.stateBefore S n w).st := by
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed w cut]
  have hmono : Block.Preceq (rho.stateBefore S i w).st.F
      (rho.stateBefore S n w).st.F :=
    Protocol.stateBefore_F_mono S rho w
      (by simpa only [strictEventIndex] using hi)
  have hcutRoot : Block.Preceq (rho.storeBeforeTime S w cut).F W.erase := by
    rw [← seedBase_fgRoot_eq_finalized S hfrontier hgate]
    exact frontierRoot_preceq_of_gateOff S adm hsb hw
      (X := W.erase) (Xn := W) rfl hWrun hWthin hfrontier hgate
  exact Block.preceq_trans hmono (by rwa [hstore] at hcutRoot)

/-- One post-GST relay makes a thin run block held by an honest validator
visible and stamped in every honest strict store of a gate-off window. -/
theorem thinBlock_visible_and_stamped_after_oneDelay
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {M : Height} {W : NamedBlock V} {holder w : V}
    (hholder : holder ∈ rho.honest) (hw : w ∈ rho.honest)
    {source cut read : Time}
    (hsource : W ∈ (rho.storeBeforeTime S holder source).bodies)
    (hWrun : RunBlock S rho W)
    (hWthin : M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h)
    (hpost : S.E.t_GST ≤ source)
    (hhop : source + S.E.Δ = cut)
    (hcutRead : cut ≤ read)
    (hhor : cut ≤ rho.horizon)
    (hfrontier : (rho.storeBeforeTime S w cut).h_max = M)
    (hgate : (rho.storeBeforeTime S w cut).h_j + 2 ≤ M) :
    W.erase ∈ (rho.storeBeforeTime S w read).T ∧
      (W.erase = Block.genesis ∨
        stampedBefore (rho.storeBeforeTime S w read).timestamp_block cut
          W.erase = true) := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed source
  have hsourceN : W ∈ (rho.stateBefore S n holder).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hsource
  have hprocessed : Object.processed (rho.stateBefore S n holder).st
      (Object.block W) = true := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq] using hsourceN
  rcases Protocol.acceptsAt_block_of_processed
      S rho holder n W hprocessed with hgen | ⟨i, hi, ta, hacc⟩
  · refine ⟨?_, Or.inl ?_⟩
    simpa only [hgen, NamedBlock.erase] using
      (Protocol.genesis_mem_and_stamp_storeBeforeTime
        S adm.toNamedScheduleWellFormed w read read).1
    simpa only [hgen, NamedBlock.erase]

  · have hta : ta < source := by
      obtain ⟨_, ⟨e, he, _, het⟩⟩ := hacc.1
      simpa only [het] using hbefore i e hi he
    have hWpos : 0 < W.slot := by
      simpa only [Proofs.NamedWire.erase_slot] using
        (Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hacc))
    have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho w W cut :=
      seedBase_thinBlock_finalizedBelow S adm hsb hWrun hWthin hw
        hfrontier hgate
    have hadmit : Protocol.AdmittedBefore S rho w W.erase cut :=
      Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hholder hw hWpos hacc hta hpost hhop hhor hFhist
    have hvisible := Protocol.admittedBefore_mem_and_stamp_at
      S adm.toNamedScheduleWellFormed hadmit hcutRead
    exact ⟨hvisible.1, Or.inr hvisible.2⟩


/-! ## Grade-1 provenance at an arbitrary in-round read -/




/-
/-! ## The base-round head floor -/

/-- At a gate-off vote duty of round `k + 1` whose SG anchor is a fresh
grade-1 anchor, the honest Goldfish head reaches the local viability boundary.

No previous ceiling record is used. The frozen candidate that carries the walk
is the provenance witness of the anchor itself: the anchor's honest grade
supporter already held it at the round-`k` action, one full relay before the
view freeze of the duty. The scenario the floor has to exclude, a grade-1
anchor delivered inside the last delay and therefore outside the frozen view,
cannot occur for that reason. -/
theorem seedBoundaryHeadThin_of_freshAnchor
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {k: Round} {s: Slot}
    (hround: S.hc.round_of (s + 1) = k + 1)
    (hpost: S.E.t_GST ≤ S.a k)
    (hhor: S.a k + S.E.Δ ≤ rho.horizon)
    (hfreeze: S.a k + S.E.Δ ≤ Protocol.view_freeze S.E s)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hprevFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k)).h_max = M)
    (hcutFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k + S.E.Δ)).h_max = M)
    (hcutGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k + S.E.Δ)).h_j + 2 ≤ M)
    (hfrontier: ∀ u ∈ rho.honest,
      (voteDutyStore S rho u (s + 1)).h_max = M)
    (hgate: ∀ u ∈ rho.honest,
      (voteDutyStore S rho u (s + 1)).h_j + 2 ≤ M)
    {w: V} (hw: w ∈ rho.honest)
    {A: Block V}
    (hA: Protocol.fresh_anchor S.E S.hc
      (voteDutyStore S rho w (s + 1)).toHealing (k + 1) = some A):
    M - 1 ≤ (derived_state S.E S.cfg (voteDutyHead S rho w (s + 1))).h:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hfreezeVote: Protocol.view_freeze S.E s <
      Protocol.vote_time S.E (s + 1):=
    Protocol.view_freeze_lt_vote_time_succ S.E s
  have hcutVote: S.a k + S.E.Δ ≤ Protocol.vote_time S.E (s + 1):=
    hfreeze.trans (le_of_lt hfreezeVote)
  have hM: 1 ≤ M:=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans
      ((Nat.le_add_left 2 (voteDutyStore S rho w (s + 1)).h_j).trans
        (hgate w hw))
  have hAdata:= Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA)
  have hAG1': Protocol.G1 S.E
      (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (s + 1))).toHealing.gradeView
        S.hc (k + 1) A = true:= by
    simpa only [voteDutyStore, voteStore, tickStore] using hAdata.2
  obtain ⟨v, hv, hAC⟩:= G1_preceq_honestPreviousActionCarrier_atRead
    S adm hfb hw k hpost hhor hcutVote hAG1'
  obtain ⟨W, hWT, hCW, hWthin⟩:=
    actionSGBlockAt_frontierWitness S adm (hprevFrontier v hv)
  have hAW: Block.Preceq A W:= Block.preceq_trans hAC hCW
  have hWpre: W ∈ (rho.storeBeforeTime S v (S.a k)).T:= by
    have hfields:= Proofs.Optimistic.attestStore_fields S
      (rho.stateBeforeTime S (S.a k) v).st (S.a k)
    simpa only [actionStoreAt, hfields.2.1, Run.storeBeforeTime] using hWT
  have hWrun: RunBlock S rho W:= by
    obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toScheduleWellFormed (S.a k)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= n)
    rw [← hn]
    simpa only [Run.storeBeforeTime] using hWpre
  have hrelay:= thinBlock_visible_and_stamped_after_oneDelay
    S adm hsb hv hw hWpre hWrun hWthin hpost rfl hcutVote hhor
    (hcutFrontier w hw) (hcutGate w hw)
  have hWmemPre: W ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).T:= hrelay.1
  have hWfiltered: W ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho w (s + 1)).toHealing.toFG:= by
    have hres:= frontierBlock_filtered_of_gateOff S adm hsb hw hvoteHor
      hWmemPre hWrun hWthin hM
      (by simpa only [voteDutyStore, voteStore, tickStore] using
        hfrontier w hw)
      (by simpa only [voteDutyStore, voteStore, tickStore] using hgate w hw)
    simpa only [voteDutyStore, voteStore, tickStore] using hres
  have hslot: (voteDutyStore S rho w (s + 1)).toHealing.s = s + 1:=
    voteDutyStore_slot S rho w (s + 1)
  have hstampFreeze: stampedBefore
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore.timestamp_block
      (Protocol.view_freeze S.E s) W = true:= by
    rcases hrelay.2 with hgen | hstamp
    · have hgenesis:= Protocol.genesis_mem_and_stamp_storeBeforeTime
        S adm.toScheduleWellFormed w (Protocol.vote_time S.E (s + 1))
        (Protocol.view_freeze S.E s)
      rw [hgen]
      simpa only [voteDutyStore, voteStore, tickStore,
        Protocol.Store.toHealing] using hgenesis.2
    · have hstamp': stampedBefore
          (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore.timestamp_block
          (S.a k + S.E.Δ) W = true:= by
        simpa only [voteDutyStore, voteStore, tickStore,
          Protocol.Store.toHealing] using hstamp
      rw [stampedBefore_eq_occurrenceBefore] at hstamp' ⊢
      exact occurrenceBefore_mono hfreeze hstamp'
  have hWprocessed: W ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s:= by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    refine ⟨?_, Or.inl hstampFreeze⟩
    simpa only [voteDutyStore, voteStore, tickStore,
      Protocol.Store.toHealing] using hWmemPre
  have hmax: (voteDutyStore S rho w (s + 1)).h_max ≤
      (derived_state S.E S.cfg W).h + 1:= by
    rw [hfrontier w hw]
    exact Nat.sub_le_iff_le_add.mp hWthin
  have hanchorEq: Proofs.Optimistic.healAnchor S.E S.hc
      (voteDutyStore S rho w (s + 1)).toHealing = A:= by
    rw [Proofs.Optimistic.healAnchor_eq_get_sg_root, hslot, hround]
    simp only [Protocol.get_sg_root, hA]
  have hanchorW: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (voteDutyStore S rho w (s + 1)).toHealing) W:= by
    rw [hanchorEq]
    exact hAW
  have hinputs: GoldfishConeVoteInputs S rho s W w:=
    { candidate:= ancestorCandidate_of_processedDescendant_and_hMax
        S adm hw hWprocessed (Block.preceq_self W) hWfiltered hmax
      root:= Proofs.Records.preceq_get_fg_root_of_mem_filtered hWfiltered
      anchor:= by
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inl hanchorW
      path:= by
        intro D hanchorD hne hDW _
        have hDfiltered:= Protocol.votePath_of_candidate
          S adm hWfiltered D hanchorD hne hDW
        exact ancestorCandidate_of_processedDescendant_and_hMax
          S adm hw hWprocessed hDW hDfiltered hmax }
  have hfloor:= voteDutyHead_height_ge_frontier_sub_one_of_candidate
    S adm hw hinputs hanchorW
  rwa [hfrontier w hw] at hfloor

/-- The base-round boundary thin head. A block below every honest fresh
grade-1 anchor of the duty is below an honest vote head that reaches the local
viability boundary. This is the `boundaryThinHead` field of a first
`RoundCeilingBoundaryConeAt`, obtained without a predecessor record. -/
theorem seedBoundaryThinHead_of_freshAnchors
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {k: Round} {s: Slot}
    (hround: S.hc.round_of (s + 1) = k + 1)
    (hpost: S.E.t_GST ≤ S.a k)
    (hhor: S.a k + S.E.Δ ≤ rho.horizon)
    (hfreeze: S.a k + S.E.Δ ≤ Protocol.view_freeze S.E s)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hprevFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k)).h_max = M)
    (hcutFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k + S.E.Δ)).h_max = M)
    (hcutGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k + S.E.Δ)).h_j + 2 ≤ M)
    (hfrontier: ∀ u ∈ rho.honest,
      (voteDutyStore S rho u (s + 1)).h_max = M)
    (hgate: ∀ u ∈ rho.honest,
      (voteDutyStore S rho u (s + 1)).h_j + 2 ≤ M)
    {C: Block V}
    (hanchors: ∀ u ∈ rho.honest, ∃ A: Block V,
      Protocol.fresh_anchor S.E S.hc
          (voteDutyStore S rho u (s + 1)).toHealing (k + 1) = some A ∧
        Block.Preceq C A):
    ThinHonestHeadAt S rho M (s + 1) C:= by
  have hpositive: 0 < ((S.E.committee (s + 1)) ∩ rho.honest).card:= by
    have hc:= hcom (s + 1)
    omega
  obtain ⟨w, hwmem⟩:= Finset.card_pos.mp hpositive
  have hwCommittee: w ∈ S.E.committee (s + 1):=
    (Finset.mem_inter.mp hwmem).1
  have hw: w ∈ rho.honest:= (Finset.mem_inter.mp hwmem).2
  obtain ⟨A, hA, hCA⟩:= hanchors w hw
  have hanchorEq: Proofs.Optimistic.healAnchor S.E S.hc
      (voteDutyStore S rho w (s + 1)).toHealing = A:= by
    rw [Proofs.Optimistic.healAnchor_eq_get_sg_root,
      show (voteDutyStore S rho w (s + 1)).toHealing.s = s + 1 from
        voteDutyStore_slot S rho w (s + 1), hround]
    simp only [Protocol.get_sg_root, hA]
  have hAX: Block.Preceq A (voteDutyHead S rho w (s + 1)):= by
    rw [← hanchorEq, Proofs.Optimistic.healAnchor_eq_get_sg_root]
    exact get_sg_root_preceq_get_head_in_tree S.E S.hc
      (voteDutyStore S rho w (s + 1))
      (Protocol.voter_filtered_block_tree S.E
        (voteDutyStore S rho w (s + 1))
        (voteDutyStore S rho w (s + 1)).s)
      (Protocol.voter_view S.E
        (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w (s + 1)).toHealing.s)
      (Protocol.voter_support_view S.E
        (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w (s + 1)).toHealing.s)
      ((voteDutyStore S rho w (s + 1)).toHealing.s - 1)
  have hXrun: RunBlock S rho (voteDutyHead S rho w (s + 1)):= by
    simpa only [voteDutyHead] using voteDutyHead_runBlock S adm hw (s + 1)
  have hXemit:= seedVoteDutyHead_emits S adm hw (Nat.succ_pos s)
    hwCommittee hvoteHor
  exact ⟨voteDutyHead S rho w (s + 1),
    ⟨w, hw, hwCommittee, hXrun, hXemit⟩,
    Block.preceq_trans hCA hAX,
    seedBoundaryHeadThin_of_freshAnchor S adm hfb hround hpost hhor hfreeze
      hvoteHor hprevFrontier hcutFrontier hcutGate hfrontier hgate hw hA⟩

/-! ## The base-round schedule margin -/

/-- The round-`k` action relay lands before the view freeze of the slot that
precedes the last vote duty of round `k + 1`. With `a_k = 4Δ·kR + 6Δ` and the
freeze at `4Δ(kR + 2R - 2) + 3Δ`, the margin is `4Δ` or more for `R ≥ 2`.
This is the timing side condition of the base-round head floor. -/
theorem seedBase_actionDelay_le_viewFreeze
    (S: Setup V) (k: Round):
    S.a k + S.E.Δ ≤
      Protocol.view_freeze S.E (seedRoundLastSlot S (k + 1) - 1):= by
  have hR: 2 ≤ S.hc.R:= S.hc.R_ge_two
  have hexpand: (k + 2) * S.hc.R = k * S.hc.R + 2 * S.hc.R:= by
    rw [Nat.add_mul]
  have hslot: seedRoundLastSlot S (k + 1) - 1 = (k + 2) * S.hc.R - 2:= by
    unfold seedRoundLastSlot Protocol.HealConfig.opening_slot
    exact Nat.sub_sub _ 1 1
  have hgeGen: ∀ a: Nat, a + 2 ≤ a + 2 * S.hc.R - 2:= by
    intro a
    omega
  have hge: k * S.hc.R + 2 ≤ (k + 2) * S.hc.R - 2:= by
    rw [hexpand]
    exact hgeGen (k * S.hc.R)
  have hcast: ((k * S.hc.R: ℕ): Time) + 2 ≤
      (((k + 2) * S.hc.R - 2: ℕ): Time):= by
    have hnat:= (Nat.cast_le (α:= Time)).mpr hge
    push_cast at hnat
    exact hnat
  have hΔ: (0: Time) < S.E.Δ:= S.E.Δ_pos
  have hcoef: (0: Time) ≤ 4 * S.E.Δ:=
    Int.mul_nonneg (by decide) (le_of_lt hΔ)
  have hstep: 4 * S.E.Δ * ((k * S.hc.R: ℕ): Time) + 8 * S.E.Δ ≤
      4 * S.E.Δ * (((k + 2) * S.hc.R - 2: ℕ): Time):= by
    have hmul:= Int.mul_le_mul_of_nonneg_left hcast hcoef
    calc 4 * S.E.Δ * ((k * S.hc.R: ℕ): Time) + 8 * S.E.Δ
        = 4 * S.E.Δ * (((k * S.hc.R: ℕ): Time) + 2):= by ring
      _ ≤ _:= hmul
  have hA: S.a k + S.E.Δ =
      4 * S.E.Δ * ((k * S.hc.R: ℕ): Time) + 7 * S.E.Δ:= by
    simp only [Setup.a, Protocol.a_eq_confirmation_time,
      Protocol.confirmation_time, Env.t, slotStart,
      Protocol.HealConfig.opening_slot]
    ring
  have hF: Protocol.view_freeze S.E (seedRoundLastSlot S (k + 1) - 1) =
      4 * S.E.Δ * (((k + 2) * S.hc.R - 2: ℕ): Time) + 3 * S.E.Δ:= by
    rw [hslot]
    simp only [Protocol.view_freeze, Env.t, slotStart]
  rw [hA, hF]
  have hseven: (7: Time) * S.E.Δ ≤ 11 * S.E.Δ:=
    Int.mul_le_mul_of_nonneg_right (by decide) (le_of_lt hΔ)
  calc 4 * S.E.Δ * ((k * S.hc.R: ℕ): Time) + 7 * S.E.Δ
      ≤ 4 * S.E.Δ * ((k * S.hc.R: ℕ): Time) + 11 * S.E.Δ:=
        Int.add_le_add_left hseven _
    _ = (4 * S.E.Δ * ((k * S.hc.R: ℕ): Time) + 8 * S.E.Δ) + 3 * S.E.Δ:= by
        ring
    _ ≤ 4 * S.E.Δ * (((k + 2) * S.hc.R - 2: ℕ): Time) + 3 * S.E.Δ:=
        Int.add_le_add_right hstep _

/-! ## Fresh grade-1 anchors at the boundary duty -/

/-- A block that forms the round-`(k+1)` grade and is still active at an honest
vote duty of that round makes the duty's fresh anchor exist and dominate it.
This is what removes the raw relative-majority fallback at the boundary. -/
theorem freshAnchor_at_voteDuty_of_gradeFormsAt
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {k: Round} {B: Block V} (hforms: GradeFormsAt S rho (k + 1) B)
    {s: Slot} (hround: S.hc.round_of s = k + 1)
    {v: V} (hv: v ∈ rho.honest)
    (hactive: B ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho v s).toHealing.toFG):
    ∃ A: Block V,
      Protocol.fresh_anchor S.E S.hc
          (voteDutyStore S rho v s).toHealing (k + 1) = some A ∧
        Block.Preceq B A:= by
  have hG1: Protocol.G1 S.E
      (voteDutyStore S rho v s).toHealing.gradeView S.hc (k + 1) B = true:=
    g1_at_voteDuty_of_gradeFormsAt S adm hforms hround hv
  obtain ⟨A, hA⟩:= Option.isSome_iff_exists.mp
    (fresh_anchor_isSome_of_G1 S.E hactive hG1)
  refine ⟨A, hA, ?_⟩
  refine deepest?_dominates hA (Finset.mem_filter.mpr ⟨hactive, hG1⟩) ?_
  exact G1_compatible S.E hG1
    (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA)).2

/-- The base-round boundary thin head from a common round-`(k+1)` grade block
that is still active at every honest boundary duty. This is the
`boundaryThinHead` field of a first `RoundCeilingBoundaryConeAt` for any
candidate ceiling below the grade block. -/
theorem seedBoundaryThinHead_of_gradeFormsAt
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {k: Round} {s: Slot}
    (hround: S.hc.round_of (s + 1) = k + 1)
    (hpost: S.E.t_GST ≤ S.a k)
    (hhor: S.a k + S.E.Δ ≤ rho.horizon)
    (hfreeze: S.a k + S.E.Δ ≤ Protocol.view_freeze S.E s)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hprevFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k)).h_max = M)
    (hcutFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k + S.E.Δ)).h_max = M)
    (hcutGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a k + S.E.Δ)).h_j + 2 ≤ M)
    (hfrontier: ∀ u ∈ rho.honest,
      (voteDutyStore S rho u (s + 1)).h_max = M)
    (hgate: ∀ u ∈ rho.honest,
      (voteDutyStore S rho u (s + 1)).h_j + 2 ≤ M)
    {B C: Block V}
    (hforms: GradeFormsAt S rho (k + 1) B)
    (hactive: ∀ u ∈ rho.honest,
      B ∈ Protocol.get_filtered_block_tree
        (voteDutyStore S rho u (s + 1)).toHealing.toFG)
    (hCB: Block.Preceq C B):
    ThinHonestHeadAt S rho M (s + 1) C:= by
  refine seedBoundaryThinHead_of_freshAnchors S adm hcom hfb hround hpost hhor
    hfreeze hvoteHor hprevFrontier hcutFrontier hcutGate hfrontier hgate ?_
  intro u hu
  obtain ⟨A, hA, hBA⟩:= freshAnchor_at_voteDuty_of_gradeFormsAt
    S adm hforms hround hu (hactive u hu)
  exact ⟨A, hA, Block.preceq_trans hCB hBA⟩

/-! ## The selector tiers under a selected grade 2 -/

/-- With a selected grade-2 block at the action store, the raw SG-root tier of
`get_sg_vote` is unreachable: the clear walk either returns a block below the
recorded live confirmation, or it is empty and the selector takes the grade-2
fallback. This is the tier list the first-ceiling frontier has to dominate. -/
theorem seedActionCarrier_classification_of_selectedG2
    (S: Setup V) (rho: Run V) {r: Round} {v: V}
    (hselected: ∃ Q: Block V, Protocol.grade2_block S.E S.hc
      (actionStoreAt S rho v r).toHealing r = some Q):
    (∃ D: Block V,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
          (confStore S rho v (S.hc.opening_slot r))
          (S.hc.opening_slot r) D ∧
        Block.Preceq (actionSGBlockAt S rho v r) D) ∨
    Block.Preceq (actionSGBlockAt S rho v r)
      (Protocol.get_fg_root
        (confStore S rho v (S.hc.opening_slot r)).toHealing.toFG) ∨
    ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
          (actionStoreAt S rho v r).toHealing r = some Q ∧
        actionSGBlockAt S rho v r = Q:= by
  cases hwalk: Protocol.deepest_clear
      (some (Protocol.get_sg_root S.E S.hc
        (actionStoreAt S rho v r).toHealing r))
      (actionStoreAt S rho v r).toHealing.live_confirmed
      (fun B => Protocol.g0_clear S.E
        (actionStoreAt S rho v r).toHealing.gradeView S.hc r B) with
  | some B =>
      have hcarrier: actionSGBlockAt S rho v r = B:= by
        unfold actionSGBlockAt
        rw [Protocol.get_sg_vote.eq_def, hwalk]
      have hBlive: Block.Preceq B
          (actionStoreAt S rho v r).toHealing.live_confirmed:=
        Proofs.Engine.deepest_clear_preceq hwalk
      rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v r with
        hgen | hroot
      · obtain ⟨D, hD, hDeq⟩:= hgen
        refine Or.inl ⟨D, hD, ?_⟩
        rw [hcarrier, hDeq]
        exact hBlive
      · obtain ⟨R, hReq, hReeq⟩:= hroot
        refine Or.inr (Or.inl ?_)
        rw [hcarrier, ← hReq, hReeq]
        exact hBlive
  | none =>
      obtain ⟨Q, hQ⟩:= hselected
      exact Or.inr (Or.inr ⟨Q, hQ,
        actionSGBlockAt_eq_selectedG2_of_noClear S rho hwalk hQ⟩)

/-- Under a selected grade 2 at every honest action store and a common
confirmation-store FG root, every honest round-`r` SG action carrier is below
the common root, below a genuine opening confirmation, or is a selected
grade-2 block. This is `previousCarriers` for a frontier that dominates the
genuine outputs and the selected grade-2 blocks. -/
theorem seedActionCarriers_preceq_of_selectedG2_of_commonRoot
    (S: Setup V) (rho: Run V) {r: Round} {F Cstar: Block V}
    (hselected: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v r).toHealing r = some Q)
    (hroot: ∀ v ∈ rho.honest,
      Protocol.get_fg_root
        (confStore S rho v (S.hc.opening_slot r)).toHealing.toFG = F)
    (hF: Block.Preceq F Cstar)
    (hgenuine: ∀ v ∈ rho.honest, ∀ D: Block V,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
          (confStore S rho v (S.hc.opening_slot r))
          (S.hc.opening_slot r) D →
        Block.Preceq D Cstar)
    (hgrade: ∀ v ∈ rho.honest, ∀ Q: Block V,
      Protocol.grade2_block S.E S.hc
          (actionStoreAt S rho v r).toHealing r = some Q →
        Block.Preceq Q Cstar):
    ∀ v ∈ rho.honest, Block.Preceq (actionSGBlockAt S rho v r) Cstar:= by
  intro v hv
  rcases seedActionCarrier_classification_of_selectedG2 S rho
      (hselected v hv) with hconf | hrootTier | hg2
  · obtain ⟨D, hD, hle⟩:= hconf
    exact Block.preceq_trans hle (hgenuine v hv D hD)
  · refine Block.preceq_trans hrootTier ?_
    rw [hroot v hv]
    exact hF
  · obtain ⟨Q, hQ, heq⟩:= hg2
    rw [heq]
    exact hgrade v hv Q hQ

/-! ## Cross-store grade transport -/

/-- A selected grade-2 block of one honest action store is below the fresh
grade-1 anchor of every honest action store of the same round.

This is the cross-store step that was buried in the private proof of
`selectedFallback_compatible_actionCarrier`. In the root arm of the settling
invariant the grade-2 block is below the reader's FG root, hence below its SG
root; in the active arm honest grade delivery turns the grade 2 at the source
into a grade 1 at the reader, and the fresh anchor is the deepest active
grade 1. -/
theorem selectedG2_preceq_freshAnchor_of_settled
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} (hready: GradeRoundReady S rho r)
    (hsettled: SelectedG2SettledAt S rho r)
    {u v: V} (hu: u ∈ rho.honest) (hv: v ∈ rho.honest)
    {Q A: Block V}
    (hQ: Protocol.grade2_block S.E S.hc
      (actionStoreAt S rho u r).toHealing r = some Q)
    (hA: Protocol.fresh_anchor S.E S.hc
      (actionStoreAt S rho v r).toHealing r = some A):
    Block.Preceq Q A:= by
  have hsgRoot: Protocol.get_sg_root S.E S.hc
      (actionStoreAt S rho v r).toHealing r = A:= by
    simp only [Protocol.get_sg_root, hA]
  rcases hsettled u hu Q hQ v hv with hroot | hactive
  · have hrootAction: Block.Preceq Q
        (Protocol.get_fg_root
          (actionStoreAt S rho v r).toHealing.toFG):= by
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v r]
      exact hroot
    exact Block.preceq_trans hrootAction
      (Proofs.Records.fresh_anchor_root_preceq S.E S.hc
        (actionStoreAt S rho v r).toHealing r hA)
  · have hactiveAction: Q ∈ Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG:= by
      rw [actionStoreAt_filteredTree S rho v r]
      exact hactive
    have hactiveGrade: Q ∈ (gradeViewAt S rho v r).tree:= by
      simpa only [gradeViewAt, healStoreAt, Protocol.HealingStore.gradeView]
        using hactive
    have hG2Action: Protocol.G2 S.E
        (actionStoreAt S rho u r).toHealing.gradeView S.hc r Q = true:=
      (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hQ)).2
    have hG2Source: Protocol.G2 S.E (gradeViewAt S rho u r) S.hc r Q = true:= by
      rw [gradeViewAt, healStoreAt,
        ← Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho u r]
      exact hG2Action
    have hdelivery:=
      GradeDeliveryRun.honestGradeDelivery_of_admissible S adm hready
    have hG1Target: Protocol.G1 S.E (gradeViewAt S rho v r) S.hc r Q = true:=
      G2_imp_G1_delivered S.E (hdelivery u hu v hv) hactiveGrade hG2Source
    have hG1Action: Protocol.G1 S.E
        (actionStoreAt S rho v r).toHealing.gradeView S.hc r Q = true:= by
      rw [Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho v r]
      simpa only [gradeViewAt, healStoreAt] using hG1Target
    refine deepest?_dominates hA
      (Finset.mem_filter.mpr ⟨hactiveAction, hG1Action⟩) ?_
    exact G1_compatible S.E hG1Action
      (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA)).2

/-- The fresh grade-1 anchor read at the round-`r` action instant is the one
read at the opening confirmation of the same round. `update_confirmation`
writes only the confirmation fields, so the finality-filtered tree and the
grade view agree at the two reads and `fresh_anchor` cannot move. -/
theorem freshAnchor_action_eq_openingConfirmation
    (S: Setup V) (rho: Run V) (v: V) (r: Round):
    Protocol.fresh_anchor S.E S.hc (actionStoreAt S rho v r).toHealing r =
      Protocol.fresh_anchor S.E S.hc
        (confStore S rho v (S.hc.opening_slot r)).toHealing r:= by
  rw [actionStoreAt_eq_update_confirmation_openingConfStore]
  rfl

/-- Every selected grade-2 block of an honest action store is below every
genuine opening confirmation of the same round. The two anchors involved are
the same block: the action read and the opening confirmation read differ only
by `update_confirmation`. -/
theorem selectedG2_preceq_genuineOpeningConfirmation
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} (hready: GradeRoundReady S rho r)
    (hsettled: SelectedG2SettledAt S rho r)
    {u v: V} (hu: u ∈ rho.honest) (hv: v ∈ rho.honest)
    {Q A D: Block V}
    (hQ: Protocol.grade2_block S.E S.hc
      (actionStoreAt S rho u r).toHealing r = some Q)
    (hA: Protocol.fresh_anchor S.E S.hc
      (actionStoreAt S rho v r).toHealing r = some A)
    (hD: GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
      (confStore S rho v (S.hc.opening_slot r)) (S.hc.opening_slot r) D):
    Block.Preceq Q D:= by
  have hQA:= selectedG2_preceq_freshAnchor_of_settled S adm hready hsettled
    hu hv hQ hA
  have hround: S.hc.round_of (S.hc.opening_slot r + 1) = r:= by
    have hR: 2 ≤ S.hc.R:= S.hc.R_ge_two
    have hgen: ∀ a: Nat, a + 1 < a + S.hc.R:= by
      intro a
      omega
    apply round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
    · exact le_refl _
    · change r * S.hc.R + 1 < (r + 1) * S.hc.R
      rw [Nat.add_mul, Nat.one_mul]
      exact hgen (r * S.hc.R)
  have hslot: (confStore S rho v (S.hc.opening_slot r)).s =
      S.hc.opening_slot r + 1:= by
    simp only [confStore, tickStore, Proofs.Optimistic.slotOf_confirmation_time]
  have hAconf: confAnchor S.E S.hc
      (confStore S rho v (S.hc.opening_slot r)) = A:= by
    have heq: Protocol.fresh_anchor S.E S.hc
        (confStore S rho v (S.hc.opening_slot r)).toHealing r = some A:= by
      rw [← freshAnchor_action_eq_openingConfirmation S rho v r]
      exact hA
    rw [confAnchor, hslot, hround]
    simp only [Protocol.get_sg_root, heq]
  have hanchorWalk: Block.Preceq
      (confAnchor S.E S.hc (confStore S rho v (S.hc.opening_slot r)))
      (confWalk S.E S.hc (confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r)):= by
    exact Protocol.ghost_preceq _ _ _ _
  rw [hAconf, hD.walk_eq] at hanchorWalk
  exact Block.preceq_trans hQA hanchorWalk

end HealingSurface
end Proofs
end DecoupledConsensusModel
-/

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms seedBase_thinBlock_finalizedBelow
#print axioms thinBlock_visible_and_stamped_after_oneDelay
end DecoupledConsensusModel.Proofs.HealingSurface

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
