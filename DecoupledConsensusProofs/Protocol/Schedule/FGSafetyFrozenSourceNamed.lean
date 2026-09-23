module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGSafetySourceNamed

@[expose] public section

/-!
# Named healed-height witnesses in the prepared frozen voter view

The prepared vote read has the same core block store and stamps as the strict
read at the vote instant. A regime seed emitted before that vote is already
present at the preceding freeze, so it belongs to the processed tree used by
the prepared voter.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem frozen_runBlock_of_action_body
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈
      (NamedRun.stateBeforeTime S rho (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨j, hj, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDj : D ∈ (rho.stateBefore S j v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho j v).st.bodies
    rw [← hj]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv j hDj)

private theorem NamedHeightRegimeRun.frozenSourceMem_at_read
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {read : Time} (hread : S.a a.round ≤ read)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (rho.storeBeforeTime S w read).bodies := by
  have hsource := h.seed.sourceMem_at_action_of_frame_named
    adm h.frame h.ready hw
  have hsourcePre : Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hsource
  have heqSource := congrFun
    (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed (S.a a.round)) w
  have heqRead := congrFun
    (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed read) w
  rw [heqSource] at hsourcePre
  have hCfgRead : Cfg ∈
      (NamedRun.stateBeforeTime S rho read w).st.bodies := by
    rw [heqRead]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hsourcePre
  simpa only [Run.storeBeforeTime] using hCfgRead

/-- The regime seed body persists to every later honest read. -/
theorem NamedHeightRegimeRun.sourceMem_at_read_named
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {read : Time} (hread : S.a a.round ≤ read)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (rho.storeBeforeTime S w read).bodies :=
  h.frozenSourceMem_at_read adm hread hw

omit [DecidableEq V] [Fintype V] in
private theorem frozen_named_height_of_matches_source
    {a : NamedAttestation V} {H : Height} {root : BlockId}
    (hmatch : NamedHeightPair.matchesEntry H root a.height_pair = true) :
    a.height_pair.erase.height? = some H := by
  cases hp : a.height_pair with
  | empty =>
      simp [hp, NamedHeightPair.matchesEntry] at hmatch
  | vote height entry timeout =>
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hmatch
      cases timeout <;>
        simp [NamedHeightPair.erase, HeightPair.height?, hmatch.1]

omit [Fintype V] in
private theorem frozen_named_row_mem_chain_of_ancestor_source
    {A B : NamedBlock V} {a : NamedAttestation V}
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations B := by
  induction B generalizing A with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      subst A
      simp [NamedBlock.attestations] at ha
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      simp only [Protocol.named_chain_attestations, Finset.mem_union,
        List.mem_toFinset]
      rcases hAB with rfl | hparent
      · exact Or.inr ha
      · exact Or.inl (ih hparent ha)

/-- An action strictly before a vote also precedes the previous slot's
freeze. -/
theorem action_lt_previousFreeze_of_lt_vote_named
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : S.a r < Protocol.vote_time S.E s) :
    S.a r < Protocol.view_freeze S.E (s - 1) := by
  have hslot : S.hc.opening_slot r + 1 < s := by
    by_contra hnot
    have hle := Protocol.vote_time_mono_slots S.E (Nat.le_of_not_gt hnot)
    exact (not_lt_of_ge hle) ((next_vote_time_lt_action S r).trans hlt)
  have hle : S.hc.opening_slot r + 1 ≤ s - 1 :=
    Nat.le_sub_of_add_le (Nat.succ_le_of_lt hslot)
  calc
    S.a r = Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) :=
      Protocol.a_eq_support_cutoff_succ S.hc S.E r
    _ ≤ Protocol.support_cutoff S.E (s - 1) := support_cutoff_mono S.E hle
    _ < Protocol.view_freeze S.E (s - 1) := support_cutoff_lt_view_freeze S.E _

private theorem previousFreeze_lt_vote_named
    (S : Setup V) {s : Slot} (hs : 1 ≤ s) :
    Protocol.view_freeze S.E (s - 1) < Protocol.vote_time S.E s := by
  simpa only [Nat.sub_add_cancel hs] using view_freeze_lt_vote_time_succ S.E (s - 1)

/-- A block in the strict preceding-freeze store belongs to the processed
tree of the prepared vote read. -/
theorem voterProcessed_mem_of_mem_previousFreeze_named
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {s : Slot} (hs : 1 ≤ s) {u : V} {B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S u
      (Protocol.view_freeze S.E (s - 1))).T) :
    B ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyRead S rho u s).st.core.toHealing.toFG.toSG.toGoldfishStore s := by
  have htransport : B ∈
        (rho.storeBeforeTime S u (Protocol.vote_time S.E s)).T ∧
      stampedBefore
        (rho.storeBeforeTime S u
          (Protocol.vote_time S.E s)).timestamp_block
        (Protocol.view_freeze S.E (s - 1)) B = true := by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
        S sch u _ hB with hgen | hadmit
    · subst B
      exact genesis_mem_and_stamp_storeBeforeTime S sch u _ _
    · obtain ⟨D, i, t, hDerase, hacc, ht⟩ := hadmit
      exact admittedBefore_mem_and_stamp_at S sch
        ⟨D, hDerase, i, t, hacc, ht⟩
        (previousFreeze_lt_vote_named S hs).le
  simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
    Run.storeBeforeTime, Protocol.voter_processed_block_tree,
    Finset.mem_filter] using ⟨htransport.1, Or.inl htransport.2⟩

namespace NamedHeightRegimeBaseRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first : Nat} {Tprev : NamedBlock V}

/-- A crossing at the prepared next-vote read supplies a processed frozen
descendant of a lower named ancestor of an honest previous head. -/
theorem exists_frozen_descendant_at_crossing_of_previousHead_named
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {s : Slot}
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C X : NamedBlock V} (hCrun : RunBlock S rho C)
    (hC : Block.Preceq C.erase (voterHeadAt S rho v s))
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1)
    (hX : X ∈ (voteDutyRead S rho u (s + 1)).st.bodies)
    (hcross : blocked + n + 1 <
      (Protocol.derive_named S.E S.cfg X).h) :
    ∃ Y : NamedBlock V, RunBlock S rho Y ∧
      Y.erase ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyRead S rho u (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1) ∧
      Block.Preceq C.erase Y.erase ∧
      (Protocol.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  obtain ⟨K, hKX, hKheight, Q, hQ, hwit⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg X
      (blocked + n + 1) (Nat.succ_le_succ (Nat.zero_le _)) hcross
  obtain ⟨p, hpQ, hpHon⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbelow hQ
  obtain ⟨carrier, b, hcarrierX, hbCarrier, hbp, hpair⟩ :=
    hwit p hpQ
  have hb : b.val_index ∈ rho.honest := hbp ▸ hpHon
  have hbChain : b ∈ Protocol.named_chain_attestations X :=
    frozen_named_row_mem_chain_of_ancestor_source hcarrierX hbCarrier
  have hXread : X ∈
      (rho.storeBeforeTime S u (Protocol.vote_time S.E (s + 1))).bodies := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hX
  obtain ⟨N, hN, hpast⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
  have hXN : X ∈ (rho.stateBefore S N u).st.bodies := by
    simpa only [Run.storeBeforeTime, hN] using hXread
  obtain ⟨j, tb, hjN, hjevent, hjout, hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hXN hbChain hb
  have htb : tb < Protocol.vote_time S.E (s + 1) :=
    hpast j (Event.tick b.val_index tb) hjN hjevent
  have hread : S.a b.round < Protocol.vote_time S.E (s + 1) := by
    simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using htb
  have hrow : b.height_pair.erase.height? = some (blocked + n + 1) :=
    frozen_named_height_of_matches_source hpair
  obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
    h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
  have hseedRow : a.height_pair.erase.height? =
      some (blocked + n + 1) := by
    rcases hreg.seed.targetOrTimeout with heq | heq <;>
      simp only [heq, HeightPair.height?, Nat.add_assoc]
  have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
  have hbSlot : S.hc.opening_slot b.round + 1 ≤ s := by
    by_contra hn
    have hslot : s + 1 ≤ S.hc.opening_slot b.round + 1 :=
      Nat.succ_le_succ (Nat.le_of_lt_succ (Nat.lt_of_not_ge hn))
    have htime := vote_time_mono_slots S.E hslot
    exact (not_lt_of_ge htime)
      ((next_vote_time_lt_action S b.round).trans hread)
  have haSlot : S.hc.opening_slot a.round + 1 ≤ s :=
    (Nat.add_le_add_right
      (Nat.mul_le_mul_right S.hc.R hab) 1).trans hbSlot
  have hCCfg := h.honestFGSource_preceq_of_previousHead
    adm hcom hbelow hgst n hreg.seed.signerHonest hreg.seed.emitted
      hseedRow hreg.seed.exactFGSource haSlot hshor hv
      hCrun hC hheight
  have hbFreeze : S.a b.round ≤ Protocol.view_freeze S.E s := by
    simpa only [Nat.add_sub_cancel] using
      (action_lt_previousFreeze_of_lt_vote_named S hread).le
  have haFreeze : S.a a.round ≤ Protocol.view_freeze S.E s :=
    ((action_strictMono S).monotone hab).trans hbFreeze
  have hCfgFreezeBody : Cfg ∈
      (rho.storeBeforeTime S u (Protocol.view_freeze S.E s)).bodies :=
    hreg.frozenSourceMem_at_read adm haFreeze hu
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
    (Protocol.view_freeze S.E s) u).1.1.1
  have hCfgFreeze : Cfg.erase ∈
      (rho.storeBeforeTime S u (Protocol.view_freeze S.E s)).T := by
    change Cfg.erase ∈
      (NamedRun.stateBeforeTime S rho
        (Protocol.view_freeze S.E s) u).st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hCfgFreezeBody
  have hCfgProcessed := voterProcessed_mem_of_mem_previousFreeze_named
    S adm.toNamedScheduleWellFormed
      (Nat.succ_le_succ (Nat.zero_le s))
      (by simpa only [Nat.add_sub_cancel] using hCfgFreeze)
  exact ⟨Cfg,
    frozen_runBlock_of_action_body S adm hreg.seed.signerHonest
      hreg.seed.sourceMem,
    hCfgProcessed, hCCfg, hreg.seed.sourceDerivedHeight⟩

end NamedHeightRegimeBaseRun

#print axioms action_lt_previousFreeze_of_lt_vote_named
#print axioms voterProcessed_mem_of_mem_previousFreeze_named
#print axioms NamedHeightRegimeRun.sourceMem_at_read_named
#print axioms NamedHeightRegimeBaseRun.exists_frozen_descendant_at_crossing_of_previousHead_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
