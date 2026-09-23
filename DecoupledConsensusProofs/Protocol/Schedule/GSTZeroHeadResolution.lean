module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.BlockVisibilityCore
public import DecoupledConsensusProofs.Protocol.Schedule.AdoptionTransport
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

/-!
# Honest-head resolution at later GST-zero duty stores

Block admission is strict at the Goldfish support cutoff, but the confirmation
and next-slot vote duties read later stores. This file transports admitted
honest heads to those later reads. It does not produce admission: block relay
and the receiver's finalized-ancestor guard remain the owners of that fact.

## Named-runtime proof status 

The `headsResolveIn_*` family below ports mechanically: `RunBlock` is
`NamedRun.blockInRun` over `NamedBlock V`, so its one internal
`RunBlock`-producing step now goes through `Proofs.NamedStoreBridge.
exists_named_of_mem_stateBefore` and `Proofs.NamedWire.erase_root`, and
`Admissible.toScheduleWellFormed`/`.toRootCollisionFree` route through the
real auto field `.toNamedAdmissibleCore` (`NamedAdmissibleCore`'s own
`.toNamedScheduleWellFormed`/`.toNamedRootCollisionFree` fields), not through
`Execution.AdmissibleCore`'s same-named abbreviations, which the plain
`.toAdmissibleCore` chain does not reach.

**available — `emittedHead_mem_voteDutyStore`.** The bridge now relates the
emitted vote to the same prepared `voteDutyRead` used by the named tick. It
proves the prepared head's membership in that read's own candidate tree and
then uses named root collision freedom to identify the emitted body.

**Open — `voteDuty_emits_head`.** Its old conclusion still identifies an
emitted head with a bare-contract `Protocol.get_head_in_tree` on
`Proofs.Optimistic.voteDutyStore`. The named tick uses
`Protocol.NamedDuties.goldfish_vote_with (NamedProfile.gradeContract n.cache)`;
its cached frame anchor is not the fresh `Protocol.GradeContract.current`
anchor. Closing that Q-PR2 agreement is the NamedOutageClosure branches's subject
and is not importable here. No new public premise is introduced.

`honestHead_mem_ownVoteDutyStore`'s earlier call required the blocked bare-head
form, and it has no consumer anywhere in the union cone (grepped against the
661-module list): it is retired verbatim  to
`the compatibility layer
.lean`.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The exact visibility surface for head resolution. Genesis needs no
accepting transition; every other honest head must be admitted before the
support cutoff. -/
def HonestHeadsAvailableBefore (S : Setup V) (rho : Run V) (s : Slot)
    (v : V) (Gamma : Time) : Prop :=
  ∀ X : Block V, Proofs.Optimistic.HonestHead S rho s X →
    X = Block.genesis ∨ AdmittedBefore S rho v X Gamma

private theorem voterHead_runBlock_for_voteDutyRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (d : Slot) :
    ∃ H : NamedBlock V, H.erase = voterHeadAt S rho w d ∧
      H.erase ∈ (voteDutyRead S rho w d).st.core.T ∧
      NamedRun.blockInRun S rho H := by
  let read := voteDutyRead S rho w d
  let st := read.st.core
  let tree := Proofs.HealingSurface.voterCandidateTreeAt S rho w d
  let H := voterHeadAt S rho w d
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E d) w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : Proofs.HealingSurface.voterAnchorAt S rho w d ∈ st.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : tree ⊆ st.T := by
    intro D hD
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hprocessed).1
  have hHmem : H ∈ st.T := by
    rw [show H = Protocol.ghost (Proofs.HealingSurface.voterAnchorAt S rho w d) tree
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) by rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : H ∈
      (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E d) w).st.core.T := by
    simpa only [read, st, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHmem
  obtain ⟨H', hH'erase, hHrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
      (Protocol.vote_time S.E d) hHpre
  refine ⟨H', hH'erase, ?_, hHrun⟩
  simpa only [hH'erase, read, st] using hHmem

/-- An emitted honest vote names a body in its prepared vote-duty tree. -/
theorem emittedHead_mem_voteDutyStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} {C : NamedBlock V}
    (hCrun : NamedRun.blockInRun S rho C)
    (hemit : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s)) :
    C.erase ∈ (voteDutyRead S rho x s).st.core.T := by
  have hs : 0 < s := by
    have hshape := Proofs.Optimistic.emits_gfVote_shape S hemit
    simpa only [Proofs.Optimistic.slotOf_vote_time S.E s] using hshape.1
  obtain ⟨i, hi, hmem⟩ := hemit
  change Object.gfVote ⟨x, s, C.erase.root⟩ ∈
    (on_tick_emit S x (rho.stateBefore S i x)
      (Protocol.vote_time S.E s)).2 at hmem
  rw [Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi] at hmem
  have hduty := (Proofs.Optimistic.gfVote_emitted_shape S x
    (rho.stateBeforeTime S (Protocol.vote_time S.E s) x)
    (Protocol.vote_time S.E s) hmem).2.2.1
  have hduty' :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract (voteDutyRead S rho x s).cache)
        S.E S.hc (S.node x) (voteDutyRead S rho x s).st).2 =
        some ⟨x, s, C.erase.root⟩ := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt] using hduty
  have hroot : (voterHeadAt S rho x s).root = C.erase.root := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with] at hduty'
    split at hduty'
    · simpa only [voterHeadAt, Proofs.HealingSurface.voterCandidateTreeAt,
        NamedRecoveryRead.voteDutyRead] using
        congrArg GoldfishVote.head (Option.some.inj hduty')
    · simp at hduty'
  obtain ⟨H, hHerase, hHmem, hHrun⟩ :=
    voterHead_runBlock_for_voteDutyRead S adm hx s
  have hrootNamed : H.root = C.root := by
    rw [← Proofs.NamedWire.erase_root H, ← Proofs.NamedWire.erase_root C, hHerase]
    exact hroot
  have hHC : H = C :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective H C
      hHrun hCrun H C (Or.inl (Proofs.NamedAncestry.named_self H))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hrootNamed
  simpa only [hHC] using hHmem



/-- Honest-head availability before the support cutoff resolves every head at
any later pre-time store. The original cutoff remains the block-stamp bound. -/
theorem headsResolveIn_storeBeforeTime_of_availableBefore_at_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) (s : Slot) {Gamma : Time}
    (hcut : Protocol.support_cutoff S.E s ≤ Gamma)
    (havailable : HonestHeadsAvailableBefore S rho s v
      (Protocol.support_cutoff S.E s)) :
    Proofs.Optimistic.HeadsResolveIn S rho s
      (rho.storeBeforeTime S v Gamma).T
      (rho.storeBeforeTime S v Gamma).timestamp_block := by
  let cutoff := Protocol.support_cutoff S.E s
  have htransport : ∀ X : Block V, Proofs.Optimistic.HonestHead S rho s X →
      X ∈ (rho.storeBeforeTime S v Gamma).T ∧
        stampedBefore (rho.storeBeforeTime S v Gamma).timestamp_block cutoff X = true := by
    intro X hX
    rcases havailable X hX with rfl | hadmit
    · exact genesis_mem_and_stamp_storeBeforeTime S
        adm.toNamedScheduleWellFormed v Gamma cutoff
    · exact admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed
        hadmit hcut
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hstore : rho.storeBeforeTime S v Gamma = (rho.stateBefore S n v).st :=
    congrArg NamedNodeState.st (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
      S adm.toNamedScheduleWellFormed Gamma) v)
  have hrun : ∀ X : Block V, X ∈ (rho.storeBeforeTime S v Gamma).T →
      ∃ C : NamedBlock V, C.erase = X ∧ RunBlock S rho C := by
    intro X hX
    have hXT : X ∈ (rho.stateBefore S n v).st.core.T := by
      rw [← hstore]; exact hX
    obtain ⟨D, hDbodies, hDerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hXT
    exact ⟨D, hDerase, D, Or.inr ⟨v, hv, n, hDbodies⟩, Proofs.NamedAncestry.named_self D⟩
  apply Proofs.Optimistic.headsResolveIn_of S rho s
  · intro X hX
    exact (htransport X hX).1
  · intro X Y hX hY hroot
    obtain ⟨CX, hCX, hCXrun⟩ := hrun X hX
    obtain ⟨CY, hCY, hCYrun⟩ := hrun Y hY
    have hrootNamed : CX.root = CY.root := by
      rw [← Proofs.NamedWire.erase_root CX, ← Proofs.NamedWire.erase_root CY, hCX, hCY]
      exact hroot
    have hCXY : CX = CY :=
      adm.toNamedRootCollisionFree.root_injective CX CY hCXrun hCYrun CX CY
        (Or.inl (Proofs.NamedAncestry.named_self CX)) (Or.inr (Proofs.NamedAncestry.named_self CY)) hrootNamed
    rw [← hCX, ← hCY, hCXY]
  · intro X hX
    exact (htransport X hX).2

theorem headsResolveIn_storeBeforeTime_of_availableBefore_at
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (s : Slot) {Gamma : Time}
    (hcut : Protocol.support_cutoff S.E s ≤ Gamma)
    (havailable : HonestHeadsAvailableBefore S rho s v
      (Protocol.support_cutoff S.E s)) :
    Proofs.Optimistic.HeadsResolveIn S rho s
      (rho.storeBeforeTime S v Gamma).T
      (rho.storeBeforeTime S v Gamma).timestamp_block :=
  headsResolveIn_storeBeforeTime_of_availableBefore_at_core
    S adm.toNamedAdmissibleCore hv s hcut havailable


/-- Genesis-aware head availability at the support cutoff resolves every head
in the same slot's confirmation store. -/
theorem headsResolveIn_confStore_of_availableBefore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (s : Slot)
    (havailable : HonestHeadsAvailableBefore S rho s v
      (Protocol.support_cutoff S.E s)) :
    Proofs.Optimistic.HeadsResolveIn S rho s
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block := by
  have h := headsResolveIn_storeBeforeTime_of_availableBefore_at
    S adm hv s (support_cutoff_le_confirmation_time S.E s) havailable
  simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using h




#print axioms emittedHead_mem_voteDutyStore

end Protocol
end DecoupledConsensusModel

end
