module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.HandoverPrefixAgreement
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationPolicy
public import DecoupledConsensusProofs.Execution.UserConfirmationHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption
public import DecoupledConsensusProofs.Generic.SlotFreshness
public import DecoupledConsensusProofs.Execution.HandoverHeight
public import DecoupledConsensusProofs.Objects.WeakLegacySources
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Execution.StrongSeedConfirmation
public import DecoupledConsensusProofs.Execution.HeightFieldAssembly
public import DecoupledConsensusProofs.Execution.FGSafetyProgressDeadline
public import DecoupledConsensusProofs.Objects.FGSafetyRoot
public import DecoupledConsensusProofs.Generic.HeightRegimeNamed
public import DecoupledConsensusProofs.Execution.HeightRegimeNamedClosed
public import DecoupledConsensusProofs.Generic.HandoverFGWitnessesNamedClosed

@[expose] public section

/-!
# Transfer of the reads used by the safety bootstrap

Local prefix agreement preserves action stores, exact attestations, and
Goldfish reads. The protected vote cone transfers actual emissions and
processed blocks; it does not assume that the run-wide block scopes agree.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem coreVoterHeadRunBlock (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) {w : V} (hw : w ∈ rho.honest) (d : Slot) :
    ∃ H : NamedBlock V, H.erase = Internal.voterHeadAt S rho w d ∧
      H.erase ∈
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.T ∧
      NamedRun.blockInRun S rho H := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w d
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w d
  let H := Internal.voterHeadAt S rho w d
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E d) w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho w d ∈ st.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : tree ⊆ st.T := by
    intro D hD
    have hp := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hp).1
  have hHmem : H ∈ st.T := by
    rw [show H = Protocol.ghost (voterAnchorAt S rho w d) tree
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) by rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : H ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E d) w).st.core.T := by
    simpa only [read, st, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hHmem
  obtain ⟨H', hH'erase, hHrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hw (Protocol.vote_time S.E d) hHpre
  refine ⟨H', hH'erase, ?_, hHrun⟩
  simpa only [hH'erase, read, st] using hHmem

theorem emittedHead_mem_voteDutyRead_of_core (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) {x : V} (hx : x ∈ rho.honest)
    {s : Slot} {C : NamedBlock V} (hCrun : NamedRun.blockInRun S rho C)
    (hemit : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s)) :
    C.erase ∈ (Internal.NamedRecoveryRead.voteDutyRead S rho x s).st.core.T := by
  obtain ⟨i, hi, hmem⟩ := hemit
  change Object.gfVote ⟨x, s, C.erase.root⟩ ∈
    (on_tick_emit S x (rho.stateBefore S i x)
      (Protocol.vote_time S.E s)).2 at hmem
  rw [Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedScheduleWellFormed hi] at hmem
  have hduty := (Proofs.Optimistic.gfVote_emitted_shape S x
    (rho.stateBeforeTime S (Protocol.vote_time S.E s) x)
    (Protocol.vote_time S.E s) hmem).2.2.1
  have hduty' :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.voteDutyRead S rho x s).cache)
        S.E S.hc (S.node x)
        (Internal.NamedRecoveryRead.voteDutyRead S rho x s).st).2 =
        some ⟨x, s, C.erase.root⟩ := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt] using hduty
  have hroot : (Internal.voterHeadAt S rho x s).root = C.erase.root := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with] at hduty'
    split at hduty'
    · simpa only [Internal.voterHeadAt, voterCandidateTreeAt,
        Internal.NamedRecoveryRead.voteDutyRead] using
        congrArg GoldfishVote.head (Option.some.inj hduty')
    · simp at hduty'
  obtain ⟨H, hHerase, hHmem, hHrun⟩ :=
    coreVoterHeadRunBlock S adm hx s
  have hrootNamed : H.root = C.root := by
    rw [← Proofs.NamedWire.erase_root H, ← Proofs.NamedWire.erase_root C, hHerase]
    exact hroot
  have hHC : H = C :=
    adm.toNamedRootCollisionFree.root_injective H C hHrun hCrun H C
      (Or.inl (Proofs.NamedAncestry.named_self H))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hrootNamed
  simpa only [hHC] using hHmem


theorem AgreesUntil.actionStoreAt_eq (S : Setup V)
    {rho rho' : Run V} {cutoff : Time} (h : AgreesUntil rho rho' cutoff)
    {r : Round} (ht : S.a r ≤ cutoff) {v : V} (hv : v ∈ rho'.honest) :
    actionStoreAt S rho' v r = actionStoreAt S rho v r := by
  unfold actionStoreAt actionReadAt NamedActionReads.actionReadAt
  exact congrArg (fun n => NamedActionReads.actionReadFrom S n r)
    (AgreesUntil.stateBeforeTime_eq S h ht hv)

theorem AgreesUntil.actionAttestationAt_eq (S : Setup V)
    {rho rho' : Run V} {cutoff : Time} (h : AgreesUntil rho rho' cutoff)
    {r : Round} (ht : S.a r ≤ cutoff) {v : V} (hv : v ∈ rho'.honest) :
    actionAttestationAt S rho' v r = actionAttestationAt S rho v r := by
  unfold actionAttestationAt
  rw [show actionReadAt S rho' v r = actionReadAt S rho v r from
    AgreesUntil.actionStoreAt_eq S h ht hv]

theorem AgreesUntil.actionSGBlockAt_eq (S : Setup V)
    {rho rho' : Run V} {cutoff : Time} (h : AgreesUntil rho rho' cutoff)
    {r : Round} (ht : S.a r ≤ cutoff) {v : V} (hv : v ∈ rho'.honest) :
    actionSGBlockAt S rho' v r = actionSGBlockAt S rho v r := by
  unfold actionSGBlockAt
  rw [show actionReadAt S rho' v r = actionReadAt S rho v r from
    AgreesUntil.actionStoreAt_eq S h ht hv]

theorem AgreesUntil.confStore_eq (S : Setup V)
    {rho rho' : Run V} {cutoff : Time} (h : AgreesUntil rho rho' cutoff)
    {s : Slot} (ht : Protocol.confirmation_time S.E s ≤ cutoff)
    {v : V} (hv : v ∈ rho'.honest) :
    confStore S rho' v s = confStore S rho v s := by
  unfold confStore
  rw [AgreesUntil.storeBeforeTime_eq S h ht hv]



/--: the vote duty reads a prepared named node, so prefix agreement is
transferred on that read rather than on the erased tick store. -/
theorem AgreesUntil.voteDutyRead_eq (S : Setup V)
    {rho rho' : Run V} {cutoff : Time} (h : AgreesUntil rho rho' cutoff)
    {s : Slot} (ht : Protocol.vote_time S.E s ≤ cutoff)
    {v : V} (hv : v ∈ rho'.honest) :
    Internal.NamedRecoveryRead.voteDutyRead S rho' v s =
      Internal.NamedRecoveryRead.voteDutyRead S rho v s := by
  unfold Internal.NamedRecoveryRead.voteDutyRead NamedActionReads.confirmationReadAt
  exact congrArg
    (fun n => NamedActionReads.confirmationReadFrom S n (Protocol.vote_time S.E s))
    (AgreesUntil.stateBeforeTime_eq S h ht hv)

theorem AgreesUntil.voteDutyHead_eq (S : Setup V)
    {rho rho' : Run V} {cutoff : Time} (h : AgreesUntil rho rho' cutoff)
    {s : Slot} (ht : Protocol.vote_time S.E s ≤ cutoff)
    {v : V} (hv : v ∈ rho'.honest) :
    voteDutyHead S rho' v s = voteDutyHead S rho v s := by
  show Internal.voterHeadAt S rho' v s = Internal.voterHeadAt S rho v s
  unfold Internal.voterHeadAt
  rw [AgreesUntil.voteDutyRead_eq S h ht hv]




/-- The seed transfers to retained honest validators, with exact emissions.

design note: `ProtectedVoteSlot` is the named record, so the head clause is read on
the prepared `voterHeadAt` and the cone clause hands back a named run block of
the NEW run with the same erasure. The core twin below uses the prepared
vote-duty read directly; the full-`Admissible` wrapper is retained for callers
that already have the stronger execution record. -/
theorem AgreesUntil.protectedVoteSlot_of_core (S : Setup V)
    {rho rho' : Run V} (adm : AdmissibleCore S rho)
    (sch' : ScheduleWellFormed S rho') {cutoff : Time}
    (h : AgreesUntil rho rho' cutoff) {s : Slot}
    (ht : Protocol.vote_time S.E s < cutoff) {P : Block V}
    (hseed : ProtectedVoteSlot S rho s P) : ProtectedVoteSlot S rho' s P := by
  refine ⟨?_, ?_⟩
  · intro v hv
    show Block.Preceq P (Internal.voterHeadAt S rho' v s)
    rw [show Internal.voterHeadAt S rho' v s = Internal.voterHeadAt S rho v s from
      AgreesUntil.voteDutyHead_eq S h ht.le hv]
    exact hseed.heads v (h.honest_subset hv)
  · intro v hv hc
    obtain ⟨X, hPX, hXrun, hemit⟩ := hseed.cone v (h.honest_subset hv) hc
    have hXmem := emittedHead_mem_voteDutyRead_of_core S adm
      (h.honest_subset hv) hXrun hemit
    rw [← AgreesUntil.voteDutyRead_eq S h ht.le hv] at hXmem
    have hXmem' : X.erase ∈
        (rho'.stateBeforeTime S (Protocol.vote_time S.E s) v).st.core.T := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hXmem
    obtain ⟨C, hCerase, hCrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S sch' hv
        (Protocol.vote_time S.E s) hXmem'
    refine ⟨C, ?_, hCrun, ?_⟩
    · rw [hCerase]
      exact hPX
    · rw [hCerase]
      exact (AgreesUntil.emits_iff S
        adm.toNamedScheduleWellFormed sch' h ht hv _).mpr
        hemit

#print axioms emittedHead_mem_voteDutyRead_of_core


#print axioms AgreesUntil.protectedVoteSlot_of_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
