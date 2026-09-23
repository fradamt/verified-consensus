module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.GSTZeroProposalEvaluation
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Generic.RecoveryConcentration
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Exact post-GST confirmation of one honest proposal

The GST-zero proposal proof packages its confirmation store through a
whole-prefix canonical history. Recovery cannot use that package: an honest
run prefix before the healing boundary can contain selections on another
branch.

This file gives the boundary-local form. Honest proposal-to-voter transfer
makes every honest committee vote name the proposal. At each confirmation
reader, the caller supplies only the exact Section 7 fork-choice facts that
recovery must preserve: the FG root and SG anchor are below the proposal, and
the proposal is in the confirmation candidate tree. Post-GST relay then
derives head resolution and numerator membership. The ordinary Goldfish
kernel returns the proposal exactly.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The exact local Section 7 inputs for confirming one block after GST.

These are read at the real confirmation store. In recovery, they are supplied
by the moving-height filter argument and the common-grade anchor argument; no
statement about the pre-boundary run prefix is present. -/
structure RecoveryProposalConfirmationRead
    (S : Setup V) (rho : Run V) (s : Slot) (v : V)
    (B : NamedBlock V) : Prop where
  root : Block.Preceq
    (Protocol.get_fg_root
      (confirmationInputRead S rho v s).st.core.toHealing.toFG) B.erase
  anchor : Block.Preceq
    (namedConfirmationAnchor S (confirmationInputRead S rho v s)) B.erase
  candidate : B.erase ∈ confTree (confirmationInputRead S rho v s).st.core

/-- A run block in an honest confirmation candidate tree resolves by its own
root. Run-wide root collision freedom supplies uniqueness. -/
theorem find?_eq_some_confStore_of_candidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest) {B : NamedBlock V}
    (_hBrun : NamedRun.blockInRun S rho B)
    (hB : B.erase ∈ confTree (confirmationInputRead S rho v s).st.core) :
    Block.find? (confirmationInputRead S rho v s).st.core.T B.erase.root =
      some B.erase := by
  have hB' : B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s) := by
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using hB
  have hfind := Protocol.confFind_of_candidate S adm hv hB'
  simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using hfind

/-- Exact honest names give the confirmation numerator's `HonestSupport`
after GST. The local FG-root floor provides block availability; no GST-zero
or whole-prefix history premise is used. -/
theorem honestSupport_confVotes_after_gst_of_names
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hBrun : NamedRun.blockInRun S rho B)
    (hnames : NamedHonestVotesName S rho s B.erase)
    {v : V} (hv : v ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho v s).st.core.toHealing.toFG) B.erase)
    (hcandidate : B.erase ∈ confTree (confirmationInputRead S rho v s).st.core) :
    HonestSupport S.E (confirmationInputRead S rho v s).st.core.T
      (confirmationVotes S.E (confirmationInputRead S rho v s).st.core s)
      s rho.honest B.erase := by
  have hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B.erase X) :=
    Proofs.Optimistic.honestVotesCone_preceq S rho s hBrun hnames
  have hroot' : Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho v s)) B.erase := by
    simpa only [confRoot, Proofs.Optimistic.confStore_eq_confirmationInputRead] using hroot
  have hresolve := headsResolveIn_confStore_of_postHealingCone
    S adm hv hpost
      (le_trans (support_cutoff_le_confirmation_time S.E s) hhor)
      hroot' hvotes
  have hfind : Block.find? (Proofs.Optimistic.confStore S rho v s).T B.erase.root =
      some B.erase := by
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using
      find?_eq_some_confStore_of_candidate S adm hv hBrun hcandidate
  have hsupport : HonestSupport S.E
      (Proofs.Optimistic.confStore S rho v s).T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      s rho.honest B.erase := by
    apply Proofs.Optimistic.honestSupport_of_names
      S rho s B.erase hcom hnames hfind
    intro u hus huHon huCommittee hemit
    have hnamed := hnames u.val_index huHon huCommittee
    have hueq : u = ⟨u.val_index, s, B.erase.root⟩ :=
      Proofs.Optimistic.emits_gfVote_unique S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hemit hnamed
        (by simpa only using hus)
    have hresolvedB := hresolve B.erase
      ⟨u.val_index, huHon, huCommittee, ⟨B, rfl, hBrun⟩, hnamed⟩
    have harr : Proofs.Optimistic.HeadArrivesBefore
        (Proofs.Optimistic.confStore S rho v s).T
        (Proofs.Optimistic.confStore S rho v s).timestamp_block
        (Protocol.support_cutoff S.E s) u := by
      refine ⟨B.erase, ?_, hresolvedB.2⟩
      rw [hueq]
      simpa only using hresolvedB.1
    exact Protocol.canonicalSuffixHonestVoteCounted
      S adm hs hpost hhor v hv u hus huHon hemit harr
  simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead, confVotes,
    confirmationVotes, confLate, confirmationLate] using hsupport

/-- One honest post-GST proposal is written exactly to every honest reader's
`live_confirmed` field once proposal-to-voter transfer and the three local
fork-choice facts hold. -/
theorem proposedBlock_liveConfirmed_after_gst_of_localReads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B)
    (hstores : VoteStoresExtend S rho s B)
    (hread : ∀ v ∈ rho.honest,
      RecoveryProposalConfirmationRead S rho s v B) :
    ∀ v ∈ rho.honest,
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
        B.erase := by
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hnames := honestVotesName_of_voteStoresExtend
    S adm hs hvoteHor hstores
  have hBrun : NamedRun.blockInRun S rho B :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore s hs hprop
      ((proposal_time_le_confirmation_time S.E s).trans hhor) hB
  intro v hv
  have hlocal := hread v hv
  have hsupport : HonestSupport S.E
      (confirmationInputRead S rho v s).st.core.T
      (confirmationVotes S.E (confirmationInputRead S rho v s).st.core s)
      s rho.honest B.erase := by
    exact honestSupport_confVotes_after_gst_of_names
      S adm hcom hs hpost hhor hBrun hnames hv hlocal.root
        hlocal.candidate
  have hvalid : Protocol.VoteSetValid S.E s
      (confirmationLate S.E (confirmationInputRead S rho v s).st.core s) := by
    have hvalid' : Protocol.VoteSetValid S.E s
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
        voteSetValid_confLate_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
          (Protocol.confirmation_time S.E s) s
    simpa only [confirmationLate, confLate,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hvalid'
  have hpath : ∀ C : Block V,
      Block.Preceq
        (namedConfirmationAnchor S (confirmationInputRead S rho v s)) C →
      C ≠ namedConfirmationAnchor S (confirmationInputRead S rho v s) →
      Block.Preceq C B.erase →
      C ∈ confTree (confirmationInputRead S rho v s).st.core := by
    have hpath' := confPath_of_candidate S
      (show B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s) from by
        simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using
          hlocal.candidate)
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using hpath'
  rw [Proofs.Optimistic.live_confirmed_eq_update
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv s hhor]
  simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using
    (live_confirmed_eq_with
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (confirmationInputRead S rho v s).st.core s rho.honest B.erase
      hsupport hvalid hlocal.anchor hpath)

/-- Opening-slot specialization at the exact Section 7 action store. The
confirmation update precedes `attest` at `a r`, so the proposal selected by the
local theorem is the value that the SG and FG selectors read. -/
theorem openingProposal_liveConfirmed_actionStore_after_gst_of_localReads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} (hr : 0 < r)
    (hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r))
    (hhor : S.a r ≤ rho.horizon)
    (hprop : S.E.proposer (S.hc.opening_slot r) ∈ rho.honest)
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot r) = some B)
    (hstores : VoteStoresExtend S rho (S.hc.opening_slot r)
      B)
    (hread : ∀ v ∈ rho.honest,
      RecoveryProposalConfirmationRead S rho (S.hc.opening_slot r) v
        B) :
    ∀ v ∈ rho.honest,
      (actionStoreAt S rho v r).live_confirmed = B.erase := by
  have hs : 0 < S.hc.opening_slot r := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hr
      (lt_of_lt_of_le (by decide) S.hc.R_ge_two)
  have hconf : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) = S.a r :=
    (Protocol.a_eq_confirmation_time S.hc S.E r).symm
  have hall := proposedBlock_liveConfirmed_after_gst_of_localReads
    S adm hcom hs hpost (by simpa only [hconf] using hhor)
      hprop hB hstores hread
  intro v hv
  have hrecorded := hall v hv
  have hbridge := Proofs.Optimistic.live_confirmed_eq_update
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv
      (S.hc.opening_slot r)
      (by simpa only [hconf] using hhor)
  rw [hrecorded] at hbridge
  change (actionStoreAt S rho v r).st.core.live_confirmed = B.erase
  rw [actionStoreAt_eq_update_confirmation]
  have hslot : S.E.slotOf (S.a r) - 1 = S.hc.opening_slot r := by
    have hsc : S.a r =
        Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) :=
      Protocol.a_eq_support_cutoff_succ S.hc S.E r
    rw [hsc, Proofs.Optimistic.slotOf_support_cutoff]
    exact Nat.add_sub_cancel (S.hc.opening_slot r) 1
  rw [hslot]
  simpa only [Proofs.Optimistic.confStore, Run.storeBeforeTime,
    NamedRecoveryRead.confirmationInputRead,
    NamedActionReads.confirmationReadAt, hconf] using hbridge.symm

#print axioms find?_eq_some_confStore_of_candidate
#print axioms honestSupport_confVotes_after_gst_of_names
#print axioms proposedBlock_liveConfirmed_after_gst_of_localReads
#print axioms openingProposal_liveConfirmed_actionStore_after_gst_of_localReads

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
