module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroPreparedWalk
public import DecoupledConsensusProofs.Protocol.Grades.ProposalWalkComposition

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Named GST-zero canonical proposal duty, prebuilt over pins -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem canonicalProposalDuty_positive_of_gstZero_named_of_pins
    (hstores : ∀ (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
      {s : Slot}, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      S.E.proposer s ∈ rho.honest →
      ∀ {B : NamedBlock V}, proposedBlockAt S rho s = some B →
      ∀ v ∈ rho.honest,
        Proofs.Optimistic.NamedVoteStoreExtends S rho v s
          (namedWalkTargetTree S rho s v B)
          (proposedParent S rho s) B)
    (hnamesPin : ∀ (S : Setup V) {rho : Run V}, AdmissibleCore S rho →
      ∀ {s : Slot}, 0 < s →
      Protocol.vote_time S.E s ≤ rho.horizon →
      ∀ {B : NamedBlock V}, VoteStoresExtend S rho s B →
        NamedHonestVotesName S rho s B.erase)
    (hconfirmationAnchor : ∀ (S : Setup V) {rho : Run V}, WeakGenesis S rho →
      ∀ {s : Slot}, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {w x : V}, w ∈ rho.honest → x ∈ rho.honest →
        Block.Preceq
          (namedConfirmationAnchor S
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w s))
          (voterHeadAt S rho x s))
    (hcandidate : ∀ (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
      {s : Slot}, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      S.E.proposer s ∈ rho.honest →
      ∀ {B : NamedBlock V}, proposedBlockAt S rho s = some B →
      (∀ v ∈ rho.honest,
        Proofs.Optimistic.NamedVoteStoreExtends S rho v s
          (namedWalkTargetTree S rho s v B)
          (proposedParent S rho s) B) →
      ∀ v ∈ rho.honest,
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
            (Protocol.derive_named S.E S.cfg B).h ∧
          B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s))
    (hduty : ∀ {S : Setup V} {rho : Run V}, AdmissibleCore S rho →
      ∀ {s : Slot}, 0 < s →
      S.E.t_GST ≤ Protocol.vote_time S.E s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {B : NamedBlock V}, CanonicalSuffixProposalStoreFacts S rho s B →
        CanonicalProposalDutyAt S rho s B)
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    CanonicalProposalDutyAt S rho s B := by
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hsupportHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E s).trans hhor
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E s := by
    rw [h.gstZero]
    exact vote_time_nonneg S.E s
  have hrun := proposedBlockAt_blockInRun_of_admissible S h.core s hs hprop
    ((proposal_time_le_confirmation_time S.E s).trans hhor) hB
  have hstoresAll := hstores S h hs hhor hprop hB
  have hstoresPackage : VoteStoresExtend S rho s B := by
    intro v hv _hcommittee
    exact ⟨namedWalkTargetTree S rho s v B, proposedParent S rho s,
      hstoresAll v hv⟩
  have hnames := hnamesPin S h.core hs hvoteHor hstoresPackage
  have hhead (v : V) (hv : v ∈ rho.honest) : voterHeadAt S rho v s = B.erase :=
    Protocol.voterHeadAt_eq_proposedBlockAt_of_namedVoteStoreExtends
      S hB (hstoresAll v hv)
  have hanchor : ∀ v ∈ rho.honest,
      Block.Preceq
        (namedConfirmationAnchor S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s)) B.erase := by
    intro v hv
    have hle := hconfirmationAnchor S h hs hhor hv hv
    rw [hhead v hv] at hle
    exact hle
  have hvalidLate : ∀ v ∈ rho.honest,
      Protocol.VoteSetValid S.E s
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) := by
    intro v _hv
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      voteSetValid_confLate_stateBeforeTime S h.core.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E s) s
  have hcandidate' : ∀ v ∈ rho.honest,
      B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s) := by
    intro v hv
    exact (hcandidate S h hs hhor hprop hB hstoresAll v hv).2
  have hcone : NamedHonestVotesCone S rho s (fun X => Block.Preceq B.erase X) :=
    Proofs.Optimistic.honestVotesCone_preceq S rho s hrun hnames
  have hresolve : ∀ v ∈ rho.honest,
      Proofs.Optimistic.HeadsResolveIn S rho s
        (Proofs.Optimistic.confStore S rho v s).T
        (Proofs.Optimistic.confStore S rho v s).timestamp_block := by
    intro v hv
    let read := Internal.NamedRecoveryRead.confirmationInputRead S rho v s
    have hrootAnchor : Block.Preceq
        (confRoot (Proofs.Optimistic.confStore S rho v s))
        (namedConfirmationAnchor S read) := by
      change Block.Preceq
        (Protocol.get_fg_root read.st.core.toHealing.toFG)
        (Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
          S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s))
      exact NamedOutageClosure.fg_root_preceq_anchor S.E S.hc
        read.st.core.toHealing (S.hc.round_of read.st.core.s)
        (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
          (S.hc.round_of read.st.core.s)).g1
    have hroot : Block.Preceq
        (confRoot (Proofs.Optimistic.confStore S rho v s)) B.erase :=
      Block.preceq_trans hrootAnchor (hanchor v hv)
    exact WeakGoldfish.headsResolveIn_confStore_of_postHealingCone
      S h.core hv hpost hsupportHor hroot hcone
  exact hduty h.core hs hpost hhor
      { run := hrun
        names := hnames
        validLate := hvalidLate
        anchor := hanchor
        candidate := hcandidate'
        resolve := hresolve }

#print axioms canonicalProposalDuty_positive_of_gstZero_named_of_pins

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
