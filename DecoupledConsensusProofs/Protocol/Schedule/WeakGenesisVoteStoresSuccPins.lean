module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedProtectedProposalPivot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Later GST-zero prepared vote-store extension, prebuilt over pins -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem honestVoteStoresExtend_succ_of_gstZero_of_pins
    (hcandidate : ∀ (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
      {d : Slot}, 1 ≤ d →
      Protocol.vote_time S.E (d + 1) ≤ rho.horizon →
      S.E.proposer (d + 1) ∈ rho.honest →
      ∀ {B : NamedBlock V}, proposedBlockAt S rho (d + 1) = some B →
      ∀ {v : V}, v ∈ rho.honest →
        B.erase ∈ voterCandidateTreeAt S rho v (d + 1))
    (hexists : ∀ (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
      {d : Slot}, 1 ≤ d →
      Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon →
      S.E.proposer (d + 1) ∈ rho.honest →
      ∀ {v : V}, v ∈ rho.honest →
        ∃ A : NamedBlock V, PreparedProtectedProposalPivot S rho d v A)
    (hfrozen : ∀ (S : Setup V) {rho : Run V}, AdmissibleCore S rho →
      ∀ {d : Slot} {v : V} {A B : NamedBlock V},
      proposedBlockAt S rho (d + 1) = some B →
      B.erase ∈ voterCandidateTreeAt S rho v (d + 1) →
      PreparedProtectedProposalPivot S rho d v A →
        NamedFrozenProposalSuffixBandInputs S rho (d + 1) A.erase v B)
    (hsuffix : ∀ (S : Setup V) {rho : Run V}, AdmissibleCore S rho →
      ∀ {s : Slot}, 0 < s →
      S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1) →
      S.E.proposer s ∈ rho.honest →
      ∀ {v : V}, v ∈ rho.honest →
      Protocol.vote_time S.E s ≤ rho.horizon →
      ∀ {pivot : Block V} {B : NamedBlock V},
      proposedBlockAt S rho s = some B →
      NamedFrozenProposalSuffixBandInputs S rho s pivot v B →
        NamedProposalPivotSuffixTransfer S rho s pivot v B)
    (htarget : ∀ (S : Setup V) {rho : Run V}, AdmissibleCore S rho →
      HonestCommittees S rho.honest →
      ∀ {d : Slot}, 0 < d →
      S.E.t_GST ≤ Protocol.vote_time S.E d →
      Protocol.support_cutoff S.E d ≤ rho.horizon →
      ∀ {v : V}, v ∈ rho.honest →
      ∀ {A B : NamedBlock V},
      proposedBlockAt S rho (d + 1) = some B →
      PreparedProtectedProposalPivot S rho d v A →
        Block.Preceq A.erase
          (Protocol.ghost (voterAnchorAt S rho v (d + 1))
            (namedWalkTargetTree S rho (d + 1) v B)
            (namedWalkTargetScore S rho (d + 1) v)
            (namedWalkTargetEligible S rho (d + 1) v)))
    (hscore : ∀ (S : Setup V) {rho : Run V}, AdmissibleCore S rho →
      ∀ {s : Slot}, 0 < s →
      S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1) →
      S.E.proposer s ∈ rho.honest →
      ∀ {v : V}, v ∈ rho.honest →
      Protocol.vote_time S.E s ≤ rho.horizon →
      ∀ {B : NamedBlock V}, proposedBlockAt S rho s = some B →
      B.erase ∈ voterCandidateTreeAt S rho v s →
      ∀ C,
        C ∈ namedWalkSourceTree S rho s →
        C ∈ namedWalkTargetTree S rho s v B →
        namedWalkTargetScore S rho s v C = namedWalkSourceScore S rho s C)
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {d : Slot} (hd : 1 ≤ d)
    (hhor : Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (d + 1) = some B) :
    ∀ v ∈ rho.honest,
      Proofs.Optimistic.NamedVoteStoreExtends S rho v (d + 1)
        (namedWalkTargetTree S rho (d + 1) v B)
        (proposedParent S rho (d + 1)) B := by
  intro v hv
  have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E (d + 1)).trans hhor
  have hsupportHor : Protocol.support_cutoff S.E d ≤ rho.horizon :=
    (support_cutoff_le_vote_time_succ S.E d).trans hvoteHor
  have hpostProposal :
      S.E.t_GST ≤ Protocol.proposal_time S.E ((d + 1) - 1) := by
    rw [h.gstZero]
    exact proposal_time_nonneg S.E _
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E d := by
    rw [h.gstZero]
    exact vote_time_nonneg S.E _
  have hcand := hcandidate S h hd hvoteHor hprop hB hv
  obtain ⟨A, hpivot⟩ := hexists S h hd hhor hprop hv
  have hband := hfrozen S h.core hB hcand hpivot
  have hsuffix' := hsuffix S h.core (Nat.zero_lt_succ d) hpostProposal
    hprop hv hvoteHor hB hband
  have htarget' := htarget S h.core h.committees (lt_of_lt_of_le Nat.zero_lt_one hd)
    hpostVote hsupportHor hv hB hpivot
  have hscore' := hscore S h.core (Nat.zero_lt_succ d) hpostProposal
    hprop hv hvoteHor hB hcand
  have hparentProposal : Block.Preceq (proposedParent S rho (d + 1)) B.erase := by
    rw [← proposedBlockErased_parent S rho (d + 1) hB]
    exact preceq_parent B.erase
  have hcompat : Block.compatible (voterAnchorAt S rho v (d + 1)) B.erase = true :=
    Block.compatible_of_preceq_common
      (Block.preceq_trans hpivot.targetAnchor
        (Block.preceq_trans hpivot.parent hparentProposal))
      (Block.preceq_self B.erase)
  apply Protocol.namedProposalWalkTransferred_of_frozenCompatiblePivot_core
    S h.core hB hprop hv hcand hcompat
  · simpa only [Internal.PhaseGrades.nodeAnchor, Internal.PhaseGrades.nodeRead,
      Protocol.get_sg_root_with] using hpivot.sourceAnchor
  · exact hpivot.parent
  · exact htarget'
  · exact hsuffix'
  · exact hscore'

#print axioms honestVoteStoresExtend_succ_of_gstZero_of_pins

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
