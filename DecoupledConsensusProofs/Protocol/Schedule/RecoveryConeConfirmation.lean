module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryProposalConfirmation

@[expose] public section

/-!
# Confirmation from a post-GST honest vote cone

This leaf packages the local confirmation consumer needed after healing. The
honest vote cone supplies the confirmation numerator, while post-GST relay
resolves its named heads in the exact confirmation store. A directional
anchor floor below the candidate makes the generic confirmation kernel return
a genuine value at or above the candidate; no global honest-weight majority is
needed here.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A post-GST honest vote cone makes one confirmation evaluation genuine and
at least as high as its candidate when the confirmation root and SG anchor
both lie below that candidate. -/
theorem genuineConfirmationAndPreceq_of_postHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {B : NamedBlock V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B.erase X))
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho v s).st.core.toHealing.toFG) B.erase)
    (hanchor : Block.Preceq
      (namedConfirmationAnchor S (confirmationInputRead S rho v s)) B.erase)
    (hcandidate : B.erase ∈
      confTree (confirmationInputRead S rho v s).st.core) :
    GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s
        (Protocol.update_confirmation_with
          (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v s) s).live_confirmed ∧
      Block.Preceq B.erase
        (Protocol.update_confirmation_with
          (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v s) s).live_confirmed := by
  have hcut : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    le_trans (support_cutoff_le_confirmation_time S.E s) hhor
  let st := Proofs.Optimistic.confStore S rho v s
  let contract := NamedProfile.gradeContract
    (confirmationInputRead S rho v s).cache
  have hroot' : Block.Preceq (confRoot st) B.erase := by
    simpa only [confRoot, st, Proofs.Optimistic.confStore_eq_confirmationInputRead] using
      hroot
  have hresolve := Protocol.headsResolveIn_confStore_of_postHealingCone
    S adm hv hpost hcut hroot' hvotes
  have hsupport := Protocol.coneSupport_confVotes_after_gst
    S adm hcom hs hpost hhor hvotes hv hresolve
  have hvalid : Protocol.VoteSetValid S.E s
      (confLate S.E st s) := by
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      Protocol.voteSetValid_confLate_stateBeforeTime
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
          (Protocol.confirmation_time S.E s) s
  have hanchor' : Block.Preceq
      (confAnchorWith contract S.E S.hc st) B.erase := by
    simpa only [confAnchorWith, contract, st, namedConfirmationAnchor,
      confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hanchor
  have hpath : ∀ C : Block V,
      Block.Preceq (confAnchorWith contract S.E S.hc st) C →
      C ≠ confAnchorWith contract S.E S.hc st →
      Block.Preceq C B.erase → C ∈ confTree st := by
    have hpath' := Protocol.confPath_of_candidate S
      (show B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s) from by
        simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using
          hcandidate)
    simpa only [confAnchorWith, contract, st, namedConfirmationAnchor,
      confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hpath'
  have hwalk : Block.Preceq B.erase
      (confWalkWith contract S.E S.hc st s) :=
    Proofs.Optimistic.ghost_passes_cone S.E st.T (confTree st)
      (confVotes S.E st s) (confVotes S.E st s) (confLate S.E st s)
      s rho.honest hsupport hvalid hanchor' hpath
  have hwalkEligible : confEligible S.E st s
      (confWalkWith contract S.E S.hc st s) = true := by
    rcases Protocol.ghost_eligible (confAnchorWith contract S.E S.hc st)
        (confTree st) (confScore S.E st s) (confEligible S.E st s) with
      hA | helig
    · have hanchor'' : Block.preceq
          (confAnchorWith contract S.E S.hc st) B.erase = true := hanchor'
      have hEq : B.erase = confAnchorWith contract S.E S.hc st := by
        have hwalk' : Block.preceq B.erase
            (confWalkWith contract S.E S.hc st s) = true := hwalk
        have hA' : confWalkWith contract S.E S.hc st s =
            confAnchorWith contract S.E S.hc st := by
          simpa only [confWalkWith] using hA
        apply Block.preceq_antisymm (by simpa only [hA'] using hwalk')
        exact hanchor''
      have hanchorEligible : confEligible S.E st s
          (confAnchorWith contract S.E S.hc st) = true := by
        simp only [confEligible, decide_eq_true_eq, confCount, confScore]
        exact hsupport.eligible hvalid (by
          intro X hX
          simpa only [hEq] using hX)
      have hA' : confWalkWith contract S.E S.hc st s =
          confAnchorWith contract S.E S.hc st := by
        simpa only [confWalkWith] using hA
      rw [hA']
      exact hanchorEligible
    · exact helig
  have hpre := Proofs.Optimistic.update_confirmation_preceq_with contract
    S.E S.hc st s rho.honest hsupport hvalid hanchor' hpath
  have hresult : GenuineConfirmationWith contract S.E S.hc st s
        (Protocol.update_confirmation_with contract S.E S.hc st s).live_confirmed ∧
      Block.Preceq B.erase
        (Protocol.update_confirmation_with contract S.E S.hc st s).live_confirmed :=
    ⟨⟨rfl, hwalkEligible⟩, hpre⟩
  simpa only [contract, st] using hresult

/-- The preceding confirmation consumer applies independently to every honest
reader when each reader supplies its local root, anchor, and candidate facts. -/
theorem genuineConfirmationAndPreceq_of_postHealingCone_all_honest
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B.erase X))
    (hlocal : ∀ v ∈ rho.honest,
      Block.Preceq
          (Protocol.get_fg_root
            (confirmationInputRead S rho v s).st.core.toHealing.toFG) B.erase ∧
      Block.Preceq
        (namedConfirmationAnchor S (confirmationInputRead S rho v s)) B.erase ∧
      B.erase ∈ confTree (confirmationInputRead S rho v s).st.core) :
    ∀ v ∈ rho.honest,
      GenuineConfirmationWith
          (NamedProfile.gradeContract
            (confirmationInputRead S rho v s).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v s) s
            (Protocol.update_confirmation_with
              (NamedProfile.gradeContract
                (confirmationInputRead S rho v s).cache)
              S.E S.hc (Proofs.Optimistic.confStore S rho v s) s).live_confirmed ∧
        Block.Preceq B.erase
          (Protocol.update_confirmation_with
            (NamedProfile.gradeContract
              (confirmationInputRead S rho v s).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho v s) s).live_confirmed := by
  intro v hv
  obtain ⟨hroot, hanchor, hcandidate⟩ := hlocal v hv
  exact genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hs hpost hhor hv hvotes hroot hanchor hcandidate

#print axioms genuineConfirmationAndPreceq_of_postHealingCone
#print axioms genuineConfirmationAndPreceq_of_postHealingCone_all_honest

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
