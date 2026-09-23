module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBoundaryConeLead
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransport

@[expose] public section

/-!
# Named gate-off window cone

This module states the named fixed-height window used by the recovery source
frame. The protected value is the selected prepared Q2, not the action SG
carrier. The same-reader selector floor is proved below.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Proofs.NamedOutageClosure
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]



/- The recovery-facing name keeps the common local-Q2 result at the gate-off
boundary. The protected block is the selected local floor `P`, not the source
block supplied by a separate recovery witness. -/

/- The common floor can protect the same block that forms at every G2 read.
The result uses the selected local floor `P`; it does not claim that a source
reader's separate Q2 is the protected value. -/

/-- A selected Q2 at one honest action read is a common floor for the
round's opening vote heads. Relative G2 transfers only to G1 at another
reader; K6 keeps the transferred block active at the domain and duty reads. -/
theorem selectedQ2_openingVotesCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {c : Round} (hc : 0 < c) (ready : GradeRoundReady S rho c)
    {v : V} (hv : v ∈ rho.honest) {Q : Block V}
    (hQ : nodeQ2 S (actionReadAt S rho v c) c = some Q)
    (hK6 : VoterAnchorSourceQ2Inputs S rho c v Q) :
    NamedHonestVotesCone S rho (S.hc.opening_slot c)
      (fun X => Block.Preceq Q X) := by
  have hopenPos : 0 < S.hc.opening_slot c := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hc
      (Nat.lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)
  have hround : S.hc.round_of (S.hc.opening_slot c) = c := by
    simp only [Protocol.HealConfig.round_of,
      Protocol.HealConfig.opening_slot]
    have hR : 0 < S.hc.R :=
      lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left c hR
  have hread : domain S.E S.hc c .g1 <
      Protocol.vote_time S.E (S.hc.opening_slot c) := by
    rw [domain_g1_eq_opening]
    exact Protocol.proposal_time_lt_vote_time S.E _
  have hvoteAction :
      Protocol.vote_time S.E (S.hc.opening_slot c) ≤ S.a c :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans (by
      rw [opening_confirmation_time_eq_action])
  have hvoteHorizon :
      Protocol.vote_time S.E (S.hc.opening_slot c) ≤ rho.horizon := by
    simpa only [domain, Phase.domainOffset, opening,
      Protocol.vote_time, one_mul] using ready.2
  have hsource : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionDutyRead S rho v c).cache)
      S.E S.hc (actionDutyRead S rho v c).st.core.toHealing c = some Q := by
    simpa only [nodeQ2, nodeRead, actionDutyRead] using hQ
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
  apply honestVotesCone_of_selectedActionG2_of_readDisposition
    S adm hc ready hv hsource hopenPos hround hread hvoteAction
      hvoteHorizon
  · intro w hw _
    have htarget := hK6.g1Target w hw
    have hforward : ∀ sender u root Head,
        u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
          (readAt S rho (domain S.E S.hc c .g2) v).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc c .g2) v).st.core.F
          S.hc.η_SG c (early S.E S.hc c .g2) sender →
        DecoupledConsensusModel.Protocol.localCovers
          (readAt S rho (domain S.E S.hc c .g2) v).st.core.toHealing.gradeView
          u.confirmed Q = true →
        u.confirmed = some root →
        Block.find?
          (readAt S rho (domain S.E S.hc c .g2) v).st.core.T root =
            some Head →
        Block.Preceq
          (readAt S rho (domain S.E S.hc c .g1) w).st.core.F Head := by
      intro sender u root Head _ hcover hconf hfind
      have hFQ := GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read
        S rho htarget
      apply Block.preceq_trans hFQ
      unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
        hconf] at hcover
      rw [hfind] at hcover
      exact hcover
    have hslash : SlashableBound S rho :=
      slashableBound_of_admissible_belowOneThird S adm hbelow
    have hfinalized :=
      crossReaderFinalizedBelow_of_finalitySafety_and_relay
        S adm hslash ready.1 ready.2 hv hw hforward
    have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
      S adm.toNamedAdmissibleCore hc ready.1 ready.2 hv hw hfinalized
    have hG1 := storeGrade_g1_of_storeGrade_g2_cross_reader
      S rho adm.toNamedAdmissibleCore c
        (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore ready.1)
        ready.2 v w hv hw Q hG2 hguard
    exact ⟨htarget, hG1, hK6.openingTarget w hw⟩
  · intro w hw _
    exact Or.inr (hK6.openingTarget w hw)

/-! The cross-reader half remains open. The exact target is:

```lean
theorem honestCarriersAbove_selectedQ2_of_gateOff...:
    HonestCarriersAbove S rho Q c
```

After `intro u hu`, the available local theorem requires
`nodeQ2 S (actionReadAt S rho u c) c = some Qᵤ` and `Q ⪯ Qᵤ`. The inputs
currently expose only the source equality at `v`. A G2-to-G1 transfer gives
Q a target-reader G1 grade, but no current theorem converts that fact into a
floor for the target reader's Q2 fallback. The prepared selector can return
that Q2 below its G1 anchor when `deepest_clear = none`.
-/

#print axioms selectedQ2_openingVotesCone

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
