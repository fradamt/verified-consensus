module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Objects.PostGSTSync

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Exact post-GST relay into the proposal input -/

/-- A post-GST honest attestation with one full relay delay before an honest
proposal occurs in the exact processed-attestation list read by that proposal.

The proof uses the emitter's self-acceptance first. Accepted-once forwarding
then either finds the exact attestation already in the proposer's pool or
supplies an actual handler call during the attestation's round -- direct
delivery, an independent re-emission, or a carrying block -- and
`Proofs.NamedSGArrival.honest_row_after_call` retains the row across all three at
once. Pool monotonicity carries it to the proposal read. -/
theorem honestAttestation_mem_processedAtProposal_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {a : NamedAttestation V} {t : Time}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) t)
    (hpost : S.E.t_GST ≤ t)
    (hdelay : t + S.E.Δ ≤ Protocol.proposal_time S.E s) :
    let duty := Protocol.proposerDutyStore S rho s
    a.erase ∈ duty.processed_attestations S.hc := by
  let p := S.E.proposer s
  let tp := Protocol.proposal_time S.E s
  have hlt : t < tp := by
    exact lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (by simpa only [tp] using hdelay)
  obtain ⟨i, hi, hselfRow⟩ :=
    Protocol.attest_row_of_emission_exact S adm haHon hemit
  have hselfPool : a.erase ∈
      (rho.stateBefore S (i + 1) a.val_index).st.sg_pool a.round :=
    NamedAdmission.pool_view_mem _
      (Proofs.NamedRuntime.stateBefore_invariants S rho (i + 1) a.val_index).1.1.1.2.2.2.1
      a hselfRow
  have hselfProcessed : NamedReceipt.processed
      (rho.stateBefore S (i + 1) a.val_index).st (Object.attest a) = true := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hselfRow
  obtain ⟨j, hj, ta, hacc⟩ :=
    Protocol.acceptsAt_attest_of_processed
      S rho a.val_index (i + 1) a hselfProcessed
  have hpHon : p ∈ rho.honest := by simpa only [p] using hprop
  obtain ⟨-, e, he, -, heta⟩ := hacc.1
  have htaT : ta ≤ t := by
    have hji : j ≤ i := Nat.lt_succ_iff.mp hj
    rcases lt_or_eq_of_le hji with hji | rfl
    · have hkey := Proofs.Optimistic.key_le_of_index_lt S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hji he hi
      calc
        ta = e.time := heta.symm
        _ ≤ (Event.tick a.val_index t).time :=
          Proofs.Bridges.time_le_of_key_le hkey
        _ ≤ t := le_refl t
    · have heq : e = Event.tick a.val_index t :=
        Option.some.inj (he.symm.trans hi)
      calc
        ta = e.time := heta.symm
        _ ≤ t := by rw [heq]; exact le_refl t
  have htTa : t ≤ ta := by
    obtain ⟨te, hte, hemite⟩ : ∃ te, te ≤ ta ∧
        rho.emits S a.val_index (Object.attest a) te := by
      have haccProcess :
          NamedRun.processes S rho a.val_index (Object.attest a) ta ∨
            ∃ B : NamedBlock V,
              NamedRun.processes S rho a.val_index (Object.block B) ta ∧
              a ∈ B.attestations :=
        Protocol.processes_of_acceptsAt_attest S hacc
      rcases haccProcess with hdirect | ⟨B, hblock, haIn⟩
      · exact adm.unforgeable a.val_index (Object.attest a) ta hdirect
          a.val_index haHon rfl
      · exact adm.carried_attest a.val_index B ta hblock a haIn haHon
    have hteq : te = t := by
      obtain ⟨-, hteShape⟩ := Proofs.Optimistic.emits_attest_shape S hemite
      obtain ⟨-, htShape⟩ := Proofs.Optimistic.emits_attest_shape S hemit
      rw [hteShape, htShape]
    simpa only [hteq] using hte
  have hta : ta = t := le_antisymm htaT htTa
  have carryToProposal : ∀ {q : Nat} {ev : Event V},
      rho.events[q]? = some ev → ev.time < tp →
        a.erase ∈ (rho.stateBefore S (q + 1) p).st.sg_pool a.round →
          a.erase ∈ (rho.stateBeforeTime S tp p).st.sg_pool a.round := by
    intro q ev hq hqt ha
    exact Protocol.attest_mem_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hq hqt ha
  have haRead : a.erase ∈
      (rho.stateBeforeTime S tp p).st.sg_pool a.round := by
    by_cases hsame : p = a.val_index
    · have hreadSelf := Protocol.attest_mem_stateBeforeTime_of_post S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi
        (by simpa only [tp] using hlt) hselfPool
      simpa only [hsame] using hreadSelf
    · by_cases halready : NamedReceipt.processed
          (rho.stateBefore S (j + 1) p).st (Object.attest a) = true
      · have hrow : a ∈ (rho.stateBefore S (j + 1) p).st.sg_rows a.round := by
          simpa only [NamedReceipt.processed, decide_eq_true_eq] using halready
        have ha : a.erase ∈ (rho.stateBefore S (j + 1) p).st.sg_pool a.round :=
          NamedAdmission.pool_view_mem _
            (Proofs.NamedRuntime.stateBefore_invariants S rho (j + 1) p).1.1.1.2.2.2.1
            a hrow
        exact carryToProposal he (by
          simp only [Event.time]
          rw [heta, hta]
          simpa only [tp] using hlt) ha
      · have hunaccepted : NamedReceipt.processed
            (rho.stateBefore S (j + 1) p).st (Object.attest a) = false :=
          Bool.eq_false_of_not_eq_true halready
        have hrelayHorizon : ta + S.E.Δ ≤ rho.horizon := by
          rw [hta]
          exact hdelay.trans hhor
        obtain ⟨td, htaTd, htd, j', hcall⟩ :=
          Protocol.relay_attest_after_gst S adm haHon hpHon
            (by simpa only [hta] using hpost) hacc hunaccepted hrelayHorizon
        have htShape := (Proofs.Optimistic.emits_attest_shape S hemit).2
        have hlo : S.a a.round ≤ td := by
          rw [← htShape, ← hta]
          exact htaTd
        have hhi : td < S.a a.round + S.E.Δ := by
          rw [← htShape, ← hta]
          exact htd
        have hemitAction : rho.emits S a.val_index (Object.attest a) (S.a a.round) := by
          rw [← htShape]; exact hemit
        have hrow : a ∈ (rho.stateBefore S (j' + 1) p).st.sg_rows a.round :=
          Proofs.NamedSGArrival.honest_row_after_call S rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
            adm.toNamedAdmissibleCore.toNamedUnforgeable haHon hemitAction hcall hlo hhi
        have hpool : a.erase ∈ (rho.stateBefore S (j' + 1) p).st.sg_pool a.round :=
          NamedAdmission.pool_view_mem _
            (Proofs.NamedRuntime.stateBefore_invariants S rho (j' + 1) p).1.1.1.2.2.2.1
            a hrow
        obtain ⟨-, e', he', -, hte'⟩ := hcall
        have htdlt : td < tp := by
          have hbound : ta + S.E.Δ ≤ tp := by
            rw [hta]; simpa only [tp] using hdelay
          exact lt_of_lt_of_le htd hbound
        exact carryToProposal he' (by
          simp only [Event.time]
          rw [hte']
          exact htdlt) hpool
  let duty := Protocol.proposerDutyStore S rho s
  have haDuty : a.erase ∈ duty.sg_pool a.round := by
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, tp, p] using haRead
  have hround : a.round ≤ S.hc.round_of duty.s := by
    have hltAction : S.a a.round < Protocol.proposal_time S.E s := by
      rw [← (Proofs.Optimistic.emits_attest_shape S hemit).2]
      simpa only [tp] using hlt
    have hr := Protocol.action_round_le_of_lt_proposal S
      (r := a.round) (s := s) hltAction
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_proposal_time] using hr
  exact Protocol.mem_processed_attestations_of_pool
    S.hc duty haDuty hround


/-! ## The exact event-prefix residual -/






/-! ## End-to-end proposal-child rebuilding -/



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
