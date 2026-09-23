module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierFirst

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Round rows travel with their carrier onto a later opening's parent chain

The gate-off seed's `M - 1` promotion and the fixed-root rows both bottom out
on one fact: every honest round-`q` action attestation is on the parent chain
of a later carrier round's opening proposal.

The route has exactly three steps and never names an interior block.

1. **The row reaches the `+2` proposer's own selected source.** The honest
   round-`q` action is emitted at `S.a q`, one network delay before the
   proposal at `opening_slot q + 2`, so after GST the honest `+2` proposer has
   processed it (`honestPlusTwoBlock_holdsRoundRows`). The named source is
   `Protocol.NamedProposalRows.select.poolAndCarried`, whose FIRST component
   is the processed pool filtered by the SG admission window alone — no SG
   resolution is needed for pool rows, which is why this step asks for nothing
   about grades. The window holds because `opening_slot q + 2` names round `q`
   or `q + 1`, and `η_SG ≥ 1` covers the second case.
2. **The `+2` proposal covers the row.** `plusTwoProposal_covers_resolvedRoundRow`
   splits on on-chain exclusion: the row is either already on the selected
   parent's chain or carried by the `+2` block itself. Both alternatives put it
   on the `+2` block's OWN chain, which is all that is needed here; the sharper
   `plusTwoProposal_carries_resolvedRoundRow` is not required.
3. **Chain rows are monotone.** `chainRows` is the recursive ancestor row list,
   so a row on one block's chain is on the chain of every named descendant.

The third step is where the later opening enters: the caller supplies the
carrier fact `B₂ ⪯ Parent` from the lifecycle and adoption records. That
premise, post-GST at the round action, and the `+2` proposal horizon are the
whole round-local input list.

This module sits below `SeedPredPromotionRun` and `HeightProgressFixedRootRun`
so both can consume `actionRowsOnNextOpeningParentChain` directly.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Chain rows are monotone along named ancestry -/



/-! ## 2. The `+2` proposer's admission window covers the round -/

omit [DecidableEq V] [Fintype V] in
/-- The `+2` slot names the round itself or its successor: `R ≥ 2` keeps it
inside the two opening slots that bracket it. -/
private theorem round_of_opening_add_two_bounds
    (hc : Protocol.HealConfig) (q : Round) :
    q ≤ hc.round_of (hc.opening_slot q + 2) ∧
      hc.round_of (hc.opening_slot q + 2) ≤ q + 1 := by
  have hR0 : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  have hopen : hc.opening_slot q = q * hc.R := rfl
  constructor
  · show q ≤ (hc.opening_slot q + 2) / hc.R
    rw [hopen]
    calc q = q * hc.R / hc.R := (Nat.mul_div_cancel q hR0).symm
      _ ≤ (q * hc.R + 2) / hc.R := Nat.div_le_div_right (Nat.le_add_right _ _)
  · show (hc.opening_slot q + 2) / hc.R ≤ q + 1
    rw [hopen]
    have hle : q * hc.R + 2 ≤ (q + 1) * hc.R := by
      have := hc.R_ge_two
      calc q * hc.R + 2 ≤ q * hc.R + hc.R := Nat.add_le_add_left this _
        _ = (q + 1) * hc.R := by ring
    calc (q * hc.R + 2) / hc.R ≤ (q + 1) * hc.R / hc.R :=
          Nat.div_le_div_right hle
      _ = q + 1 := Nat.mul_div_cancel _ hR0

/-- `omega` unfolds `HealConfig.round_of` into a division by the variable `R`,
so the one arithmetic step is stated on opaque naturals. -/
private theorem nat_sub_le_of_le_succ {x e q : Nat}
    (hx : x ≤ q + 1) (he : 1 ≤ e) : x - e ≤ q := by omega

/-- The prepared `+2` proposer read carries the `+2` slot's own clock. -/
private theorem proposerReadAt_slot (S : Setup V) (rho : Run V) (s : Slot) :
    (proposerReadAt S rho s).st.core.s = s := by
  simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using Proofs.Optimistic.slotOf_proposal_time S.E s

/-- **Round `q` is inside the `+2` proposer's SG admission window.** The `+2`
slot names round `q` or `q + 1`; the second case is covered by `η_SG ≥ 1`. -/
theorem inWindow_round_at_plusTwo (S : Setup V) (rho : Run V) (q : Round) :
    Protocol.ProposalRows.inWindow S.hc
      (proposerReadAt S rho (S.hc.opening_slot q + 2)).st.core q = true := by
  obtain ⟨hlo, hhi⟩ := round_of_opening_add_two_bounds S.hc q
  have hslot : (proposerReadAt S rho (S.hc.opening_slot q + 2)).st.core.s =
      S.hc.opening_slot q + 2 :=
    proposerReadAt_slot S rho (S.hc.opening_slot q + 2)
  have hone : 1 ≤ S.hc.η_SG := S.hc.η_SG_ge_one
  unfold Protocol.ProposalRows.inWindow
  rw [hslot, decide_eq_true_eq]
  exact ⟨nat_sub_le_of_le_succ hhi hone, hlo⟩

/-! ## 3. The exact named row at the `+2` proposer read

`exactRow_mem_namedProcessed` is private to `RawHeightCoverageRun`; the lift is
repeated here rather than weakened, and its shape is unchanged. -/

/-- An honest emitter's exact named row is in the prepared proposal read's own
processed rows once its erasure is in the duty store's processed pool. -/
private theorem exactActionRow_mem_namedProcessed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {a : NamedAttestation V}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) (S.a a.round))
    (hprocessed : a.erase ∈
      (Protocol.proposerDutyStore S rho s).processed_attestations S.hc) :
    a ∈ Protocol.NamedProposalRows.processedRows S.hc
      (proposerReadAt S rho s).st := by
  let st := (proposerReadAt S rho s).st
  have hPool : NamedStore.PoolView st := by
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (Protocol.proposal_time S.E s)
          (S.E.proposer s)).1.1.1.2.2.2.1
  have hmap := NamedProposalRows.processed_rows_erasure S.hc st hPool
  have hmemMap : a.erase ∈
      (Protocol.NamedProposalRows.processedRows S.hc st).map
        NamedAttestation.erase := by
    rw [hmap]
    simpa only [st, Protocol.proposerDutyStore, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        hprocessed
  obtain ⟨b, hb, hberase⟩ := List.mem_map.mp hmemMap
  have hbFlat := hb
  rw [Protocol.NamedProposalRows.processedRows] at hbFlat
  obtain ⟨k, -, hbk⟩ := List.mem_flatMap.mp hbFlat
  have hrounds : Proofs.NamedStoreBridge.SgRowRounds st := by
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.sgRowRounds_stateBeforeTime S rho
          (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hbr : b.round = k := hrounds k b hbk
  have hbOwn : b ∈ st.sg_rows b.round := by
    rw [hbr]
    exact hbk
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.proposal_time S.E s)
  have hbN : b ∈
      (rho.stateBefore S n (S.E.proposer s)).st.sg_rows b.round := by
    rw [← congrFun hn (S.E.proposer s)]
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hbOwn
  have hbval : b.val_index = a.val_index :=
    congrArg CombinedAttestation.val_index hberase
  have hbHon : b.val_index ∈ rho.honest := by
    rw [hbval]
    exact haHon
  obtain ⟨_, _, _, _, _, hbEmit⟩ :=
    Proofs.Bridges.heldArePastEmissions_of_admissibleCore
      S adm.toNamedAdmissibleCore n (S.E.proposer s) hbN hbHon
  have hbEmit' : rho.emits S a.val_index
      (Object.attest b) (S.a b.round) := by
    simpa only [hbval] using hbEmit
  have hround : b.round = a.round :=
    congrArg CombinedAttestation.round hberase
  have hba : b = a := Proofs.Optimistic.emits_attest_unique S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
    hbEmit' hemit hround
  simpa only [st, hba] using hb

/-- **The honest round-`q` action row is in the `+2` proposer's selected
source.** Pool rows need only processing and the admission window; no SG
resolution and no grade hypothesis enters. -/
theorem actionAttestationAt_mem_selectedRows_at_plusTwo
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    actionAttestationAt S rho v q ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc
        (proposerReadAt S rho (S.hc.opening_slot q + 2)).st := by
  have haVal : (actionAttestationAt S rho v q).val_index = v :=
    (actionAttestationAt_shape S rho v q).1
  have haRound : (actionAttestationAt S rho v q).round = q :=
    (actionAttestationAt_shape S rho v q).2.1
  have hactionHor : S.a q ≤ rho.horizon :=
    (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (action_add_delta_le_plusTwo_proposal_time S q)).trans hhor
  have hemit : rho.emits S (actionAttestationAt S rho v q).val_index
      (Object.attest (actionAttestationAt S rho v q))
      (S.a (actionAttestationAt S rho v q).round) := by
    rw [haVal, haRound]
    exact honest_emits_exact_actionAttestationAt S adm hv q hactionHor (by assumption)
  have haHon : (actionAttestationAt S rho v q).val_index ∈ rho.honest := by
    rw [haVal]
    exact hv
  have haProcessed := exactActionRow_mem_namedProcessed S adm haHon hemit
    (honestPlusTwoBlock_holdsRoundRows S adm hcar hpost hhor hv)
  apply List.mem_append_left
  simp only [Protocol.NamedProposalRows.poolRows, List.mem_filter]
  refine ⟨haProcessed, ?_⟩
  rw [haRound]
  exact inWindow_round_at_plusTwo S rho q

/-! ## 4. The row on a later opening's parent chain -/





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
