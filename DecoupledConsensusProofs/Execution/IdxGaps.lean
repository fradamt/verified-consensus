module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Execution.EventIndexBridge
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrivalStampCarrier
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.ProposalRows
public import DecoupledConsensusProofs.Execution.ReceiptCallsBase

@[expose] public section

/-!
# Closed gap (index-bounded refactor)

This file proves `emission_index_le_self_proposed_carrier` by index bounds.

`emission_index_le_self_proposed_carrier` is closed here by strong induction
on the self-proposal tick index, routing through the F2 row source
(`Protocol.NamedProposalRows.select.poolAndCarried`): a carried row is either
a direct pool row (`NamedOutageProvenance.honest_held_row_emission`) or a row
carried by an already-held body (`honest_held_ancestor_row_emission`). Either
way the resulting acceptance event is a delivery (closed directly by the
index bridge lemmas) or a further self-tick at a strictly smaller index
(closed by the induction hypothesis).
-/


namespace DecoupledConsensusModel.Internal.NamedOutageEntry.History
open Execution Protocol
open Protocol.NamedProposalRows
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem tick_index_unique (rho : NamedRun V) (nodup : rho.events.Nodup)
    {i j : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) (hj : rho.events[j]? = some (.tick v t)) :
    i = j := by
  obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj_iff nodup).mp (by rw [hiGet, hjGet])

private theorem row_tick_time_eq_action (S : Setup V) (rho : NamedRun V)
    {u : V} {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho u (.attest a) t) : t = S.a a.round := by
  obtain ⟨_, _, _, _, _, _, htime, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hem
  exact htime

omit [Fintype V] in
private theorem preceq_refl (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

private theorem emission_index_le_self_proposed_carrier_aux
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho) :
    ∀ (j : Nat) (v : V) (t : Time) (B : NamedBlock V),
    rho.events[j]? = some (.tick v t) →
    NamedObject.block B ∈ NamedRun.emittedAt S rho j v t →
    ∀ (a : NamedAttestation V), a ∈ B.attestations → a.val_index ∈ rho.honest →
    ∀ (k : Nat) (t' : Time), rho.events[k]? = some (.tick a.val_index t') →
    NamedObject.attest a ∈ NamedRun.emittedAt S rho k a.val_index t' →
    t' ≤ t → k ≤ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j IH =>
    intro v t B hj hemB a ha hu k t' hk hemit ht'
    have ht'eq : t' = S.a a.round := row_tick_time_eq_action S rho ⟨k, hk, hemit⟩
    have hcall := Proofs.NamedReceiptCallsBase.self_proposal_call S rho hj hemB
    dsimp only at hcall
    set before : Protocol.NamedStore V :=
      Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho j v).st t with hbefore_def
    have hpw : Protocol.NamedActions.proposal_with
        (DecoupledConsensusModel.Protocol.frameContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc
            (NamedRun.stateBefore S rho j v).st.core.toHealing t
            (NamedRun.stateBefore S rho j v).cache))
        .poolAndCarried S.E S.hc (S.node v) before = some B := by
      have h2 := congrArg Prod.snd hcall
      unfold Protocol.NamedDuties.propose_block_with at h2
      split at h2 <;> simp_all
    have hpayload := Proofs.NamedActions.proposal_payload
      (DecoupledConsensusModel.Protocol.frameContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc
          (NamedRun.stateBefore S rho j v).st.core.toHealing t
          (NamedRun.stateBefore S rho j v).cache))
      .poolAndCarried S.E S.hc (S.node v) before B hpw
    have hrows : B.attestations = proposalRows B.parent (select .poolAndCarried S.hc before) :=
      hpayload.2.2.2.2.2.2.1
    have haSel : a ∈ select .poolAndCarried S.hc before :=
      (Proofs.NamedProposalRows.mem_proposalRows B.parent
        (select .poolAndCarried S.hc before) a (hrows ▸ ha)).1
    rw [Proofs.NamedProposalRows.selected_source_exact] at haSel
    rcases List.mem_append.mp haSel with hpool | hcarried
    · -- Pool branch: `a` sits in v's own pool at the strict prefix `j`.
      have hprocessed : a ∈ processedRows S.hc before := (List.mem_filter.mp hpool).1
      obtain ⟨round', -, haRow'⟩ := List.mem_flatMap.mp hprocessed
      have hdata := (Proofs.NamedOutageHistory.SGArrival.data_at_event S rho
        core.toNamedScheduleWellFormed hj v).1
      have hround'eq : a.round = round' := (hdata.2 round' a haRow').1
      have haRound : a ∈ (NamedRun.stateBefore S rho j v).st.sg_rows a.round := by
        rw [hround'eq]; exact haRow'
      obtain ⟨j', hj'lt, t'', hacc, hsend, -⟩ :=
        Proofs.NamedOutageProvenance.honest_held_row_emission S rho core.toNamedUnforgeable
          j v haRound hu
      rcases hacc.1.1 with hdirect | ⟨Bc, pos, before', hcarr⟩
      · rcases hdirect with ⟨tt, hjtick, hemtt⟩ | ⟨tt, hjdeliv⟩
        · have hemV : NamedRun.emits S rho v (.attest a) tt := ⟨j', hjtick, hemtt⟩
          obtain ⟨-, -, -, -, hval, -, htimeV, -⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_stages S rho hemV
          have hveq : v = a.val_index := hval.symm
          have httV : tt = t' := htimeV.trans ht'eq.symm
          have hjtick' : rho.events[j']? = some (.tick a.val_index t') := by
            rw [← hveq, ← httV]; exact hjtick
          have hkj' : k = j' := tick_index_unique rho core.nodup hk hjtick'
          exact hkj' ▸ hj'lt.le
        · obtain ⟨e, heE, -, hteqE⟩ := hacc.1.2
          have heEq : e = NamedEvent.deliver v (NamedObject.attest a) tt :=
            Option.some.inj (heE.symm.trans hjdeliv)
          have httEq : tt = t'' := by rw [heEq] at hteqE; exact hteqE
          have htle : t' ≤ tt := by rw [ht'eq, httEq]; exact hsend
          have hklt : k < j' := tick_lt_of_deliver_index rho core.sorted hjdeliv hk htle
          exact le_trans hklt.le hj'lt.le
      · obtain ⟨hblockcall, -, -, hpos⟩ := hcarr
        have haBc : a ∈ Bc.attestations := List.mem_iff_getElem?.mpr ⟨pos, hpos⟩
        rcases hblockcall with ⟨tt, hjdeliv2, -⟩ | ⟨tt, hjtick2, hemBc2, -⟩
        · obtain ⟨k'', t''', hk''lt, hk''tick, hk''emit⟩ :=
            emission_index_lt_acceptance_carried_attest S rho core j' v Bc tt hjdeliv2 a haBc hu
          have hemK'' : NamedRun.emits S rho a.val_index (.attest a) t''' :=
            ⟨k'', hk''tick, hk''emit⟩
          have ht'''eq : t''' = S.a a.round := row_tick_time_eq_action S rho hemK''
          have hk''tick' : rho.events[k'']? = some (.tick a.val_index t') := by
            rw [← ht'eq] at ht'''eq; rw [ht'''eq] at hk''tick; exact hk''tick
          have hkk'' : k = k'' := tick_index_unique rho core.nodup hk hk''tick'
          exact hkk'' ▸ le_trans hk''lt.le hj'lt.le
        · obtain ⟨e, heE, -, hteqE⟩ := hacc.1.2
          have heEq : e = NamedEvent.tick v tt := Option.some.inj (heE.symm.trans hjtick2)
          have httEq : tt = t'' := by rw [heEq] at hteqE; exact hteqE
          have htle : t' ≤ tt := by rw [ht'eq, httEq]; exact hsend
          have hkj' : k ≤ j' := IH j' hj'lt v tt Bc hjtick2 hemBc2 a haBc hu k t' hk hemit htle
          exact le_trans hkj' hj'lt.le
    · -- Carried branch: `a` sits in an already-held body's attestations.
      obtain ⟨Bc, hBcOrdered, -, haBc, -⟩ :=
        (Proofs.NamedProposalRows.mem_carried_rows S.hc before a).mp hcarried
      have hBcBodies : Bc ∈ before.bodies :=
        Proofs.NamedProposalRows.ordered_bodies_mem hBcOrdered
      have hBcBodiesN : Bc ∈ (NamedRun.stateBefore S rho j v).st.bodies := hBcBodies
      obtain ⟨j', hj'lt, t'', hacc, hsend, -⟩ :=
        Proofs.NamedOutageProvenance.honest_held_ancestor_row_emission S rho
          core.toNamedUnforgeable j v hBcBodiesN (preceq_refl Bc) haBc hu
      rcases hacc.1.1 with ⟨tt, hjtick2, hemBc2⟩ | ⟨tt, hjdeliv2⟩
      · obtain ⟨e, heE, -, hteqE⟩ := hacc.1.2
        have heEq : e = NamedEvent.tick v tt := Option.some.inj (heE.symm.trans hjtick2)
        have httEq : tt = t'' := by rw [heEq] at hteqE; exact hteqE
        have htle : t' ≤ tt := by rw [ht'eq, httEq]; exact hsend
        have hkj' : k ≤ j' := IH j' hj'lt v tt Bc hjtick2 hemBc2 a haBc hu k t' hk hemit htle
        exact le_trans hkj' hj'lt.le
      · obtain ⟨k'', t''', hk''lt, hk''tick, hk''emit⟩ :=
          emission_index_lt_acceptance_carried_attest S rho core j' v Bc tt hjdeliv2 a haBc hu
        have hemK'' : NamedRun.emits S rho a.val_index (.attest a) t''' :=
          ⟨k'', hk''tick, hk''emit⟩
        have ht'''eq : t''' = S.a a.round := row_tick_time_eq_action S rho hemK''
        have hk''tick' : rho.events[k'']? = some (.tick a.val_index t') := by
          rw [← ht'eq] at ht'''eq; rw [ht'''eq] at hk''tick; exact hk''tick
        have hkk'' : k = k'' := tick_index_unique rho core.nodup hk hk''tick'
        exact hkk'' ▸ le_trans hk''lt.le hj'lt.le

theorem emission_index_le_self_proposed_carrier
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (j : Nat) (v : V) (t : Time) (B : NamedBlock V)
    (hj : rho.events[j]? = some (.tick v t))
    (hemB : NamedObject.block B ∈ NamedRun.emittedAt S rho j v t)
    (a : NamedAttestation V) (ha : a ∈ B.attestations) (hu : a.val_index ∈ rho.honest)
    (k : Nat) (t' : Time) (hk : rho.events[k]? = some (.tick a.val_index t'))
    (hemit : NamedObject.attest a ∈ NamedRun.emittedAt S rho k a.val_index t')
    (ht' : t' ≤ t) : k ≤ j :=
  emission_index_le_self_proposed_carrier_aux S rho core j v t B hj hemB a ha hu k t' hk hemit ht'

#print axioms emission_index_le_self_proposed_carrier

end DecoupledConsensusModel.Internal.NamedOutageEntry.History

end
