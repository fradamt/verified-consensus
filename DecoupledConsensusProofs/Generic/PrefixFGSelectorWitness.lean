module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Execution.Acceptance
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.BridgesTail
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import DecoupledConsensusProofs.Execution.FGSelectorWitness
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryCrossingCore
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryPrefix

@[expose] public section

/-!
# Prefix-indexed exact FG-selector witnesses

A finite height crossing carries an honest height row. This module keeps that
row's exact event index, then reconstructs the exact `fg_source` block selected
by its action. The inner crossing of that selected block uses prefix freshness
to place the action inside the recovery interval.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Indexed carried-attestation provenance -/

/-- The indexed strengthening of `Proofs.Bridges.processes_block_of_mem_T`.

The public bridge pairs an earlier event with a time-based `processes` fact,
but does not state that this event itself processes the block. The stronger
local form keeps that link, which is required to turn authenticity's time bound
into a strict event-prefix bound. -/
private theorem processesBlockAtIndex_of_mem_bodies
    (S : Setup V) (rho : Run V) (v : V) (n : Nat)
    {B : NamedBlock V} (hB : B ∈ (rho.stateBefore S n v).st.bodies) :
    B = NamedBlock.genesis ∨
      ∃ j : Nat, j < n ∧
        NamedRun.processesAtIndex S rho j v (.block B) := by
  have hprocessed :
      Object.processed (rho.stateBefore S n v).st (.block B) = true := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
      using hB
  rcases Protocol.acceptsAt_block_of_processed S rho v n B hprocessed with
    hgen | ⟨j, hj, _, hacc⟩
  · exact Or.inl hgen
  · refine Or.inr ⟨j, hj, ?_⟩
    simpa only [NamedRun.actualHandlesAtIndex] using hacc.1.1

omit [Fintype V] in
private theorem namedAncestor_mem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

omit [Fintype V] in
private theorem named_mem_chain_attestations {a : NamedAttestation V} :
    ∀ B : NamedBlock V, a ∈ Protocol.named_chain_attestations B →
      ∃ X : NamedBlock V, NamedBlock.Preceq X B ∧ a ∈ X.attestations := by
  intro B
  induction B with
  | genesis =>
      simp [Protocol.named_chain_attestations, NamedBlock.attestations]
  | node parent slot root votes support rows proposer ih =>
      intro h
      simp only [Protocol.named_chain_attestations, Finset.mem_union,
        List.mem_toFinset] at h
      rcases h with h | h
      · obtain ⟨X, hXB, hX⟩ := ih h
        exact ⟨X, Proofs.NamedAncestry.named_extend slot root votes support rows proposer hXB,
          hX⟩
      · exact ⟨.node parent slot root votes support rows proposer,
          Proofs.NamedAncestry.named_self _, by
            simpa only [NamedBlock.attestations] using h⟩

omit [Fintype V] in
private theorem named_row_mem_chain_of_ancestor
    {A B : NamedBlock V} {a : NamedAttestation V}
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations B := by
  induction B generalizing A with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      subst A
      simp [NamedBlock.attestations] at ha
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      simp only [Protocol.named_chain_attestations, Finset.mem_union,
        List.mem_toFinset]
      rcases hAB with rfl | hparent
      · exact Or.inr ha
      · exact Or.inl (ih hparent ha)

/-- Strict event times determine strict event indices in a sorted run. -/
private theorem eventIndex_lt_of_time_lt
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i j : Nat} {e f : Event V}
    (hi : rho.events[i]? = some e)
    (hj : rho.events[j]? = some f)
    (ht : e.time < f.time) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hji with hji' | rfl
  · have hkey := Proofs.Optimistic.key_le_of_index_lt S sch hji' hj hi
    exact (not_le_of_gt ht) (Proofs.Bridges.time_le_of_key_le hkey)
  · have heq : e = f := Option.some.inj (hi.symm.trans hj)
    exact (lt_irrefl _ (by simpa only [heq] using ht))

/-- At one time, the schedule puts an attestation tick before a block delivery. -/
private theorem tickIndex_lt_delivery_sameTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i j : Nat} {u v : V} {t : Time} {B : NamedBlock V}
    (hi : rho.events[i]? = some (Event.tick u t))
    (hj : rho.events[j]? = some (Event.deliver v (Object.block B) t)) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hji with hji' | rfl
  · have hkey := Proofs.Optimistic.key_le_of_index_lt S sch hji' hj hi
    simp [NamedEvent.key, NamedEvent.time, NamedEvent.phase,
      Prod.Lex.toLex_le_toLex] at hkey
  · cases Option.some.inj (hj.symm.trans hi)

omit [DecidableEq V] [Fintype V] in
private theorem named_height_of_matches
    {a : NamedAttestation V} {H : Height} {root : BlockId}
    (hmatch : NamedHeightPair.matchesEntry H root a.height_pair = true) :
    a.height_pair.erase.height? = some H := by
  cases hp : a.height_pair with
  | empty =>
      simp [hp, NamedHeightPair.matchesEntry] at hmatch
  | vote height entry timeout =>
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hmatch
      cases timeout <;>
        simp [NamedHeightPair.erase, HeightPair.height?, hmatch.1]

set_option maxHeartbeats 1000000 in
/-- An honest attestation carried on a block chain already held in an event
prefix was emitted by an honest tick strictly inside that prefix.

The result keeps both the indexed tick facts and the ordinary `rho.emits`
witness. The latter is needed by the exact action-selector theorem. -/
theorem honestCarriedAttestation_emittedBeforeIndex
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {n : Nat} {v : V} {B : NamedBlock V} {a : NamedAttestation V}
    (hB : B ∈ (rho.stateBefore S n v).st.bodies)
    (ha : a ∈ Protocol.named_chain_attestations B)
    (haHon : a.val_index ∈ rho.honest) :
    ∃ i : Nat, ∃ t : Time,
      i < n ∧
        rho.events[i]? = some (Event.tick a.val_index t) ∧
        Object.attest a ∈
          NamedRun.emittedAt S rho i a.val_index t ∧
        NamedRun.emits S rho a.val_index (Object.attest a) t := by
  obtain ⟨X, hXB, haX⟩ := named_mem_chain_attestations B ha
  have hXT : X ∈ (rho.stateBefore S n v).st.bodies :=
    namedAncestor_mem
      (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1.2.2.1 hB hXB
  rcases processesBlockAtIndex_of_mem_bodies S rho v n hXT with hgen |
      ⟨j, hj, hprocessed⟩
  · simp [hgen, NamedBlock.attestations] at haX
  · simp only [NamedRun.processesAtIndex] at hprocessed
    rcases hprocessed with ⟨tp, hprocessTick, hblockEmit⟩ |
        ⟨tp, hprocessDeliver⟩
    · have hprocess : NamedRun.processes S rho v (.block X) tp :=
        Or.inl ⟨j, hprocessTick, hblockEmit⟩
      obtain ⟨ta, hta, hemit⟩ :=
        adm.toNamedAdmissibleCore.toNamedUnforgeable.carried_attest
          v X tp hprocess a haX haHon
      obtain ⟨i, hi, himit⟩ := hemit
      have hemit' : NamedRun.emits S rho a.val_index (.attest a) ta :=
        ⟨i, hi, himit⟩
      have htaLt : ta < tp := by
        apply lt_of_le_of_ne hta
        intro hEq
        have haction : tp = S.a a.round :=
          hEq.symm.trans (Proofs.Optimistic.emits_attest_shape S hemit').2
        obtain ⟨hguard, -⟩ := block_mem_on_tick_emit S v
          (rho.stateBefore S j v) tp hblockEmit
        exact (Proofs.Optimistic.a_ne_proposal_time S haction) hguard.2.1
      have hij : i < j := eventIndex_lt_of_time_lt S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi hprocessTick htaLt
      exact ⟨i, ta, hij.trans hj, hi, himit, hemit'⟩
    · have hprocess : NamedRun.processes S rho v (.block X) tp :=
        Or.inr ⟨j, hprocessDeliver⟩
      obtain ⟨ta, hta, hemit⟩ :=
        adm.toNamedAdmissibleCore.toNamedUnforgeable.carried_attest
          v X tp hprocess a haX haHon
      obtain ⟨i, hi, himit⟩ := hemit
      rcases lt_or_eq_of_le hta with htaLt | htaEq
      · have hemit' : NamedRun.emits S rho a.val_index (.attest a) ta :=
          ⟨i, hi, himit⟩
        have hij : i < j := eventIndex_lt_of_time_lt S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi hprocessDeliver htaLt
        exact ⟨i, ta, hij.trans hj, hi, himit, hemit'⟩
      · have hi' : rho.events[i]? = some (Event.tick a.val_index tp) := by
          simpa only [htaEq] using hi
        have himit' : Object.attest a ∈
            NamedRun.emittedAt S rho i a.val_index tp := by
          simpa only [htaEq] using himit
        have hemit' : NamedRun.emits S rho a.val_index (.attest a) tp :=
          ⟨i, hi', himit'⟩
        have hij : i < j := tickIndex_lt_delivery_sameTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi' hprocessDeliver
        exact ⟨i, tp, hij.trans hj, hi', himit', hemit'⟩

/-! ## Exact selector from a finite prefix crossing -/

private theorem one_le_derive_named_h
    (E : Env V) (cfg : Protocol.HeightConfig) :
    ∀ B : NamedBlock V, 1 ≤ (Protocol.derive_named E cfg B).h := by
  intro B
  induction B with
  | genesis => exact Nat.le_refl 1
  | node parent slot root votes support rows proposer ih =>
      rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg parent slot root
        votes support rows proposer with hstay | hadvance
      · rw [hstay]
        exact ih
      · rw [hadvance]
        exact le_trans ih (Nat.le_succ _)

/-- A finite honest height crossing yields an honest action inside the crossing
interval, its exact selected `fg_source` block, and the selected block's exact
height. The row may be either a target or a timeout row. -/
theorem prefixHeightCrossing_exactFGSelectorWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start stop : Nat} {blocked : Height}
    (hcross : PrefixHeightCrossingWitness S rho stop blocked)
    (hfresh : Internal.NoLocalHeightPairBefore S rho start blocked) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (B : NamedBlock V) (J : Block V),
      start ≤ i ∧
        i < stop ∧
        a.val_index ∈ rho.honest ∧
        rho.events[i]? = some (Event.tick a.val_index ta) ∧
        Object.attest a ∈ NamedRun.emittedAt S rho i a.val_index ta ∧
        NamedRun.emits S rho a.val_index (Object.attest a) ta ∧
        ta = S.a a.round ∧
        a = actionAttestationAt S rho a.val_index a.round ∧
        actionFGSource S (actionStoreAt S rho a.val_index a.round) =
          some B.erase ∧
        B ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
        ((actionStoreAt S rho a.val_index a.round).st.core.σ B.erase).h =
          blocked + 1 ∧
        (Protocol.derive_named S.E S.cfg B).h = blocked + 1 ∧
        J = (Protocol.derive_named S.E S.cfg B).T_h ∧
        (a.height_pair.erase = HeightPair.target (blocked + 1) J.root ∨
          a.height_pair.erase = HeightPair.timeout (blocked + 1)) := by
  rcases hcross with
    ⟨holder, hholder, carrier, anchor, hcarrier, hanchor,
      hcarrierRun, hanchorRun, hanchorCarrier, hanchorHeight, hcarrierHeight⟩
  have hblockedPos : 1 ≤ blocked := by
    rw [← hanchorHeight]
    exact one_le_derive_named_h S.E S.cfg anchor
  have hnextPos : 1 ≤ blocked + 1 :=
    hblockedPos.trans (Nat.le_add_right blocked 1)
  have hcarrierCross : blocked + 1 <
      (Protocol.derive_named S.E S.cfg carrier).h := by
    rw [hcarrierHeight]
    exact Nat.lt_succ_self (blocked + 1)
  obtain ⟨X, hXcarrier, hXheight, Q, hQ, hrows⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg carrier
      (blocked + 1) hnextPos hcarrierCross
  obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbelow hQ
  obtain ⟨carrier', a, hcarrier', haCarrier, haSigner, haPair⟩ :=
    hrows signer hsignerQ
  have haHon : a.val_index ∈ rho.honest := by
    rw [haSigner]
    exact hsignerHonest
  have haHeight : a.height_pair.erase.height? = some (blocked + 1) :=
    named_height_of_matches haPair
  clear haPair
  have haChain : a ∈ Protocol.named_chain_attestations carrier :=
    named_row_mem_chain_of_ancestor hcarrier' haCarrier
  obtain ⟨i, ta, hiStop, hiEvent, hiEmit, hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hcarrier haChain haHon
  have hselector := honestEmittedHeightRow_exactFGSelectorWitness
    S adm haHon hemit haHeight
  let B : NamedBlock V := Classical.choose hselector
  have hselectorB := Classical.choose_spec hselector
  let J : Block V := Classical.choose hselectorB
  have hselectorBJ := Classical.choose_spec hselectorB
  have hta : ta = S.a a.round := hselectorBJ.1
  have haAction : a = actionAttestationAt S rho a.val_index a.round :=
    hselectorBJ.2.1
  have hsource : actionFGSource S (actionStoreAt S rho a.val_index a.round) =
      some B.erase := hselectorBJ.2.2.1
  have hBmem : B ∈ (actionStoreAt S rho a.val_index a.round).st.bodies :=
    hselectorBJ.2.2.2.1
  have hBstoredHeight :
      ((actionStoreAt S rho a.val_index a.round).st.core.σ B.erase).h =
        blocked + 1 := hselectorBJ.2.2.2.2.1
  have hBderivedHeight :
      (Protocol.derive_named S.E S.cfg B).h = blocked + 1 :=
    hselectorBJ.2.2.2.2.2.1
  have hJderived : J =
      (Protocol.derive_named S.E S.cfg B).T_h :=
    hselectorBJ.2.2.2.2.2.2.1
  have hrow := hselectorBJ.2.2.2.2.2.2.2
  have hiStart : start ≤ i := by
    by_contra hnot
    have hiBeforeStart : i < start := Nat.lt_of_not_ge hnot
    have hstate : rho.stateBefore S i a.val_index =
        rho.stateBeforeTime S ta a.val_index :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hiEvent
    have hBpre : B ∈
        (rho.stateBeforeTime S (S.a a.round) a.val_index).st.bodies := by
      simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hBmem
    have hBAtI : B ∈ (rho.stateBefore S i a.val_index).st.bodies := by
      rw [hstate, hta]
      exact hBpre
    have hBcross : blocked <
        (Protocol.derive_named S.E S.cfg B).h := by
      rw [hBderivedHeight]
      exact Nat.lt_succ_self blocked
    obtain ⟨X0, hX0B, hX0Height, Q0, hQ0, hrows0⟩ :=
      NamedFinalityCertificates.height_crossing S.E S.cfg B blocked
        hblockedPos hBcross
    obtain ⟨signer0, hsigner0Q, hsigner0Honest⟩ :=
      AlignedRoundLemmas.honest_member_of_quorum hbelow hQ0
    obtain ⟨carrier0, a0, hcarrier0, ha0B, ha0Signer, ha0Pair⟩ :=
      hrows0 signer0 hsigner0Q
    have ha0Hon : a0.val_index ∈ rho.honest := by
      rw [ha0Signer]
      exact hsigner0Honest
    have ha0Height : a0.height_pair.erase.height? = some blocked :=
      named_height_of_matches ha0Pair
    have ha0Chain : a0 ∈ Protocol.named_chain_attestations B :=
      named_row_mem_chain_of_ancestor hcarrier0 ha0B
    obtain ⟨k, tk, hkI, hkEvent, hkEmit, hkemit⟩ :=
      honestCarriedAttestation_emittedBeforeIndex S adm hBAtI ha0Chain ha0Hon
    have hkStart : k < start := hkI.trans hiBeforeStart
    exact (hfresh hkStart ha0Hon hkEvent hkEmit ha0Height).elim
  exact ⟨i, a, ta, B, J, hiStart, hiStop, haHon, hiEvent, hiEmit, hemit,
    hta, haAction, hsource, hBmem, hBstoredHeight, hBderivedHeight,
    hJderived, hrow⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
