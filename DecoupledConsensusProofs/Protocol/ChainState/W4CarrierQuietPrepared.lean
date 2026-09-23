module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.W4CarrierFirstHalf
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Quiet first-half rows at the previous honest opening
The selected D2 carrier has an honest previous opening. The prepared duty
places that opening's anchor below its named proposal, and the action live
confirmation equals that proposal. The source of an honest height row is
therefore below the same named proposal in either prepared selector tier.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An honest row at the selected carrier's previous opening cannot have
height above that opening's named proposal. This is earlier's `k = r - 1`
source-to-live step, restated over the prepared duty and named height. -/
theorem w4_quietPreviousRow_height_le_namedOpening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {k : Round} (hk : 0 < k) (hhor : S.a k ≤ rho.horizon)
    {Pprev : NamedBlock V} (hPrun : RunBlock S rho Pprev)
    (hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v k).st.core.live_confirmed = Pprev.erase)
    (hanchor : ∀ v ∈ rho.honest,
      Block.Preceq (PhaseGrades.nodeAnchor S (actionReadAt S rho v k) k)
        Pprev.erase)
    {v : V} (hv : v ∈ rho.honest) {H : Height}
    (hrow : (actionAttestationAt S rho v k).height_pair.erase.height? = some H) :
    H ≤ (Protocol.derive_named S.E S.cfg Pprev).h := by
  obtain ⟨Q, hsource, hmem, hheight⟩ :=
    honestRow_height_le_source S adm hv hrow
  have hQbodyPre : Q ∈ (rho.stateBeforeTime S (S.a k) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hmem
  obtain ⟨N, hN, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a k)
  have hQrun : RunBlock S rho Q := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := N)
    simpa only [hN] using hQbodyPre
  have hsourceStore : actionFGSource S (actionStoreAt S rho v k) =
      some Q.erase := hsource
  obtain ⟨A, hA⟩ := w4NodeQ2_of_actionFGSource S rho v k hsourceStore
  have hQP : Block.Preceq Q.erase Pprev.erase := by
    rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho v k hA hsourceStore with hclear | hselected
    · obtain ⟨C, -, hClive, -, -, hQC⟩ := hclear
      rw [hClive, hlive v hv] at hQC
      exact hQC
    · rw [hselected]
      exact Block.preceq_trans
        (actionQ2_preceq_actionAnchor S adm.toNamedAdmissibleCore
          hv hk hhor hA) (hanchor v hv)
  have hnamed : NamedBlock.Preceq Q Pprev :=
    namedPreceq_of_runBlock_erase_preceq adm hQrun hPrun hQP
  rw [← hheight]
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed

#print axioms w4_quietPreviousRow_height_le_namedOpening

/-- The actual selected carrier's honest predecessor has the named
height-source history earlier reads in its early-row quiet case. The recovery
deadline, delay bound and honest proposer come from the selected D3/D2 spine;
no all-slot endpoint family is assumed. -/
theorem w4_quietPreviousHistory_of_spine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} {extra : Nat}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S extra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round}
    (hq0 : fgSafetyProgressDeadline S rho rGST gap extra + 3 ≤ q0)
    (hqr : q0 + 2 < r)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    {Pprev : NamedBlock V} (hPprevRun : RunBlock S rho Pprev)
    (hPprev : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) =
      some Pprev) :
    CanonicalHeightSourceHistoryAt S rho q0 (r - 1) Pprev := by
  let m := r - 1
  have harith : ∀ (D q r : Nat), D + 3 ≤ q → q + 2 < r →
      0 < r - 1 ∧ D + 2 ≤ r - 1 := by
    intro D q r hD hqr'
    omega
  obtain ⟨hmpos, hdeadlineM⟩ :=
    harith (fgSafetyProgressDeadline S rho rGST gap extra) q0 r hq0 hqr
  have hgeom : S.hc.opening_slot (m - 1) + 1 ≤ S.hc.opening_slot m := by
    have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hmpos)
    have hstep : S.hc.opening_slot (m - 1) + 1 ≤
        S.hc.opening_slot ((m - 1) + 1) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left
        ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two)
        ((m - 1) * S.hc.R)
    rwa [hmEq] at hstep
  have hhorVote : Protocol.vote_time S.E (S.hc.opening_slot m) + S.E.Δ ≤
      rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E _).trans
      (by simpa only [m, opening_confirmation_time_eq_action S] using hprevHor)
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hheads := w4cr_openingHeads_atRound S adm hcom hbelow hrec hdelay
    hpost hdeadlineM hprev hprevHor hPprev
  exact w4cr_canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named_of_carrierWindows
    S adm hcom hbelow hrec hdelay hpost hq0 hgeom hhorVote hw
    hPprevRun (hheads w hw).symm

#print axioms w4_quietPreviousHistory_of_spine

/-- A matching honest row of the slot-`+1` fold was emitted before the
carrier's own action. The `+1` proposal is already in every honest action
reader's prepared filtered tree; its named body is thus held before that
action, and named authenticity gives the strict round bound for every row
on its ancestor chain. -/
theorem w4_quietFoldProgress_row_beforeCarrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {P0 P1 : NamedBlock V}
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hparent : NamedBlock.parent? P1 = some P0)
    (hP1run : RunBlock S rho P1)
    {v : V} (hv : v ∈ rho.honest)
    (hvprog : v ∈ (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase
      P1.attestations).progress) :
    ∃ k : Round, k < r ∧
      (actionAttestationAt S rho v k).height_pair.erase.height? =
        some (Protocol.derive_named S.E S.cfg P0).h := by
  have hfiltered := hround.plusOneCandidate v hv P1 hP1
  have htree : P1.erase ∈ (actionStoreAt S rho v r).st.core.T :=
    mem_T_of_mem_filteredTree hfiltered
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
      (actionStoreAt S rho v r).st := by
    have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
        (actionStoreAt S rho v r).st := by
      apply Proofs.NamedConfirmationMembership.invariant_update
      exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
    exact hinv.1.1
  have hview : (actionStoreAt S rho v r).st.core.T =
      (actionStoreAt S rho v r).st.bodies.image NamedBlock.erase := hcoh.1
  rw [hview] at htree
  obtain ⟨D, hD, hDE⟩ := Finset.mem_image.mp htree
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hD
  obtain ⟨N, hN, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDrun : RunBlock S rho D := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := N)
    simpa only [hN] using hDpre
  have hDP : D = P1 :=
    adm.toNamedRootCollisionFree.root_injective D P1 hDrun hP1run D P1
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self P1))
      (by rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root P1, hDE])
  have hP1pre : P1 ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    rw [← hDP]
    exact hDpre
  obtain ⟨carrier, a, hcarrier, ha, hval, hmatch⟩ :=
    carrierPlusOneFold_progressRow S hparent hvprog
  have haHon : a.val_index ∈ rho.honest := by rw [hval]; exact hv
  obtain ⟨hbefore, hem⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_before_action S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      adm.toNamedAdmissibleCore.toNamedUnforgeable v r hP1pre hcarrier ha haHon
  have haeq : a = actionAttestationAt S rho v a.round := by
    have h := emittedHonestAttestation_eq_actionAttestationAt S adm hem
    simpa only [hval] using h
  have hheight : a.height_pair.erase.height? =
      some (Protocol.derive_named S.E S.cfg P0).h := by
    cases hp : a.height_pair with
    | empty => simp [NamedHeightPair.matchesEntry, hp] at hmatch
    | vote height entry timeout =>
        simp only [NamedHeightPair.matchesEntry, hp, decide_eq_true_eq] at hmatch
        cases timeout <;>
          simpa [NamedHeightPair.erase, HeightPair.height?] using hmatch.1
  refine ⟨a.round, hbefore, ?_⟩
  rw [← haeq]
  exact hheight

#print axioms w4_quietFoldProgress_row_beforeCarrier

/-- The named previous-opening height below `H` rules out every honest
progress or target row in the carrier's slot-`+1` fold. Early rows use the
previous opening's height-source history; the last row uses the prepared
source-to-live bound. -/
theorem w4_quietRows_of_namedPreviousHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {Pprev P0 P1 : NamedBlock V}
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hparent : NamedBlock.parent? P1 = some P0)
    (hP1run : RunBlock S rho P1)
    (hPprevRun : RunBlock S rho Pprev)
    (hqr : q0 + 2 < r)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q0 (r - 1) Pprev)
    (hPrevNamedBelow : (Protocol.derive_named S.E S.cfg Pprev).h <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v (r - 1)).st.core.live_confirmed = Pprev.erase)
    (hanchor : ∀ v ∈ rho.honest,
      Block.Preceq
        (PhaseGrades.nodeAnchor S (actionReadAt S rho v (r - 1)) (r - 1))
        Pprev.erase) :
    (∀ v ∈ (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations).target_participation, v ∉ rho.honest) ∧
      (∀ v ∈ (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations).progress, v ∉ rho.honest) := by
  have hsplit : ∀ (q r k : Nat), q + 2 < r → k < r →
      k < r - 1 ∨ k = r - 1 := by
    intro q r k hqr' hkr'
    omega
  have hprogress : ∀ v ∈ (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase
      P1.attestations).progress, v ∉ rho.honest := by
    intro v hvprog hvhon
    obtain ⟨k, hkr, hrow⟩ :=
      w4_quietFoldProgress_row_beforeCarrier S adm hround hP1 hparent
        hP1run hvhon hvprog
    have hq0k : q0 < k := honestRow_after_frontier S adm hvhon habove hrow
    rcases hsplit q0 r k hqr hkr with hearly | hlast
    · exact w4_noHonestRowAtHeight_early S (EndN := fun _ => Pprev)
        hhistPrev hPrevNamedBelow
        (Nat.le_of_lt hq0k) hearly hvhon hrow
    · subst k
      have hkpos : 0 < r - 1 := Nat.lt_of_le_of_lt (Nat.zero_le q0) hq0k
      have hle := w4_quietPreviousRow_height_le_namedOpening S adm
        hkpos hprevHor hPprevRun hlive hanchor hvhon hrow
      exact absurd hle (Nat.not_le_of_lt hPrevNamedBelow)
  refine ⟨?_, hprogress⟩
  intro v hvtarget
  exact hprogress v
    ((carrierPlusOneFold_matchingWitnesses S hparent).1 hvtarget)

#print axioms w4_quietRows_of_namedPreviousHistory

/-- The scoped quiet arm from the actual selected carrier and retained D3
spine facts. This replaces the previous erased-height quiet branch; `Pprev` is
the honest predecessor opening and the case split is on its named height.
No endpoint family or named/erased derivation bridge is used. -/
theorem w4_quietRows_of_selectedCarrierSpine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} {extra : Nat}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S extra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round}
    (hq0 : fgSafetyProgressDeadline S rho rGST gap extra + 3 ≤ q0)
    (hqr : q0 + 2 < r)
    {Pprev P0 P1 : NamedBlock V}
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hparent : NamedBlock.parent? P1 = some P0)
    (hP1run : RunBlock S rho P1)
    (hPprevRun : RunBlock S rho Pprev)
    (hPprev : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) =
      some Pprev)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hpred : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hPrevNamedBelow : (Protocol.derive_named S.E S.cfg Pprev).h <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v (r - 1)).st.core.live_confirmed = Pprev.erase)
    (hanchor : ∀ v ∈ rho.honest,
      Block.Preceq
        (PhaseGrades.nodeAnchor S (actionReadAt S rho v (r - 1)) (r - 1))
        Pprev.erase) :
    (∀ v ∈ (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations).target_participation, v ∉ rho.honest) ∧
      (∀ v ∈ (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations).progress, v ∉ rho.honest) := by
  have hhistPrev := w4_quietPreviousHistory_of_spine S adm hcom hbelow
    hrec hdelay hpost hq0 hqr hprevHor hpred hPprevRun hPprev
  exact w4_quietRows_of_namedPreviousHistory S adm hround hP1 hparent
    hP1run hPprevRun hqr habove hhistPrev hPrevNamedBelow hprevHor
    hlive hanchor

#print axioms w4_quietRows_of_selectedCarrierSpine

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
