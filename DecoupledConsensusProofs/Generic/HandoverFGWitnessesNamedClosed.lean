module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HeightRegimeNamedRunAbove
public import DecoupledConsensusProofs.Protocol.ChainState.HeightRegimeNamedBaseDeadline
public import DecoupledConsensusProofs.Objects.WeakLegacySources
public import DecoupledConsensusProofs.Execution.FGSafetyProgressDeadline
public import DecoupledConsensusProofs.Objects.GSTZeroPreviousConfirmation

@[expose] public section

/-!
# Closed aggregate FG witnesses below the handover carrier
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem actionBody_runBlock_handover
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈
      (NamedRun.stateBeforeTime S rho (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨j, hj, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDj : D ∈ (rho.stateBefore S j v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho j v).st.bodies
    rw [← hj]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv j hDj)


/-- A lifecycle records identifies the prepared opening vote head. -/
private theorem voterHeadAt_eq_proposal_of_packet
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {s : Slot} {P : NamedBlock V}
    (hpacket : NamedSGProposalLifecyclePacket S rho r s P)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r + 1)) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hcommittee : v ∈ S.E.committee (S.hc.opening_slot (r + 1))) :
    voterHeadAt S rho v (S.hc.opening_slot (r + 1)) = P.erase := by
  have hPemit := hpacket.honestVotes v hv hcommittee
  obtain ⟨hpositiveRaw, -, -, hslot⟩ :=
    Proofs.Optimistic.emits_gfVote_shape S hPemit
  have hpositive : 0 < S.hc.opening_slot (r + 1) := by
    simpa only [← hslot] using hpositiveRaw
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot (r + 1)) ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E _).trans hhor
  obtain ⟨C, hChead, hCrun, hCemit⟩ :=
    named_voter_head_emits S adm hv hpositive hcommittee hvoteHor
  have hvoteEq :
      (⟨v, S.hc.opening_slot (r + 1), C.erase.root⟩ : GoldfishVote V) =
        ⟨v, S.hc.opening_slot (r + 1), P.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
      hCemit hPemit rfl
  have hroot : C.root = P.root := by
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root P]
    exact congrArg GoldfishVote.head hvoteEq
  have hCP : C = P :=
    adm.toNamedRootCollisionFree.root_injective C P hCrun
      hpacket.lifecycle.runBlock C P
      (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self P)) hroot
  calc
    voterHeadAt S rho v (S.hc.opening_slot (r + 1)) = C.erase :=
      hChead.symm
    _ = P.erase := congrArg NamedBlock.erase hCP

theorem fgWitness_preceq_carrierProposal_of_namedHeightRegimeRun
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r0 : Round} {blocked : Height} {first i : Nat}
    {a : NamedAttestation V} {ta : Time}
    {Cfg K Tprev : NamedBlock V} {c0 : Round}
    (hreg : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg K Tprev c0)
    {b : NamedAttestation V} {tb : Time} {W : Block V}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    {q : Round} (hbefore : b.round < q) (hq : 1 ≤ q)
    {P : NamedBlock V}
    (hpacket : NamedSGProposalLifecyclePacket S rho (q - 1)
      (S.hc.opening_slot q - 1) P)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hwitness : fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some W) :
    Block.Preceq W P.erase := by
  have hsourceBefore : a.round < q :=
    (hreg.minimal b tb hb hemit hrow).trans_lt hbefore
  have hslot : S.hc.opening_slot a.round + 1 ≤ S.hc.opening_slot q := by
    have hnext : S.hc.opening_slot a.round + 1 <
        S.hc.opening_slot (a.round + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
        Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          (a.round * S.hc.R)
    exact (Nat.le_of_lt hnext).trans
      (Nat.mul_le_mul_right S.hc.R hsourceBefore)
  have htime : ∀ p d : Int, 0 < d → p + d + d ≤ p + 6 * d := by
    intro p d hd
    omega
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot q) + S.E.Δ ≤
      rho.horizon := (htime _ _ S.E.Δ_pos).trans hhor
  have hKW : K.erase = W := Option.some.inj
    ((hreg.witness_eq adm hcom hbelow hb hemit hrow).symm.trans hwitness)
  obtain ⟨w, hw, hcommittee⟩ :=
    Protocol.HonestWeightMajority.exists_honest_committee_member
      hcom (S.hc.opening_slot q)
  have hKhead := hreg.heads_from_firstInterior adm hcom hbelow
    hslot hvoteHor w hw
  have hhead : voterHeadAt S rho w (S.hc.opening_slot q) = P.erase := by
    simpa only [Nat.sub_add_cancel hq] using
      voterHeadAt_eq_proposal_of_packet S adm hpacket
        (by simpa only [Nat.sub_add_cancel hq] using hhor) hw
        (by simpa only [Nat.sub_add_cancel hq] using hcommittee)
  rw [hKW, hhead] at hKhead
  exact hKhead

#print axioms
  fgWitness_preceq_carrierProposal_of_namedHeightRegimeRun



/-- All honest FG witnesses in the finite B7 interval are below a carrier
proposal whose prepared opening head is known at every honest voter. -/
theorem fgWitnessesBelow_of_namedHeightRegimeBaseRun_of_headEq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {r0 : Round} (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hbase : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {rGST gap : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho
      (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)))
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra + 1 + S.hc.η_SG ≤ m)
    {P : NamedBlock V}
    (hheads : ∀ w ∈ rho.honest,
      voterHeadAt S rho w (S.hc.opening_slot m) = P.erase)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    WeakJoint.FGWitnessesBelow S rho
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1)
      (fgSafetyProgressDeadline S rho rGST gap delayExtra +
        2 * progressLag' gap delayExtra + 1) P.erase := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let L := progressLag' gap delayExtra
  have hmPos : 1 ≤ m := by
    have hpos : 1 ≤ D + 2 * L + 1 + S.hc.η_SG :=
      (Nat.le_add_left 1 (D + 2 * L)).trans
        (Nat.le_add_right (D + 2 * L + 1) S.hc.η_SG)
    exact hpos.trans (by simpa only [D, L] using hm)
  have hDm : D < m := by
    have hle : D + 1 ≤ D + 2 * L + 1 + S.hc.η_SG :=
      (Nat.add_le_add_right (Nat.le_add_right D (2 * L)) 1).trans
        (Nat.le_add_right (D + 2 * L + 1) S.hc.η_SG)
    exact lt_of_lt_of_le (Nat.lt_succ_self D)
      (hle.trans (by simpa only [D, L] using hm))
  intro b tb height W hb hemit hrow hfresh hold hwitness
  have hbefore : b.round < m :=
    hold.trans_le (by simpa only [D, L] using hm)
  by_cases hsmall : height ≤ blocked
  · obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
      hbase.exists_regime_closed adm hbelow hgst
    have hi : i < inclusiveEventIndex rho (S.a D) :=
      hreg.seed.indexLtStop.trans_le (by simpa only [D] using hdeadline)
    have hfilter :
        rho.events.filter (fun e => decide (e.time ≤ S.a D)) =
          rho.events.take (inclusiveEventIndex rho (S.a D)) := by
      simpa only [inclusiveEventIndex] using
        Proofs.Optimistic.filter_eq_take S adm.toNamedScheduleWellFormed _
          (Proofs.Optimistic.downward_le (S.a D))
    have hmem : Event.tick a.val_index ta ∈
        rho.events.take (inclusiveEventIndex rho (S.a D)) := by
      apply List.mem_of_getElem? (i := i)
      rw [List.getElem?_take_of_lt hi]
      exact hreg.seed.exactTick
    rw [← hfilter] at hmem
    have htime : S.a a.round ≤ S.a D := by
      simpa only [Event.time, hreg.seed.actionTime_eq,
        decide_eq_true_eq] using (List.mem_filter.mp hmem).2
    have haround : a.round ≤ D := (action_strictMono S).le_iff_le.mp htime
    have hround : a.round + 1 ≤ b.round :=
      (Nat.add_le_add_right haround 1).trans (by simpa only [D] using hfresh)
    obtain ⟨source, K, hW, hsourceMem, _hsource, hsourceHeight,
        hKmem, hKerase, hKheight, hKsource, _hshape⟩ :=
      honestHeightRow_confirmationWitness S adm hb hemit hrow
    have hrowHor : S.a b.round ≤ rho.horizon := by
      have hbtime := (Proofs.Optimistic.emits_attest_shape S hemit).2
      obtain ⟨j, hevent, -⟩ := hemit
      simpa only [Event.time, hbtime] using
        (adm.in_horizon _ (List.mem_of_getElem? hevent)).2
    have hcompat :=
      ((hreg.laterHistory_main adm hcom hbelow hround).2 hrowHor).2
        b.val_index hb (Protocol.derive_named S.E S.cfg K).T_h hW
    have hsourceRun : RunBlock S rho source :=
      actionBody_runBlock_handover S adm hb hsourceMem
    have hKrun : RunBlock S rho K :=
      actionBody_runBlock_handover S adm hb hKmem
    have hKsourceNamed :=
      Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hKrun hsourceRun hKsource
    have hKfixed :
        (Protocol.derive_named S.E S.cfg K).T_h = K.erase :=
      (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKsourceNamed
        (hKheight.trans hsourceHeight.symm)).trans hKerase.symm
    have hWK : W = K.erase := by
      apply Option.some.inj
      exact hwitness.symm.trans (by simpa only [hKfixed] using hW)
    have hKT : Block.Preceq K.erase T.erase := by
      have hcompat' : Block.compatible K.erase T.erase = true := by
        simpa only [hKfixed] using hcompat
      rcases (show Block.Preceq K.erase T.erase ∨
          Block.Preceq T.erase K.erase by
        simpa only [Block.compatible, Bool.or_eq_true] using hcompat') with
        hKT | hTK
      · exact hKT
      · obtain ⟨hTrun, hTheight⟩ := hreg.checkpoint_runBlock adm
        have hTKnamed :=
          Protocol.namedPreceq_of_runBlock_erase_preceq
            adm hTrun hKrun hTK
        have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTKnamed
        rw [hTheight, hKheight] at hmono
        exact False.elim
          (Nat.not_succ_le_self blocked (hmono.trans hsmall))
    have hsourceBefore : a.round < m := haround.trans_lt hDm
    have hslot : S.hc.opening_slot a.round + 1 ≤ S.hc.opening_slot m := by
      have hnext : S.hc.opening_slot a.round + 1 <
          S.hc.opening_slot (a.round + 1) := by
        simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul,
          Nat.one_mul] using
          Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
            (a.round * S.hc.R)
      exact (Nat.le_of_lt hnext).trans
        (Nat.mul_le_mul_right S.hc.R hsourceBefore)
    have hdelta : ∀ p d : Int, 0 < d → p + d + d ≤ p + 6 * d := by
      intro p d hd
      omega
    have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot m) +
        S.E.Δ ≤ rho.horizon := (hdelta _ _ S.E.Δ_pos).trans hhor
    obtain ⟨w, hw⟩ := honest_nonempty_of_honestCommittees hcom
    have hThead := hreg.heads_from_firstInterior adm hcom hbelow
      hslot hvoteHor w hw
    rw [hheads w hw] at hThead
    rw [hWK]
    exact Block.preceq_trans hKT hThead
  · let n := height - (blocked + 1)
    have heq : blocked + n + 1 = height := by
      dsimp only [n]
      calc
        blocked + (height - (blocked + 1)) + 1 =
            (height - (blocked + 1)) + (blocked + 1) := by ac_rfl
        _ = height := Nat.sub_add_cancel (Nat.lt_of_not_ge hsmall)
    obtain ⟨first_n, i, a, ta, Cfg, K, Tprev', c0, hreg⟩ :=
      hbase.exists_regime_of_row_named adm hcom hbelow hgst n
        hb hemit (heq.symm ▸ hrow)
    have hsourceBefore : a.round < m :=
      (hreg.minimal b tb hb hemit (heq.symm ▸ hrow)).trans_lt hbefore
    have hslot : S.hc.opening_slot a.round + 1 ≤ S.hc.opening_slot m := by
      have hnext : S.hc.opening_slot a.round + 1 <
          S.hc.opening_slot (a.round + 1) := by
        simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul,
          Nat.one_mul] using
          Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
            (a.round * S.hc.R)
      exact (Nat.le_of_lt hnext).trans
        (Nat.mul_le_mul_right S.hc.R hsourceBefore)
    have hdelta : ∀ p d : Int, 0 < d → p + d + d ≤ p + 6 * d := by
      intro p d hd
      omega
    have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot m) +
        S.E.Δ ≤ rho.horizon := (hdelta _ _ S.E.Δ_pos).trans hhor
    have hKW : K.erase = W := Option.some.inj
      ((hreg.witness_eq adm hcom hbelow hb hemit
        (heq.symm ▸ hrow)).symm.trans hwitness)
    obtain ⟨w, hw⟩ := honest_nonempty_of_honestCommittees hcom
    have hKhead := hreg.heads_from_firstInterior adm hcom hbelow
      hslot hvoteHor w hw
    rw [hKW, hheads w hw] at hKhead
    exact hKhead

#print axioms fgWitnessesBelow_of_namedHeightRegimeBaseRun_of_headEq



end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
