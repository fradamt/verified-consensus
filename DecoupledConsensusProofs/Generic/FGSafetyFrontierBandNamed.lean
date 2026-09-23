module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HeightRegimeNamedRunAbove
public import DecoupledConsensusProofs.Protocol.ChainState.HeightRegimeNamedBaseDeadline

@[expose] public section

/-!
# Named global frontier witness

The run-scoped named height regime supplies a common checkpoint in the
one-height band below an honest reader's frontier. Unlike the earlier named
frontier interface, the conclusion covers every honest voter, not only voters
in the slot committee.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- An action strictly before a confirmation has reached the slot's first
interior position. This is the clean local twin of the erased frontier
helper. -/
private theorem firstInterior_le_of_action_lt_confirmation_namedFrontier
    (S : Setup V) {r : Round} {s : Slot}
    (hact : S.a r < Protocol.confirmation_time S.E s) :
    S.hc.opening_slot r + 1 ≤ s := by
  by_contra hn
  have hslot : s ≤ S.hc.opening_slot r :=
    Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)
  have hmono : Protocol.confirmation_time S.E s ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot r) := by
    unfold Protocol.confirmation_time
    exact Int.add_le_add_right (proposal_time_mono S.E hslot) _
  change Protocol.confirmation_time S.E (S.hc.opening_slot r) <
    Protocol.confirmation_time S.E s at hact
  exact (not_lt_of_ge hmono) hact

namespace NamedHeightRegimeBaseRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first : Nat} {Tprev : NamedBlock V}

/-- After the base deadline, a named run checkpoint in the reader's frontier
band is below every honest vote-duty head. -/
theorem exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_deadline
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {read : Time} (_hhor : read ≤ rho.horizon)
    {s : Slot} (hs : S.hc.opening_slot deadline + 1 ≤ s)
    (hnext : read ≤ Protocol.confirmation_time S.E s)
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u : V} (_hu : u ∈ rho.honest) :
    ∃ T : NamedBlock V,
      RunBlock S rho T ∧
      (rho.storeBeforeTime S u read).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg T).h ∧
      ∀ w ∈ rho.honest, T.erase ⪯ voterHeadAt S rho w s := by
  let st := rho.storeBeforeTime S u read
  by_cases hlow : st.h_max - 1 ≤ blocked + 1
  · obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
      h.exists_regime_closed adm hbelow hgst
    have hi : i < inclusiveEventIndex rho (S.a deadline) :=
      hreg.seed.indexLtStop.trans_le hdeadline
    have hfilter :
        rho.events.filter (fun e => decide (e.time ≤ S.a deadline)) =
          rho.events.take (inclusiveEventIndex rho (S.a deadline)) := by
      simpa only [inclusiveEventIndex] using
        Proofs.Optimistic.filter_eq_take S adm.toNamedScheduleWellFormed _
          (Proofs.Optimistic.downward_le (S.a deadline))
    have hmem : Event.tick a.val_index ta ∈
        rho.events.take (inclusiveEventIndex rho (S.a deadline)) := by
      apply List.mem_of_getElem? (i := i)
      rw [List.getElem?_take_of_lt hi]
      exact hreg.seed.exactTick
    rw [← hfilter] at hmem
    have haround : a.round ≤ deadline := by
      apply (action_strictMono S).le_iff_le.mp
      simpa only [Event.time, hreg.seed.actionTime_eq, decide_eq_true_eq] using
        (List.mem_filter.mp hmem).2
    obtain ⟨hTrun, hTheight⟩ := hreg.checkpoint_runBlock adm
    refine ⟨T, hTrun, ?_, ?_⟩
    · rw [hTheight]
      exact hlow
    · exact hreg.heads_from_firstInterior adm hcom hbelow
        ((Nat.add_le_add_right
          (Nat.mul_le_mul_right S.hc.R haround) 1).trans hs)
        hshor
  · have hlarge : 1 < st.h_max := by
      apply Nat.sub_pos_iff_lt.mp
      exact (Nat.zero_le (blocked + 1)).trans_lt
        (Nat.lt_of_not_ge hlow)
    obtain ⟨a, ta, _D, _K, ha, hemit, hta, hrow, _hfg,
        _hDmem, _hKmem, _hKentry, _hKrun, _hKheight⟩ :=
      frontier_confirmationWitness S adm
        (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
        hlarge
    let n := (st.h_max - 1) - (blocked + 1)
    have heq : blocked + n + 1 = st.h_max - 1 := by
      calc
        blocked + n + 1 = n + (blocked + 1) := by ac_rfl
        _ = st.h_max - 1 := Nat.sub_add_cancel
          (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
    have hrow' :
        a.height_pair.erase.height? = some (blocked + n + 1) := by
      rw [heq]
      exact hrow
    obtain ⟨first_n, i, source, tsource, Cfg, T, Tprev', c0, hreg⟩ :=
      h.exists_regime_of_row_named adm hcom hbelow hgst n ha hemit hrow'
    have hactionLt : S.a a.round < read := by
      rw [← (Proofs.Optimistic.emits_attest_shape S hemit).2]
      exact hta
    have hsourceRound : source.round ≤ a.round :=
      hreg.minimal a ta ha hemit hrow'
    have hslot : S.hc.opening_slot source.round + 1 ≤ s :=
      (Nat.add_le_add_right
        (Nat.mul_le_mul_right S.hc.R hsourceRound) 1).trans
          (firstInterior_le_of_action_lt_confirmation_namedFrontier S
            (hactionLt.trans_le hnext))
    obtain ⟨hTrun, hTheight⟩ := hreg.checkpoint_runBlock adm
    refine ⟨T, hTrun, ?_, ?_⟩
    · rw [hTheight, heq]
    · exact hreg.heads_from_firstInterior adm hcom hbelow hslot hshor

#print axioms NamedHeightRegimeBaseRun.exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_deadline

end NamedHeightRegimeBaseRun

/-- Bounded recovery supplies the named global frontier witness after its
progress deadline. -/
theorem exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {read : Time}
    (hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot}
    (hs : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hnext : read ≤ Protocol.confirmation_time S.E s)
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u : V} (hu : u ∈ rho.honest) :
    ∃ T : NamedBlock V,
      RunBlock S rho T ∧
      (rho.storeBeforeTime S u read).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg T).h ∧
      ∀ w ∈ rho.honest, T.erase ⪯ voterHeadAt S rho w s := by
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost (hread.trans hhor)
  exact hbase.exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_deadline
    adm hcom hbelow (gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost)
      hfirst hhor hs hnext hshor hu

#print axioms exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
