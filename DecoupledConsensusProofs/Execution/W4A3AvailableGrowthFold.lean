module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads
public import DecoupledConsensusInternal.Definitions.Confirmation
public import DecoupledConsensusInternal.Legacy.Assumptions.Recurrence
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# W4 A3 — named two-proposal available-growth fold

Named-witness proof of the body of `Protocol.availableChainGrowthFrom_of_userProposals`
(`WeakAvailableChainGrowthRun.lean:19-86`, both trees): the same two honest
proposal records and the same monotonicity argument, now concluding a named
`NamedBlock` witness rather than the retired total `proposedBlock` reader.
See the liveness audit `the proof record` §5 A3.

The existing `Protocol.availableChainGrowthFrom_of_userProposals` in
`WeakAvailableChainGrowthRun.lean` still uses the retired total `proposedBlock`
and does not type-check against the current (named) `AvailableChainGrowthFrom`
and `UserProposalsConfirmedAfter`; that file is left untouched (/frozen
layer discipline) and this is a new clean leaf.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace W4

open Internal Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Exact honest-proposal records and monotonicity give a strict common
advance within each opening-carrier window, over named witnesses. No
execution or fault premise is added to the two input properties. -/
theorem availableChainGrowthFrom_of_userProposals
    (S : Setup V) {rho : Run V} {start : Slot} {gap : Round}
    (hmono : ConfirmationMonotoneFrom S rho (Protocol.confirmation_time S.E start))
    (hprops : UserProposalsConfirmedAfter S rho start)
    (hrec : ProposerOpeningCarrierRecurrence S rho gap)
    (hGSTStart : S.E.t_GST ≤ Protocol.proposal_time S.E start) :
    AvailableChainGrowthFrom S rho start gap := by
  intro r hstart hhor
  obtain ⟨c, hclo, hchi, _, hp1, hcarrier⟩ := hrec r
    (hGSTStart.trans (Protocol.proposal_time_mono S.E hstart))
    ((Proofs.HealingLemmas.openingProposal_window_le_action S r gap).trans hhor)
  have hp2 := hcarrier.1
  have harith : ∀ x y : Nat, x + 2 ≤ y → x < y - 1 ∧ y - 1 < y := by
    intro x y hxy
    omega
  obtain ⟨hr1, h12⟩ := harith r c hclo
  have hR : 0 < S.hc.R := lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hs01 : S.hc.opening_slot r < S.hc.opening_slot (c - 1) :=
    Nat.mul_lt_mul_of_pos_right hr1 hR
  have hs12 : S.hc.opening_slot (c - 1) < S.hc.opening_slot c :=
    Nat.mul_lt_mul_of_pos_right h12 hR
  have ht01 : S.a r ≤ S.a (c - 1) := Assembly.a_mono S hr1.le
  have ht12 : S.a (c - 1) ≤ S.a c := Assembly.a_mono S h12.le
  have ht2hi : S.a c ≤ S.a (r + gap) := Assembly.a_mono S hchi
  have htstart : Protocol.confirmation_time S.E start ≤ S.a r := by
    change Protocol.confirmation_time S.E start ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot r)
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact Proofs.Optimistic.support_cutoff_mono S.E (Nat.succ_le_succ hstart)
  have hconf1 : Protocol.confirmation_time S.E (S.hc.opening_slot (c - 1)) ≤
      rho.horizon := ht12.trans (ht2hi.trans hhor)
  have hconf2 : Protocol.confirmation_time S.E (S.hc.opening_slot c) ≤
      rho.horizon := ht2hi.trans hhor
  obtain ⟨B1, hB1, hfirst1, hfirst2⟩ :=
    hprops _ (hstart.trans_lt hs01) hconf1 hp1
  obtain ⟨B2, hB2, hsecond1, hsecond2⟩ :=
    hprops _ ((hstart.trans_lt hs01).trans hs12) hconf2 hp2
  have hfirstAt (v : V) (hv : v ∈ rho.honest) :
      (rho.storeAt S v (S.a (c - 1))).latest_confirmed = B1.erase := hfirst1 v hv
  have hsecondAt (v : V) (hv : v ∈ rho.honest) :
      (rho.storeAt S v (S.a c)).latest_confirmed = B2.erase := hsecond1 v hv
  have hP12 : Block.Preceq B1.erase B2.erase := by
    have h := hmono _ hp1 _ _ (htstart.trans ht01) ht12 hconf2
    rw [hfirstAt _ hp1, hsecondAt _ hp1] at h
    exact h
  have hne : B1.erase ≠ B2.erase := by
    intro heq
    have hs := congrArg Block.slot heq
    rw [Proofs.NamedWire.erase_slot, Proofs.NamedWire.erase_slot,
      DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho _ hB1,
      DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho _ hB2] at hs
    exact (Nat.ne_of_lt hs12) hs
  refine ⟨S.hc.opening_slot c, hs01.trans hs12, hp2, ht2hi, B2, hB2, ?_, ?_⟩
  · intro v hv
    refine ⟨hsecond1 v hv, ?_⟩
    have h01 := hmono v hv _ _ htstart ht01 hconf1
    rw [hfirstAt v hv] at h01
    have h02 := Block.preceq_trans h01 hP12
    have hneq : (rho.storeAt S v (S.a r)).latest_confirmed ≠ B2.erase := by
      intro heq
      rw [heq] at h01
      exact hne (Block.preceq_antisymm hP12 h01)
    simp only [Block.Prec, Block.prec, hneq, decide_false,
      Bool.not_false, Bool.true_and]
    exact h02
  · intro v hv t ht hthor
    have h := hmono v hv _ _ (htstart.trans (ht01.trans ht12)) ht hthor
    rw [hsecondAt v hv] at h
    exact ⟨h, hsecond2 v hv t ht hthor⟩

#print axioms availableChainGrowthFrom_of_userProposals

end W4
end Proofs
end DecoupledConsensusModel

end
