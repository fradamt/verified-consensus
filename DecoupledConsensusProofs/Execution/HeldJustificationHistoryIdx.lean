module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Execution.EventIndexBridge
public import DecoupledConsensusProofs.Execution.IdxGaps
public import DecoupledConsensusProofs.Execution.ViabilityHistoryIndices
public import DecoupledConsensusProofs.Protocol.Handlers.HandlerAdmissionGuards
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance

@[expose] public section

/-!
# Index-bounded guard proofs (task 5)

`held_justification_checkpoint_on_history`, copied from `HandlerAdmissionGuards.lean`
with the index hypotheses in place of the time cut, reusing the same
provenance route (and the same recorded gap on the self-proposal branch) as
tasks 3-4. `fresh_receipt_derived_and_admitted` and
`receipt_J_guard_or_already_ordered` never took a run/time/history argument
at all -- they are single-store-update algebra, not history statements -- so
both are history-free and reused unchanged via `open... GuardProofsTime`.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardProofs
open Execution Execution.NamedReceiptCalls Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistory
open DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardProofsTime
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem genesis_preceq (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => simp [NamedBlock.Preceq, NamedBlock.preceq]
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
    exact Or.inr ih

omit [Fintype V] in
private theorem ancestor_body_mem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · exact ih (hpc.2 _ hB) hparent

private theorem quorum_honest_member (S : Setup V) (rho : NamedRun V)
    (Q : Finset V) (hQ : S.E.electorate.IsQuorum Q)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    ∃ signer ∈ Q, signer ∈ rho.honest := by
  by_contra hn
  have hsub : Q ⊆ Finset.univ \ rho.honest := by
    intro signer hs
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh => hn ⟨signer, hs, hh⟩⟩
  have hm := S.E.electorate.weightOf_mono hsub
  have hq : S.E.q ≤ S.E.electorate.weightOf Q := hQ
  omega

theorem held_justification_checkpoint_on_history
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V)
    (hhistory : LayerAHistoryIdx S rho n C)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (hi : i ≤ n)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (D : NamedBlock V)
    (hD : D ∈ (NamedRun.stateBefore S rho i v).st.bodies) :
    ∃ J : NamedBlock V,
      NamedRun.blockInRun S rho J ∧
      J ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      NamedBlock.Preceq J D ∧
      J.erase = (derive_named S.E S.cfg D).J ∧
      NamedBlock.Preceq J C ∧
      ((derive_named S.E S.cfg D).h_j = 0 → J = .genesis) ∧
      ((derive_named S.E S.cfg D).h_j ≠ 0 →
        (derive_named S.E S.cfg J).h = (derive_named S.E S.cfg D).h_j ∧
        (derive_named S.E S.cfg J).T_h = J.erase) := by
  have hDscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hD)
  have hpc := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1.2.2.1
  by_cases hz : (derive_named S.E S.cfg D).h_j = 0
  · have hgen := NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg D hz
    refine ⟨.genesis,
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope (genesis_preceq D),
      hpc.1, genesis_preceq D, hgen.symm, genesis_preceq C,
      fun _ => rfl, ?_⟩
    intro hn
    exact False.elim (hn hz)
  · obtain ⟨J, hJD, hJE, Q, hQ, hrows⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg D hz
    obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrier, hrow, hsigner, hp⟩ := hrows signer hsignerQ
    have ha : a.val_index ∈ rho.honest := by simpa only [hsigner] using hsignerHon
    obtain ⟨j, hj, received, hacc, hsend, hem⟩ :=
      NamedOutageProvenance.honest_held_ancestor_row_emission S rho
        core.toNamedUnforgeable i v hD hcarrier hrow ha
    obtain ⟨k, hk, hemit⟩ := hem
    have hjn : j < n := lt_of_lt_of_le hj hi
    have hkj : k ≤ j :=
      row_emission_index_le_block_acceptance S rho core v carrier j received hacc
        a hrow ha k hk hemit hsend
    have hkn : k < n := lt_of_le_of_lt hkj hjn
    obtain ⟨source, entry, hsourceScope, hsourceHeld, hentryScope, hentryHeld,
      hval, htime, hcreate, hselector, hfields, hheight, htarget, herase,
      hancestor, hsameHeight, hroot, hentryC⟩ :=
      hhistory.2.2.1 k a.val_index (S.a a.round) a ha hk hemit hkn
        (derive_named S.E S.cfg D).h_j J.root false hp
    have heq : entry = J := core.root_injective C D hhistory.1 hDscope
      entry J (Or.inl hentryC) (Or.inr hJD) hroot
    subst entry
    have hco := (Proofs.NamedOutageInputs.action_read_invariant S rho k a.val_index a.round).1.1
    have hsourceState := hco.2.2.2.2 source hsourceHeld
    rw [hsourceState] at hheight herase
    have hJheight : (derive_named S.E S.cfg J).h = (derive_named S.E S.cfg D).h_j :=
      hsameHeight.trans hheight.symm
    have hJentry : (derive_named S.E S.cfg J).T_h = J.erase :=
      (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hancestor hsameHeight).trans herase.symm
    refine ⟨J, Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope hJD,
      ancestor_body_mem hpc hD hJD, hJD, hJE, hentryC, ?_, ?_⟩
    · intro hzero
      exact False.elim (hz hzero)
    · intro _
      exact ⟨hJheight, hJentry⟩

#print axioms fresh_receipt_derived_and_admitted
end DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardProofs

end
