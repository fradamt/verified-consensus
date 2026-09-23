module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.RelayGuards

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedCheckpointRows
open Execution Internal.NamedJointOutage
variable {V : Type} [DecidableEq V] [Fintype V]

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


private theorem held_carried_guard (S : Setup V) (rho : NamedRun V)
    (i : Nat) (reader : V) {A : NamedBlock V}
    (hA : A ∈ (NamedRun.stateBefore S rho i reader).st.bodies) :
    Protocol.carried_attestations_admissible S.hc A.erase = true := by
  rcases NamedOutageProvenance.held_block_origin S rho i reader hA with
    hgen | ⟨j, _hj, ta, hacc⟩
  · subst A
    rfl
  · exact (NamedRelayGuards.accepted_block_static_guards S rho hacc).2.2

private theorem row_round_of_guard (S : Setup V) {A : NamedBlock V}
    (hguard : Protocol.carried_attestations_admissible S.hc A.erase = true)
    {a : NamedAttestation V} (ha : a ∈ A.attestations) :
    a.round ≤ S.hc.round_of A.slot := by
  have herow : a.erase ∈ A.erase.attestations := by
    rw [Proofs.NamedWire.erase_attestations]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have h := List.all_eq_true.mp hguard a.erase herow
  simpa only [decide_eq_true_eq, NamedAttestation.erase, Proofs.NamedWire.erase_slot] using h

/-- Every actual earlier nonempty honest height row has a full signed source
and entry. This history field requires no additional execution assumption. -/
theorem signed_source_history (S : Setup V) (rho : NamedRun V) (r : Round) :
    SignedSourceHistory S rho r := by
  intro a _hHon _hprior hem h root timeout hVote
  exact Proofs.NamedIntrinsicEntry.emitted_height_signed_source S rho hem hVote

/-- At the strict checkpoint, all rows in every ancestral carrier pass the
carried-round guard; honest rows came from actual strictly earlier actions. -/
theorem prior_carrier_rows_at_checkpoint
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (reader : V) (r : Round) {B : NamedBlock V}
    (hB : B ∈ (checkpoint S rho reader r).st.bodies) :
    PriorCarrierRows S rho r B := by
  have hstrict : B ∈ (NamedRun.stateBeforeTime S rho (S.a r) reader).st.bodies := hB
  obtain ⟨i, hread, _hbefore⟩ :=
    Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted (S.a r)
  have hBi : B ∈ (NamedRun.stateBefore S rho i reader).st.bodies := by
    rw [hread] at hstrict
    exact hstrict
  have hpc := (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1.2.2.1
  intro A hAB
  have hA := ancestor_body_mem hpc hBi hAB
  have hguard := held_carried_guard S rho i reader hA
  refine ⟨hguard, ?_⟩
  intro a ha
  refine ⟨row_round_of_guard S hguard ha, ?_⟩
  intro hHon
  exact NamedOutageProvenance.honest_held_ancestor_row_before_action
    S rho sch auth reader r hstrict hAB ha hHon

end DecoupledConsensusModel.Proofs.NamedCheckpointRows

end
