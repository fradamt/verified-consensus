module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PrefixThroughHistory
public import DecoupledConsensusProofs.Protocol.Handlers.HandlerAdmissionGuards
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistoryTime
open Execution Protocol
open Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
theorem genesis_preceq (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => simp [NamedBlock.Preceq, NamedBlock.preceq]
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
    exact Or.inr ih

omit [Fintype V] in
theorem ancestor_body_mem {st : Protocol.NamedStore V}
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


theorem quorum_honest_member (S : Setup V) (rho : NamedRun V)
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


omit [Fintype V] in
theorem named_extend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

omit [Fintype V] in
theorem named_common_chain {A B C : NamedBlock V}
    (hA : NamedBlock.Preceq A C) (hB : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A := by
  induction C with
  | genesis =>
    have heq : A = .genesis := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hA
    subst A
    exact Or.inl (genesis_preceq B)
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hA
    rcases hA with rfl | hAP
    · exact Or.inr hB
    · simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hB
      rcases hB with rfl | hBP
      · exact Or.inl (named_extend s root votes support rows proposer hAP)
      · exact ih hAP hBP




end DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistoryTime

end
