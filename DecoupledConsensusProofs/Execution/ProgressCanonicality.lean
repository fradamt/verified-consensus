module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalCanonicality
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Frontier quorum and height bounds

The named maximum carrier replaces the retired dependency-reachable store
conversion. A named height-crossing certificate supplies the honest row, and
its carried-row provenance places the emission before the strict read. -/

theorem frontierQuorumWitness_stateBeforeTime_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {t : Time} {v : V}
    (hlarge : 1 < (rho.storeBeforeTime S v t).h_max) :
    ∃ W : NamedBlock V,
      W ∈ (rho.storeBeforeTime S v t).bodies ∧
      ∃ Q : Finset V, ∃ X : NamedBlock V, ∃ a : NamedAttestation V, ∃ ta,
        (rho.storeBeforeTime S v t).core.h_max ≤
            (Protocol.derive_named S.E S.cfg W).h ∧
          S.E.electorate.IsQuorum Q ∧ NamedBlock.Preceq X W ∧
          a.erase ∈ chain_attestations W.erase ∧
          a.val_index ∈ rho.honest ∧
          NamedRun.emits S rho a.val_index (.attest a) ta ∧ ta < t ∧
          a.height_pair.erase.height? =
            some ((rho.storeBeforeTime S v t).core.h_max - 1) := by
  let pre := (rho.stateBeforeTime S t v).st
  have hlarge' : 1 < pre.core.h_max := by
    simpa only [pre, Run.storeBeforeTime] using hlarge
  obtain ⟨W, hW, hmaxW⟩ :=
    Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime S rho t v
  have hcross : pre.core.h_max - 1 <
      (Protocol.derive_named S.E S.cfg W).h := by
    rw [hmaxW]
    exact Nat.sub_lt (Nat.zero_lt_of_lt hlarge') (by decide)
  have hpositive : 1 ≤ pre.core.h_max - 1 :=
    Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlarge')
  obtain ⟨X, hX, hXheight, Q, hQ, hwit⟩ :=
    Proofs.NamedFinalityCertificates.height_crossing S.E S.cfg W
      (pre.core.h_max - 1) hpositive hcross
  obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
    HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, a, hcarrier, ha, hsigner, hmatch⟩ := hwit signer hsignerQ
  have haHonest : a.val_index ∈ rho.honest := by
    rw [hsigner]
    exact hsignerHonest
  obtain ⟨n, hread, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted t
  have hWn : W ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
    simpa only [hread] using hW
  obtain ⟨j, hj, received, hacc, hsend, hemit⟩ :=
    Proofs.NamedOutageProvenance.honest_held_ancestor_row_emission S rho
      adm.toNamedUnforgeable n v hWn hcarrier ha haHonest
  obtain ⟨e, he, -, het⟩ := hacc.1.2
  have hreceived : received < t := by
    simpa only [het] using hbefore j e hj he
  have hta : S.a a.round < t := hsend.trans_lt hreceived
  have hheight : a.height_pair.erase.height? = some (pre.core.h_max - 1) := by
    cases hpair : a.height_pair with
    | empty =>
        have : False := by
          simpa only [hpair, NamedHeightPair.matchesEntry, Bool.false_eq_true] using hmatch
        exact this.elim
    | vote height entry timeout =>
        have hfields : height = pre.core.h_max - 1 ∧ entry = X.root := by
          simpa only [hpair, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hmatch
        cases timeout <;>
          simp [hpair, NamedHeightPair.erase, HeightPair.height?, hfields.1]
  refine ⟨W, hW, Q, X, a, S.a a.round, hmaxW.symm.le, hQ, hX, ?_,
    haHonest, hemit, hta, hheight⟩
  exact Proofs.Bridges.erase_mem_chain_attestations W carrier hcarrier a ha

theorem frontierQuorumWitness_stateBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {t : Time} {v : V}
    (hlarge : 1 < (rho.storeBeforeTime S v t).h_max) :
    ∃ W : NamedBlock V,
      W ∈ (rho.storeBeforeTime S v t).bodies ∧
      ∃ Q : Finset V, ∃ X : NamedBlock V, ∃ a : NamedAttestation V, ∃ ta,
        (rho.storeBeforeTime S v t).core.h_max ≤
            (Protocol.derive_named S.E S.cfg W).h ∧
          S.E.electorate.IsQuorum Q ∧ NamedBlock.Preceq X W ∧
          a.erase ∈ chain_attestations W.erase ∧
          a.val_index ∈ rho.honest ∧
          NamedRun.emits S rho a.val_index (.attest a) ta ∧ ta < t ∧
          a.height_pair.erase.height? =
            some ((rho.storeBeforeTime S v t).core.h_max - 1) :=
  frontierQuorumWitness_stateBeforeTime_core S adm.toNamedAdmissibleCore
    hmajority hlarge






#print axioms frontierQuorumWitness_stateBeforeTime_core
#print axioms frontierQuorumWitness_stateBeforeTime

end Protocol
end DecoupledConsensusModel

end
