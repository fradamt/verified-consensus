module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.StableRootSuffixOrigin

@[expose] public section

/-!
# T_out, step 2: split the total frame stable root

The frame contract returns the active prefix of a frozen G2 root when that
projection is present. If the projection is empty, it returns the local FG
root. The latter is intentionally left unsplit here: it may be the `J` or
the `F` arm of the fork-choice root.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

theorem stableOutput_frameStableRoot_split
    (S : Setup V) (rho : Run V) (v : V) (i : Nat) {G : Block V}
    (hroot : StableRecord.StableRootAt S rho v i G) :
    ∃ time : Time,
      rho.events[i]? = some (.tick v time) ∧
        0 < S.E.slotOf time ∧
        time = Protocol.support_cutoff S.E (S.E.slotOf time) ∧
        ((∃ raw : Block V,
            (DecoupledConsensusModel.Protocol.readFrame
              (NamedActionReads.confirmationReadFrom S
                (rho.stateBefore S i v) time).cache
              (NamedActionReads.confirmationReadFrom S
                (rho.stateBefore S i v) time).st.core.toHealing
              (S.hc.round_of
                (NamedActionReads.confirmationReadFrom S
                  (rho.stateBefore S i v) time).st.core.s)).g2 = some (some raw) ∧
            DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree
                (NamedActionReads.confirmationReadFrom S
                  (rho.stateBefore S i v) time).st.core.toHealing.toFG) raw = some G) ∨
          G = Protocol.get_fg_root
            (NamedActionReads.confirmationReadFrom S
              (rho.stateBefore S i v) time).st.core.toHealing.toFG) := by
  rcases hroot with ⟨time, hi, hpos, hcut, hframe⟩
  refine ⟨time, hi, hpos, hcut, ?_⟩
  let n := NamedActionReads.confirmationReadFrom S
    (rho.stateBefore S i v) time
  let frame := DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
    (S.hc.round_of n.st.core.s)
  have hframe' : DecoupledConsensusModel.Protocol.frameStableRoot n.cache S.E S.hc
      n.st.core.toHealing (S.hc.round_of n.st.core.s) = some G := by
    simpa only [n] using hframe
  unfold DecoupledConsensusModel.Protocol.frameStableRoot at hframe'
  change (match (frame.g2.bind id).bind
      (DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) with
    | some Q => some Q
    | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG)) = some G at hframe'
  cases hslot : frame.g2 with
  | none =>
      simp only [hslot, Option.bind_none] at hframe'
      exact Or.inr (Option.some.inj hframe').symm
  | some opt =>
      cases opt with
      | none =>
          simp only [hslot, Option.bind_some] at hframe'
          exact Or.inr (Option.some.inj hframe').symm
      | some raw =>
          rw [hslot] at hframe'
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw with
          | none =>
              simp [Option.bind, hactive] at hframe'
              exact Or.inr hframe'.symm
          | some A =>
              simp [Option.bind, hactive] at hframe'
              have hAG : A = G := hframe'
              subst G
              exact Or.inl ⟨raw, rfl, hactive⟩

#print axioms stableOutput_frameStableRoot_split

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
