module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Exact event-prefix height crossing carriers

A least honest `h_max` crossing names the honest store and processed block that
attain the new maximum. An exact-height ancestor is then selected on that same
chain. No caller-selected block or recovery/nonfinality premise is used.

: the carrier is a `NamedBlock` `D` read from
`Proofs.NamedStoreBridge.maximum_carrier_stateBefore`, whose height fact is stated
over `derive_named`, not the retired `derived_state`; `RunBlock` at a named
body comes from `Proofs.Bridges.runBlock_of_stateBefore_mem`, needing only bodies
membership, so no `DepReachableStore`/`Admissible` premise survives the proof
except as a kept, now-unused, argument at call sites that still supply one
(C1). `PrefixHeightCrossingWitness` and the chain-interpolation lemma feeding
it are restated the same way: both `carrier` and `anchor` are named bodies,
selected and chained entirely through `derive_named`/`NamedBlock.Preceq`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]


/-- One named transition raises height by at most one. Reproved here (
 pattern, same as `HMaxCoreRun`'s own `named_transition_h_le_succ`): that
copy is `private` to its file, so a single-file compile of this module cannot
reach it, and `HMaxCoreRun` is not to be edited to export a public twin. -/
private theorem named_transition_h_le_succ
    (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V)
    (sigma : Protocol.ChainState V) :
    (Protocol.named_transition E cfg sigma B).h ≤ sigma.h + 1 := by
  have hfold : (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) sigma
      B.erase B.attestations).h = sigma.h := by
    unfold Protocol.fold_rows
    exact (NamedDerivationGeometry.fold_context_fields
      (Protocol.TimeoutBinding.targeted V) B.attestations
      { sigma with s := B.erase.slot }).2.1
  unfold Protocol.named_transition Protocol.transition_rows
  rw [Protocol.process_height_events_eq]
  split_ifs
  · rw [Protocol.advance_height_h, Protocol.afterFin_h, hfold]
  · rw [Protocol.advance_height_h, Protocol.afterFin_h, hfold]
  · rw [Protocol.afterFin_h, hfold]
    exact Nat.le_succ _

omit [Fintype V] in
/-- A named body's ancestor is itself a named body of a parent-closed store.
Reproved here (same short private induction already duplicated in
`NamedStoreBridge`, `NamedFinalityGuard`, `NamedCheckpointRows` and
`NamedOutageProvenance`; none of those copies is public). -/
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


/-- A chain whose derived height reaches `H` contains an exact height-`H`
ancestor, for every positive protocol height.

: restated over `NamedBlock`/`derive_named`/`NamedBlock.Preceq`; the erased
`derived_state`/`Block.Preceq` chain this used is retired ( 1636). The
one-step height bound is `named_transition_h_le_succ` above instead of
`derived_state_child_h_le`, and the ancestor step is `Proofs.NamedAncestry.named_extend`
instead of `Block.preceq_trans` composed with `Protocol.preceq_node`. -/
theorem exists_derivedHeight_eq_on_chain
    (E : Env V) (cfg : Protocol.HeightConfig)
    {B : NamedBlock V} {H : Height} (hH : 1 ≤ H)
    (hHB : H ≤ (derive_named E cfg B).h) :
    ∃ P : NamedBlock V, NamedBlock.Preceq P B ∧ (derive_named E cfg P).h = H := by
  induction B with
  | genesis =>
      have hHle : H ≤ 1 := by
        simpa only [Protocol.derive_named] using hHB
      have hEq : H = 1 := Nat.le_antisymm hHle hH
      subst H
      exact ⟨NamedBlock.genesis, Proofs.NamedAncestry.named_self _, rfl⟩
  | node p s root votes support attestations proposer ih =>
      by_cases hparent : H ≤ (derive_named E cfg p).h
      · obtain ⟨P, hPp, hPheight⟩ := ih hparent
        exact ⟨P, Proofs.NamedAncestry.named_extend s root votes support attestations proposer hPp,
          hPheight⟩
      · have hparentLt : (derive_named E cfg p).h < H :=
          Nat.lt_of_not_ge hparent
        have hchildUpper :
            (derive_named E cfg
              (.node p s root votes support attestations proposer)).h ≤ H :=
          (named_transition_h_le_succ E cfg _ (derive_named E cfg p)).trans
            (Nat.succ_le_iff.mpr hparentLt)
        have hchildEq :
            (derive_named E cfg
              (.node p s root votes support attestations proposer)).h = H :=
          Nat.le_antisymm hchildUpper hHB
        exact ⟨.node p s root votes support attestations proposer,
          Proofs.NamedAncestry.named_self _, hchildEq⟩


/-- An exact successor-valued honest prefix maximum is attained by a processed
run block at one honest store.

: the carrier is a `NamedBlock` `D` read from
`Proofs.NamedStoreBridge.maximum_carrier_stateBefore`, whose height fact is already
`derive_named`-valued and needs no admissibility premise; `adm` is kept only
so existing call sites' argument shape still applies (same discipline as
`HMaxCoreRun.treeHeightsLeHMax_storeBeforeTime`). -/
theorem exists_honest_exactHMaxCarrierAtPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (n : Nat) (H : Height)
    (heq : honestHMaxBeforeIndex S rho n = H + 1) :
    ∃ v ∈ rho.honest, ∃ carrier : NamedBlock V,
      carrier ∈ (rho.stateBefore S n v).st.bodies ∧
      RunBlock S rho carrier ∧
      (derive_named S.E S.cfg carrier).h = H + 1 := by
  obtain ⟨v, hv, hlocal⟩ :=
    exists_honest_localHMax_eq_of_honestHMaxBeforeIndex_eq_succ
      S rho n H heq
  obtain ⟨carrier, hcarrier, hcarrierHeight⟩ :=
    Proofs.NamedStoreBridge.maximum_carrier_stateBefore S rho n v
  exact ⟨v, hv, carrier, hcarrier,
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hcarrier, hcarrierHeight.trans hlocal⟩


/-- The causal crossing package selected from one exact honest-prefix maximum.
The protected block is an ancestor chosen on the crossing carrier's own chain.

/C1: both `carrier` and `anchor` are `NamedBlock`, held via bodies
membership and chained by `derive_named`/`NamedBlock.Preceq`. -/
def PrefixHeightCrossingWitness
    (S : Setup V) (rho : Run V) (n : Nat) (blocked : Height) : Prop :=
  ∃ v ∈ rho.honest, ∃ carrier anchor : NamedBlock V,
    carrier ∈ (rho.stateBefore S n v).st.bodies ∧
    anchor ∈ (rho.stateBefore S n v).st.bodies ∧
    RunBlock S rho carrier ∧ RunBlock S rho anchor ∧
    NamedBlock.Preceq anchor carrier ∧
    (derive_named S.E S.cfg anchor).h = blocked ∧
    (derive_named S.E S.cfg carrier).h = blocked + 2


/-- A first frontier value `blocked + 2` supplies the exact protected ancestor
and crossing carrier required by causal recovery.

: the anchor's bodies membership comes from `Proofs.NamedStore.Coherent`'s
`NamedParentClosed` clause at the prefix store (`Proofs.NamedRuntime.stateBefore_invariants`,
the same projection path `NamedOutageProvenance.honest_held_ancestor_row_before_action`
uses), not from the retired `Proofs.Bridges.depReachable_of_admissible`/`parentClosed_depReachable`. -/
theorem prefixHeightCrossingWitness_of_frontier_eq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {n : Nat} {blocked : Height} (hblocked : 1 ≤ blocked)
    (heq : honestHMaxBeforeIndex S rho n = (blocked + 1) + 1) :
    PrefixHeightCrossingWitness S rho n blocked := by
  obtain ⟨v, hv, carrier, hcarrier, hcarrierRun, hcarrierHeight⟩ :=
    exists_honest_exactHMaxCarrierAtPrefix S adm n (blocked + 1) heq
  have hblockedCarrier : blocked ≤
      (derive_named S.E S.cfg carrier).h := by
    rw [hcarrierHeight]
    exact Nat.le_add_right blocked 2
  obtain ⟨anchor, hanchorCarrier, hanchorHeight⟩ :=
    exists_derivedHeight_eq_on_chain S.E S.cfg hblocked hblockedCarrier
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.stateBefore S n v).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1
  have hanchor : anchor ∈ (rho.stateBefore S n v).st.bodies :=
    ancestor_body_mem hcoh.2.2.1 hcarrier hanchorCarrier
  exact ⟨v, hv, carrier, anchor, hcarrier, hanchor,
    hcarrierRun, Proofs.Bridges.runBlock_of_stateBefore_mem S hv hanchor,
    hanchorCarrier, hanchorHeight, by
      simpa only [Nat.add_assoc] using hcarrierHeight⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
