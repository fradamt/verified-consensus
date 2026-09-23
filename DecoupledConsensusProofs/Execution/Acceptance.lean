module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Pool
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges
public import DecoupledConsensusProofs.Execution.BridgesTail
public import DecoupledConsensusProofs.Execution.ReceiptCalls
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# First-acceptance provenance along a run

The accepted-once relay contract starts from `Run.acceptsAt`, while most
protocol arguments first know only that an object is present in a store at a
run prefix. This file proves the bridge between those two views.

Genesis is the only exception. It is in every initial block tree and therefore
is processed at prefix zero without a handler event. Goldfish votes and
attestations start in empty pools, so their provenance statements have no
exception.

The one-event step (a false-to-true `processed` change at one run index has an
actual accepting handler call) is already proved for the named runtime by
`Proofs.NamedReceiptCalls.new_marker_accepts`; this file only supplies the
induction over run prefixes that repeats that step, plus the genesis base
case and the three per-object-kind specializations that callers use.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Prefix provenance -/


/-- Every processed object at a run prefix has an earlier accepting event,
except for the genesis block that is present in the initial store. -/
theorem genesis_or_acceptsAt_of_processed (S : Setup V) (rho : Run V) (v : V) :
    forall (n : Nat) (o : Object V),
      Object.processed (rho.stateBefore S n v).st o = true ->
        o = Object.block NamedBlock.genesis ∨
          exists i : Nat, i < n ∧ exists t : Time, Run.acceptsAt S rho i v o t := by
  intro n
  induction n with
  | zero =>
      intro o hprocessed
      cases o with
      | block B =>
          simp only [Object.processed, NamedReceipt.processed, Run.stateBefore,
            Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial, decide_eq_true_eq] at hprocessed
          exact Or.inl (congrArg Object.block (Finset.mem_singleton.mp hprocessed))
      | gfVote u =>
          simp [Object.processed, NamedReceipt.processed, Run.stateBefore,
            Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial, Protocol.Store.init, Protocol.Store.pool] at hprocessed
      | attest a =>
          simp [Object.processed, NamedReceipt.processed, Run.stateBefore,
            Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
            Protocol.NamedStore.initial] at hprocessed
  | succ n ih =>
      intro o hpost
      by_cases hpre : Object.processed (rho.stateBefore S n v).st o = true
      · rcases ih o hpre with hgen | ⟨i, hi, t, haccepts⟩
        · exact Or.inl hgen
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, t, haccepts⟩
      · have hpreFalse : Object.processed (rho.stateBefore S n v).st o = false :=
          Bool.eq_false_of_not_eq_true hpre
        obtain ⟨t, hacc⟩ := Proofs.NamedReceiptCalls.new_marker_accepts S rho n v o hpreFalse hpost
        exact Or.inr ⟨n, Nat.lt_succ_self n, t, hacc⟩

/-- Block specialization. Genesis is the only block without an accepting
event. -/
theorem acceptsAt_block_of_processed (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) (B : NamedBlock V)
    (hprocessed : Object.processed (rho.stateBefore S n v).st (.block B) = true) :
    B = NamedBlock.genesis ∨
      exists i : Nat, i < n ∧ exists t : Time,
        Run.acceptsAt S rho i v (.block B) t := by
  rcases genesis_or_acceptsAt_of_processed S rho v n (.block B) hprocessed with
    hgen | haccepts
  · exact Or.inl (NamedObject.block.inj hgen)
  · exact Or.inr haccepts

/-- The erased-tree form of block provenance, with a named body retained for
the accepting event. -/
theorem acceptsAt_block_of_processed_erased (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) {B : Block V}
    (hprocessed : B ∈ (rho.stateBefore S n v).st.core.T) :
    B = Block.genesis ∨
      exists D : NamedBlock V, D.erase = B ∧
        exists i : Nat, i < n ∧ exists t : Time,
          NamedRun.acceptsAt S rho i v (.block D) t := by
  obtain ⟨D, hD, hDB⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore
    S rho n v hprocessed
  have hprocessedD : Object.processed (rho.stateBefore S n v).st (.block D) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    exact hD
  rcases acceptsAt_block_of_processed S rho v n D hprocessedD with hgen | hacc
  · left
    rw [← hDB, hgen]
    rfl
  · right
    exact ⟨D, hDB, hacc⟩

/-- Goldfish-vote specialization. The initial pool is empty, so there is no
genesis exception. -/
theorem acceptsAt_gfVote_of_processed (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) (u : GoldfishVote V)
    (hprocessed : Object.processed (rho.stateBefore S n v).st (.gfVote u) = true) :
    exists i : Nat, i < n ∧ exists t : Time,
      Run.acceptsAt S rho i v (.gfVote u) t := by
  rcases genesis_or_acceptsAt_of_processed S rho v n (.gfVote u) hprocessed with
    hgen | haccepts
  · cases hgen
  · exact haccepts

/-- Attestation specialization. The initial SG pool is empty, so there is no
genesis exception. -/
theorem acceptsAt_attest_of_processed (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) (a : NamedAttestation V)
    (hprocessed : Object.processed (rho.stateBefore S n v).st (.attest a) = true) :
    exists i : Nat, i < n ∧ exists t : Time,
      Run.acceptsAt S rho i v (.attest a) t := by
  rcases genesis_or_acceptsAt_of_processed S rho v n (.attest a) hprocessed with
    hgen | haccepts
  · cases hgen
  · exact haccepts

#print axioms acceptsAt_block_of_processed_erased

end Protocol
end DecoupledConsensusModel

end
