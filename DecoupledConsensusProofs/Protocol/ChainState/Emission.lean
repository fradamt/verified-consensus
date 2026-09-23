module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Anchor
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry

@[expose] public section

/-!
# P4, step D — the emitted target is on the emitter's own confirmed chain
(`Props/Proofs.Optimistic.lean` (C3) clause 6, (C2); §6 H1;
PROTOCOL.md#the-complete-protocol)

Lemma G1 says the §6 duty reads its height pair off the chain state of a block on
its own `live_confirmed` chain (`Proofs.Engine.round_action_gated`). (C3)'s gate
clause asks for one step more: that the **target root** the pair carries names a
block on that chain, not merely that the *gate* is on it.

That step is `Proofs.Records.derived_state_T_h_preceq` — `σ[C].T_h ⪯ C`, the
height-entry block is on the chain that entered the height — plus two store
invariants, because the gate's chain state has to be the *derived* one:

* `ParentClosed` and `DerivedStateAgrees`, both of which
  `Proofs.Bridges.storeInvariants_of_admissible` supplies on an admissible run;
* `live_confirmed ∈ Σ.T`, which is **not** in the P6 pack. Since the
  confirmation rewire the composed evaluation reads
  `get_fg_root(Σ) ∈ {Σ.J, Σ.F}` — as the no-confirmation value and under the
  relative anchor — so the membership needs O10's `Σ.J ∈ Σ.T` beside O5's
  `Σ.F ∈ Σ.T`, and O16 rides the dependency contract now
  (`Alignment.confirmedInTree_depReachable`). Carried as an explicit premise
  here and named in `StoreGateProcessed` below.

This closes check-doc H1's *ancestry* half at the store: the emitted target is an
ancestor of the emitter's confirmation, so with clause (b) it is an ancestor of
`Can`. What H1's remaining half asks — that the emitted *height* is at most
`σ[Can].h`, which is what upgrades "compatible" to "equal" through Lemma A — is
not here; it is `RootOnCan`'s business.

**The run-level lift.** `GateIsOwnConfirmation` is `Main.lean`'s residual, and
`gateIsOwnConfirmation_of` below reduces it to exactly two things: the store
invariants above at the reading position `t⁻`, and `EmissionAtOwnStore` — that
the store `round_action` reads inside the emitting tick is the `t⁻` store in `σ`
and `T`, and reports the `live_confirmed` the store at `t` reports.
`Proofs.AlignedRoundLemmas.on_tick_emit_shape` is the first half of that fact
(the tick's own branch structure); `Optimistic/Alignment.lean` proves the whole
of it (`emissionAtOwnStore_of_admissible`), so neither `Prop` below is a
residual any more.

**The reading positions are not the same, and O19 is why.** An earlier form of
`EmissionAtOwnStore` put all three fields at `ρ.storeAt S v t`. That is
*unprovable*: `Event.key` orders a same-instant delivery **after** the tick
(`Event.phase`), `Run.storeAt` folds it in, and `on_block` writes both `σ`
and `Σ.T`. Only `Σ.live_confirmed` survives the crossing, because no handler but
`update_confirmation` writes it (`TickBridges.process_live_confirmed`). So the
clause is split by writer: `live_confirmed` at `t`, `σ` and `Σ.T` at `t⁻`
(`docs/fragments/review-gate-clause.md`, obligation O19).
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The store-level statement -/

/-- Named twin of `Proofs.Records.derived_state_T_h_preceq`. -/
theorem derive_named_T_h_preceq (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    Block.Preceq (Protocol.derive_named E cfg B).T_h B.erase := by
  simpa only [Proofs.NamedDerivationGeometry.derive_named_latest] using
    (Proofs.NamedDerivationGeometry.chainOrder_derive_named E cfg B).target_preceq_latest



/-! ## 2. The run-level lift -/





end Optimistic
end Proofs
end DecoupledConsensusModel

end
