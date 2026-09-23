module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusStatements
public import DecoupledConsensusWitnesses.StrongRecovery
public import DecoupledConsensusWitnesses.WeakGenesis
public import DecoupledConsensusWitnesses.FinalityLiveness
public import DecoupledConsensusWitnesses.Outage

/-!
# Witness index

The concrete witness modules retain the original fixtures and activate the
premises used by the generic result bundle. The public proof is
`Proofs.concreteConsensus`; the internal proof is `Proofs.reviewedInternal`.

| Standard group or result | Selected witness |
|---|---|
| Unconditional nested outputs | `WeakGenesis.nested_outputs_activated` |
| Unconditional vote safety | `WeakGenesis.vote_safety_of_clients_activated` |
| Accountable leak fairness | `Outage.leak_fairness_activated` |
| Available confirmation and stable records | `WeakGenesis` and `StrongRecovery` fixtures |
| Finalized inclusion | `FinalityLiveness.honest_proposal_finalization_activated` |
| Outage persistence | `Outage.asynchrony_resilience_activated` |
| `VoteSafetyAfterRecovery` | `StrongRecovery.vote_safety_after_recovery_activated` |
| `HeightProgress` | proof-side theorem; no separate fixture is required |
-/

/-!
## Public guards are active

- `FinalityLiveness.finality_inclusion_guard_active`
- `FinalityLiveness.finality_growth_guard_active`
- `genesis_growth_guard_active`
- `genesis_inclusion_guard_active`
-/
