# Decoupled Consensus

Lean formalizations for decoupled-consensus protocol work.

Current contents:

- `DecoupledConsensus/State`: Section 2 state-machine model, statements, and
  accountable-safety proofs.
- `DecoupledConsensus/Store`: Section 3 store model, statements, and proofs.
- `DecoupledConsensus/AccountableSafety.lean`: compatibility facade for the
  Section 2 accountable-safety results.
- `DecoupledConsensus/AccountableSafety.md`: architectural notes for the
  formalization.

Build the current formalization with:

```sh
lake build DecoupledConsensus
```
