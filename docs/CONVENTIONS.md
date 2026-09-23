# Source conventions

This page defines source conventions for the Lean model and proof libraries.
For the library layout and import direction, read
[`docs/ARCHITECTURE.md`](ARCHITECTURE.md).

## Naming

- Use the paper name for a protocol function when Lean permits it.
- Use `snake_case` for paper functions and data fields: `on_tick`,
  `update_finality`, `proposal_time`.
- Use `CamelCase` for types and proposition structures: `Block`, `ChainState`,
  `LiveFrom`.
- Use `Named*` only when a named type exists beside an erased twin. For example,
  `NamedBlock` retains signed payloads beside `Block`.
- Keep protocol declarations in `DecoupledConsensusModel.Protocol`.
- Use a qualified name when it makes the source library clear. Do not create a
  second public alias only to shorten a proof.

## Docstrings and paper anchors

Every declaration that models a protocol fact has a short docstring. The
docstring states the purpose and gives the active protocol anchor, for example:

```lean
/-- The block handler checks the parent and carried rows
(PROTOCOL.md#on_block). -/
def on_block := ...
```

Use an anchor in `PROTOCOL.md` for protocol behavior. Use the paper label only
when the declaration describes a result that has no protocol section anchor.
Keep the anchor close to the declaration. Do not cite a private working file.

Module docstrings state what the module defines, what it reads, and what an
auditor should read next. Keep this information at the start of the file.

## No plan vocabulary in source

Source comments are part of the published review surface. Do not put rule
numbers, internal task labels, workstream names, audit dates, or build status
in Lean comments. State the current behavior directly. Keep historical detail
in Git or in the private collaboration log.

Do not describe a declaration as ported, landed, pre-port, or a plan step.
Describe the definition that exists at the current `HEAD`.

## Where a lemma goes

- Put a protocol definition in `DecoupledConsensusModel`.
- Put a generic proposition or regime in `DecoupledConsensusStatements`.
- Put proof-only vocabulary in `DecoupledConsensusInternal`.
- Put a lemma beside the definition or invariant that it proves, under
  `DecoupledConsensusProofs/Protocol`, `Proofs/Execution`, or `Proofs/Generic`.
- Put a bridge theorem in `DecoupledConsensusProofs/Bridge` when it converts
  between generic and concrete vocabulary.
- Put a concrete satisfying run in `DecoupledConsensusWitnesses`.

Do not add a theorem to Model or Statements. A proof term is allowed there only
when a definition needs it for type checking, such as a decidability or
termination obligation.

## Module headers

Every project Lean file starts with a `module` command. It then lists its
`public import` declarations. A declaration module opens an
`@[expose] public section`; an import-only facade has only the module header and
imports. The namespace must match the library and subject area.

Proof bodies are private by construction under this module system. A proof-file
edit therefore rebuilds one module. Batch edits to Model or Statements before
building their importer cone.

Scripts are plain importers. They do not define project modules and do not add
source declarations to the review surface.
