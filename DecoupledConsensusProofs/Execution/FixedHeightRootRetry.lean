module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore

/-!
# Fixed-height root-target retry facade

The recovery-free fixed-height target, admission, rebase, and no-repeat API now
lives in `FixedHeightRootCoreRun`. This facade preserves the historical import
path without adding recovery or post-healing dependencies to the low provider.
-/
