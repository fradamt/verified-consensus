module
public import DecoupledConsensusModel.Generic.Run
public import DecoupledConsensusModel.Objects.Weights

@[expose] public section

/-!
# `DecoupledConsensusModel/Generic/Env.lean`

Purpose: generic execution model — network and timing environment.
Paper: generic execution model (not a paper algorithm).

Defines: Env and its timing, electorate, and awake fields.

Read after: `DecoupledConsensusModel.Generic.Run`, `DecoupledConsensusModel.Objects.Weights`
Read next: `DecoupledConsensusStatements.Generic.Conditions`.

State read: generic events, protocol specifications, worlds, and runs.
State written: generic world/run values and observations.

Representation notes: The generic layer is independent of the Section 7 protocol and uses typed events and folds over worlds.
-/

-- ── from Generic/Env.lean ──
namespace DecoupledConsensusModel.Generic

structure Env (V : Type) [DecidableEq V] [Fintype V] where
  Δ : Time
  Δ_pos : 0 < Δ
  t_GST : Time
  t_GST_nonneg : 0 ≤ t_GST
  /-- The fixed validator weights used by participation premises. -/
  electorate : Electorate V
  /-- Who is awake when. Participation premises are stated on this profile. -/
  awake : V → Time → Bool

end DecoupledConsensusModel.Generic

end
