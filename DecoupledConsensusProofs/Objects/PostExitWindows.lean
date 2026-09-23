module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Canonicality
public import DecoupledConsensusProofs.Generic.EvaluationStore

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The round invariant -/


/-! ## `roots`, gate-off free
`get_fg_root_compatible_of_history`'s `finalized` field comes from
`fgRoot_eq_F_of_frame`/`GateOffFrameAt` (the frozen-`M` cap `h_F + 2 ≤ M`).
It does not need the cap at all: `st.F ⪯ st.J` is a plain reachable-store
invariant (`finalizedPrecedesJustifiedInvariant`), so once `st.J` is
compatible with `B`, `st.F` is too — either `J ⪯ B`, and `F ⪯ J ⪯ B`; or
`B ⪯ J`, and `F`, `B` are both ancestors of `J`, hence comparable. -/














/-! ## `roots`, split at the FG gate

The post-exit proof cannot constrain every stored justification. A target
below the exit frontier can remain off the protected chain while the gate is
off. The gate split keeps that harmless stockpiled target out of the
finalized-root branch and uses target history only when the gate selects `J`.
-/













/-! ## Height-restricted filtered-tree membership

`coneAndThin_succ'`'s frame is not restated wholesale: inside its call chain
(`seedRelayVoteFacts`) the frame is consumed only for root comparability (now
`roots_gateSplit`) and for `frontierAncestor_filtered_of_gateOff` (band-witness
membership in the finality-filtered tree). The proof below replaces exactly
that one lemma; the rest of `coneAndThin_succ'`'s chain is reused unchanged.

`frontierBlock_filtered_of_gateOff` already needs no unrestricted history for
the `F ⪯ X` half — its `hXh`/`hgateOff` are raw inputs, and its crossing step
is either the pure gate-off arithmetic (`h_F ≤ h_j ≤ st.h_j < M - 1`, no
history) or, as used here, `finalizedRoot_preceq_of_band` directly. The only
history-dependent piece is `hXh` itself, which
`frontierHeight_le_of_canonicalHistoryBetween` now supplies. -/

/-- **`F ⪯ get_fg_root`, unconditionally.** No gate-off cap: `get_fg_root` is
`J` exactly when the gate is on, and `F ⪯ J` always
(`finalizedPrecedesJustifiedInvariant`); when the gate is off it is `F`
itself, reflexively below. So `root ⪯ X` alone gives `F ⪯ X` by transitivity
in the lemmas below — no cap on `h_j`/`h_max` is needed at all. -/
theorem finalizedRoot_preceq_fgRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) {w : V} {t : Time} :
    Block.Preceq (rho.storeBeforeTime S w t).F
      (Protocol.get_fg_root (rho.storeBeforeTime S w t).toHealing.toFG) := by
  have hFJ : Block.Preceq (rho.storeBeforeTime S w t).F
      (rho.storeBeforeTime S w t).J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t w
  simp only [Protocol.get_fg_root, Protocol.Store.toHealing]
  split
  · exact hFJ
  · exact Block.preceq_self _



/-! ## The cone/band persistence step

`coneAndThin_succ'`'s own chain (`seedRelayVoteFacts`, `goldfishCone_step`,
`headThin_of_band`) is not restated wholesale. Only `seedRelayVoteFacts`'s one
call to `frontierAncestor_filtered_of_gateOff` needs a replacement; the rest —
`goldfishCone_step`'s Goldfish-fork-choice argument,
`ancestorCandidate_of_processedDescendant_and_hMax`,
`votePath_of_candidate` — carries no frame dependence and is reused unchanged.

`seedRelayVoteFacts`'s `hthin: ThinHonestHeadAt S rho M s C` parameter served
two purposes: producing the honest head `H` used for the processed-membership
argument (`honestHead_voterProcessed_at_nextDuty_of_postHealingCone`, purely
timing, no `M`), and its height bound `M - 1 ≤ H.height`, used twice (inside
`frontierAncestor_filtered_of_gateOff` and again for
`ancestorCandidate_of_processedDescendant_and_hMax`'s `hmax`). The height
-restricted version below drops `hthin` entirely: `H` comes straight out of
`hvotes` at any honest committee member of slot `s` (`hcom` picks one, as
`seedBoundaryAdoption_of_discharge` already does elsewhere), and both height
uses come from `frontierHeight_le_of_canonicalHistoryBetween` applied to `H`
via `history.mono` (`history` is stated for `C`; `Block.Preceq C H` transports
it to `H`, since `CanonicalHistoryBetween` covers every honest source below
its own endpoint). -/









/-! ## `roots`, gate off: fresh or previous, and the fault bound confined to previous
Combines `finalized_compatible_of_honestFinalityHistoryFrom` (fresh
certificate, no fault bound) with
`fgRoot_compatible_gateOff_of_canonicalHistoryBetween` (previous certificate,
needs `BelowOneThird`) by casing on the finalized checkpoint's own
certificate height against the exit threshold `H0`. `BelowOneThird` remains
a hypothesis of this theorem — the previous-certificate branch still needs it —
but a caller who can independently show every relevant checkpoint is fresh
(e.g. every round far enough past the exit, once finalization height has
caught up) never actually exercises that branch. -/

/-! ## `roots`, the full producer

`roots_gateSplit`'s justified branch, with the gate-off branch replaced by
`fgRoot_compatible_gateOff_freshOrOld`. This is the producer to use going
forward: `BelowOneThird` is still a hypothesis (the justified branch never
needed it; the gate-off branch's old-certificate case still does), but a
caller who can show the round's finalized checkpoint is fresh exercises
only the bound-free paths throughout. -/

/-! ## Finality-filter noninterference from a comparable-root ancestor

`healAnchor_compatible_carrier_or_freshFresh`'s `LiveG1SettledAt` premise
(via `liveG1SettledAt_of_previousActionCarriersQuiet`/
`previousActionCarriersQuietAt_of_gateOff`) needs every honest round-`(r-1)`
action carrier noninterfering at every honest round-`r` read
(`PreviousActionCarriersQuietAt`, `SeedActivityRun.lean`), which that
producer gets from a frozen frontier and `SlashableBound`
(`frontierRoot_preceq_of_gateOff`, `frontierBlock_filtered_of_gateOff`).

The carrier is already an ancestor of `PostExitRoundAt`'s own canonical
block `B` (its `carriers` field), and `B` is already known processed and
band-reaching at every honest round-`r` read (the same facts `roots`
already establishes there). So the carrier's own viability witness is `B`
itself — no separate witness needs to be built or relayed from round
`r - 1`, and the whole argument is the same
`Block.compatible_of_preceq_common` plus `frontierAncestor_filtered_of_canonicalHistoryBetween`
combination the roots and cone work above already uses. No fault bound. -/



/-! ## `LiveG1SettledAt`, fault-bound free

`G1_honest_named_supporter`/`G1_preceq_honestPreviousActionCarrier` (used by
`liveG1SettledAt_of_previousActionCarriersQuiet`) extract an honest member
of a grade-1 block's `direct_support` quorum via `exists_honest_direct_supporter`,
which takes `BelowOneThird` directly. That premise is more than the
extraction needs: `exists_honest_direct_supporter_of_faulty_lt_m` (its own
unconditional core) only needs the quorum's faulty weight below `E.m`, the
plain majority threshold `⌊W/2⌋ + 1` — exactly what `HonestWeightMajority`
gives by a one-line weight count, not the accountable-safety bound. -/






/-! ## Previous-round action carrier, raw visibility, fault-bound free

`seedActionRead_genesisResolved` (`SeedCanonicalAnchorRun.lean`) needs the
raw finalized root `F` at an honest round-`c` read comparable with the
previous round's honest action carrier `H`, to place `H` in the finalized
history that ultimately admits it before the read. Its only bound-dependent
step is exactly that comparability, via `finalizedRoot_preceq_of_band`
(`SlashableBound`). But `H` is already below `PostExitRoundAt`'s own
canonical block `B` (`carriers`), and the read's own root is already known
compatible with `B` (`roots`) — the same "`B` is its own witness" argument
as `finalityFilterNoninterference_of_history`, here ending at `F` directly
via the unconditional `finalizedRoot_preceq_fgRoot` instead of a band
witness. No fault bound. -/




/-! ## Genesis holds grade 1 at an action read, fault-bound free

`g1_exists_at_action` (`SeedCanonicalAnchorRun.lean`) uses `BelowOneThird`
in exactly two places: converting it to `HonestWeightMajority`
(`honestWeight_ge_m`'s only need), and calling `seedActionRead_genesisResolved`
for each honest supporter `v`. Both are already handled: the conversion is
now just the hypothesis itself, and the call becomes
`seedActionRead_genesisResolved_of_history`, needing per-supporter
`Preceq (actionSGBlockAt v (c-1)) B` (the invariant's own `carriers` field)
and one root-compatibility fact at the fixed reader `w`
(the invariant's own `roots` field). -/

/-! ## `get_sg_root` case split at an action read, fault-bound free -/

/-! ## Genesis holds grade 1 at a vote duty, fault-bound free -/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
