module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore

@[expose] public section

/-! # The named store's emitted-height bound ( companion)

`honestEmittedHeight_le_honestHMaxAt` and `honestEmittedHeight_le_honestHMaxBeforeIndex`
are proved on earlier over the retired `Protocol.round_action` / `DepReachableStore`
route (`Proofs.HealingSurface.roundActionHeight_le_actionHMax` and its callers).
`HMaxCoreRun.lean`'s own channel-1659 Open removes that route entirely: the
named runtime never builds a `DepReachableStore` witness and the row is no
longer a bare `Protocol.round_action` call.

This module recovers both theorems over the named runtime instead, using the
design note exports that already exist premise-free at every named read:
`NamedActionSources.action_run_emission` (Q3b) identifies an actual emission
with the action's own named row `Proofs.HealingSurface.actionAttestationAt`;
`NamedActionSources.action_source` / `action_witness` (Q5/Q6) name the row's
FG source as a retained named body; and `Proofs.NamedStoreBridge.heights_le_hMax_*`
(itself a fold over the named tick, `NamedNumericStore.heights_bounded_*`)
bounds every retained body's `derive_named` height by the read's own `h_max`.
Composed, these replace `roundActionHeight_le_actionHMax` at the one read the
row is actually built on; the rest of the argument (time monotonicity, the
honest maximum) is earlier's own unchanged `HMaxCoreRun` machinery. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A named height pair whose erasure has a height is a proper vote pair at
that same height. -/
private theorem heightPair_vote_of_height {hp : NamedHeightPair} {h : Height}
    (he : hp.erase.height? = some h) :
    ∃ entry timeout, hp = .vote h entry timeout := by
  cases hp with
  | empty => simp [NamedHeightPair.erase, HeightPair.height?] at he
  | vote h' entry timeout =>
    have hEq : h' = h := by
      cases timeout <;>
        simpa [NamedHeightPair.erase, HeightPair.height?] using he
    exact ⟨entry, timeout, by rw [hEq]⟩

/-- An honest row sent by an actual tick is no higher than the emitter's own
strict pre-action frontier. Named twin of earlier's
`Proofs.HealingSurface.honestEmittedHeight_le_localHMaxBeforeTime`, over
`NamedActionSources.action_source` / `action_witness` and
`Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime` in place of the retired
`Protocol.round_action` / `DepReachableStore` route. -/
theorem honestEmittedHeight_le_localHMaxBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {a : NamedAttestation V} {t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) t)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.storeBeforeTime S v t).h_max := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have ht : t = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  subst ht
  have heq : a = Proofs.HealingSurface.actionAttestationAt S rho v a.round :=
    ((NamedActionSources.action_run_emission S rho sch v a.round a).mp hemit).2.2
  obtain ⟨entry, timeout, hvote⟩ := heightPair_vote_of_height hh
  rw [heq] at hvote
  obtain ⟨Cfg, hCfg, hheight, -⟩ :=
    NamedActionSources.action_source S rho v a.round h entry timeout hvote
  obtain ⟨C, hCmem, -, hCderiv, -⟩ :=
    NamedActionSources.action_witness S rho v a.round Cfg hCfg
  rw [hCderiv] at hheight
  have hbound :=
    Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime S rho (S.a a.round) v C hCmem
  rw [hheight] at hbound
  exact hbound

/-- Preserve the inclusive emission-time bound. -/
theorem honestEmittedHeight_le_localHMax
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {a : NamedAttestation V} {t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) t)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.storeAt S v t).h_max :=
  (honestEmittedHeight_le_localHMaxBeforeTime S adm hemit hh).trans
    (storeBeforeTime_hMax_le_storeAt S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v t)

/-- Every honest row sent by a time is below the honest strict-time frontier
there. This also covers rows sent exactly at that time. -/
theorem honestEmittedHeight_le_honestHMaxBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {a : NamedAttestation V}
    {u t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) u)
    (hh : a.height_pair.erase.height? = some h) (hut : u ≤ t) :
    h ≤ honestHMaxBeforeIndex S rho (strictEventIndex rho t) := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hlocal := (honestEmittedHeight_le_localHMaxBeforeTime S adm hemit hh).trans
    (storeBeforeTime_hMax_mono S sch v hut)
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch] at hlocal
  exact hlocal.trans (localHMax_le_honestHMaxBeforeIndex S rho _ hv)

/-- A height-pair attestation emitted by event `i` is below the emitter's
local maximum at every strict event prefix `n` beyond that event. Named twin
of earlier's `attestationHeight_le_stateBeforeIndex`. -/
theorem attestationHeight_le_stateBeforeIndex
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i n : Nat} {v : V} {t : Time} {a : NamedAttestation V} {h : Height}
    (hi : rho.events[i]? = some (.tick v t))
    (hmem : Object.attest a ∈ (NamedNode.tick S v (rho.stateBefore S i v) t).2)
    (hin : i < n)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.stateBefore S n v).st.h_max := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hemit : rho.emits S v (Object.attest a) t := ⟨i, hi, hmem⟩
  have hlocal := honestEmittedHeight_le_localHMaxBeforeTime S adm hemit hh
  have heqst : rho.storeBeforeTime S v t = (rho.stateBefore S i v).st :=
    congrArg NamedNodeState.st
      (Proofs.NamedRuntime.tick_prefix_eq_strict S rho sch.sorted
        (NamedScheduleWellFormed.nodup sch) hi).symm
  rw [heqst] at hlocal
  exact hlocal.trans (stateBefore_hMax_mono S rho v (Nat.le_of_lt hin))

/-- An honest height-pair emission made by event `i` is below the honest
frontier at every strict event prefix `n` beyond that event. -/
theorem honestEmittedHeight_le_honestHMaxBeforeIndex
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i n : Nat} {v : V} (hv : v ∈ rho.honest)
    {t : Time} {a : NamedAttestation V} {h : Height}
    (hi : rho.events[i]? = some (.tick v t))
    (hmem : Object.attest a ∈ (NamedNode.tick S v (rho.stateBefore S i v) t).2)
    (hin : i < n)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ honestHMaxBeforeIndex S rho n :=
  (attestationHeight_le_stateBeforeIndex S adm hi hmem hin hh).trans
    (localHMax_le_honestHMaxBeforeIndex S rho n hv)

/-- An honest height-pair emission made by time `t` is at most the moving
honest frontier at `t`. Named twin of earlier's
`honestEmittedHeight_le_honestHMaxAt`. -/
theorem honestEmittedHeight_le_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {a : NamedAttestation V}
    {u t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) u)
    (hh : a.height_pair.erase.height? = some h) (hut : u ≤ t) :
    h ≤ honestHMaxAt S rho t := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  exact (honestEmittedHeight_le_localHMax S adm hemit hh).trans
    ((stateAt_h_max_mono S sch v hut).trans
      (localHMax_le_honestHMaxAt S rho t hv))

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
