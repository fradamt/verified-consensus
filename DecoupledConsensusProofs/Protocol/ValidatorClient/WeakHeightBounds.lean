module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Height bounds for actual rows under core execution

A row emitted by an action cannot exceed its pre-action height frontier.
These bounds use the executed action, not an all-awake premise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakFG

open Internal Execution Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

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






theorem honestEmittedHeight_le_localHMaxBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {a : NamedAttestation V}
    {t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) t)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.storeBeforeTime S v t).h_max := by
  have sch : ScheduleWellFormed S rho := adm.toNamedScheduleWellFormed
  have htime := (Proofs.Optimistic.emits_attest_shape S hemit).2
  rw [htime] at hemit
  have heq : a = actionAttestationAt S rho v a.round :=
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
  simpa only [htime] using hbound

theorem honestEmittedHeight_le_localHMax
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {a : NamedAttestation V}
    {t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) t)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.storeAt S v t).h_max := by
  have sch : ScheduleWellFormed S rho := adm.toNamedScheduleWellFormed
  exact (honestEmittedHeight_le_localHMaxBeforeTime S adm hemit hh).trans
    (storeBeforeTime_hMax_le_storeAt S sch v t)


theorem honestEmittedHeight_le_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {a : NamedAttestation V}
    {u t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) u)
    (hh : a.height_pair.erase.height? = some h) (hut : u ≤ t) :
    h ≤ honestHMaxAt S rho t := by
  have sch : ScheduleWellFormed S rho := adm.toNamedScheduleWellFormed
  exact (honestEmittedHeight_le_localHMax S adm hemit hh).trans
    ((stateAt_h_max_mono S sch v hut).trans
      (localHMax_le_honestHMaxAt S rho t hv))

end WeakFG
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
