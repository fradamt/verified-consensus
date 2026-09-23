module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SlashableBound
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Validator-client vote safety

The emission proof restates the existing non-self-slashing argument with its
actual premise: `ScheduleWellFormed.honest_only`. It does not route through
`AdmissibleCore`. The attributed proof adds only carried-attestation
authenticity to connect honest-attributed store rows to actual emissions.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Two emitted target entries at one height agree. The schedule is used only
to show that the emitting tick's validator belongs to the run's honest set. -/
private theorem emitted_targets_eq_of_schedule (S : Setup V) {rho : Run V}
    (sch : VoteSafetySchedule S rho) {v : V} {a b : NamedAttestation V}
    {ta tb : Time} (ha : rho.emits S v (.attest a) ta)
    (hb : rho.emits S v (.attest b) tb) {h : Height} {T U : BlockId}
    (hT : T ∈ targetsAt a.erase h) (hU : U ∈ targetsAt b.erase h) : T = U := by
  obtain ⟨i, hi, hai⟩ := ha
  have hmem : Event.tick v ta ∈ rho.events := List.mem_of_getElem? hi
  have hv : v ∈ rho.honest := sch.honest_only _ hmem
  exact Proofs.HealingSurface.honestNoDoubleTarget S rho v hv a b ta tb ⟨i, hi, hai⟩ hb
    h T U hT hU

/-- A height pair from one client emission does not conflict with a finality
pair from another emission by the same validator. -/
private theorem conflictsWithFinality_false_of_schedule (S : Setup V) {rho : Run V}
    (sch : VoteSafetySchedule S rho) {v : V} {a b : NamedAttestation V}
    {ta tb : Time} (ha : rho.emits S v (.attest a) ta)
    (hb : rho.emits S v (.attest b) tb) {p : FinalityPair}
    (hfp : a.finality_pair = some p) :
    Protocol.conflictsWithFinality b.erase.height_pair p = false := by
  obtain ⟨h, T⟩ := p
  cases hhp : b.erase.height_pair with
  | empty => simp [Protocol.conflictsWithFinality]
  | timeout g =>
      by_cases hgh : g = h
      · subst g
        exact False.elim
          (Proofs.HealingSurface.no_timeout_against_finality S rho ha hb hfp hhp)
      · simp [Protocol.conflictsWithFinality, hgh]
  | target g U =>
      by_cases hgh : g = h
      · subst g
        have hTU : T = U := emitted_targets_eq_of_schedule S sch ha hb
          (Or.inr hfp) (Or.inl hhp)
        simp [Protocol.conflictsWithFinality, hTU]
      · simp [Protocol.conflictsWithFinality, hgh]

/-- Two height pairs from client emissions do not form E2 evidence. -/
private theorem e2Fields_false_of_schedule (S : Setup V) {rho : Run V}
    (sch : VoteSafetySchedule S rho) {v : V} {a b : NamedAttestation V}
    {ta tb : Time} (ha : rho.emits S v (.attest a) ta)
    (hb : rho.emits S v (.attest b) tb) :
    Protocol.e2Fields a.erase b.erase = false := by
  cases hpa : a.erase.height_pair with
  | empty => simp [Protocol.e2Fields, hpa]
  | timeout h => simp [Protocol.e2Fields, hpa]
  | target h T =>
      cases hpb : b.erase.height_pair with
      | empty => simp [Protocol.e2Fields, hpa, hpb]
      | timeout g => simp [Protocol.e2Fields, hpa, hpb]
      | target g U =>
          by_cases hgh : h = g
          · subst g
            have hTU : T = U := emitted_targets_eq_of_schedule S sch ha hb
              (Or.inl hpa) (Or.inl hpb)
            simp [Protocol.e2Fields, hpa, hpb, hTU]
          · simp [Protocol.e2Fields, hpa, hpb, hgh]

/-- The validator client's signing discipline prevents E1 and E2 between any
two attestations it actually emits. -/
theorem emissionVoteSafety (S : Setup V) : EmissionVoteSafety S := by
  intro rho sch v a b ha hb
  obtain ⟨ta, ha⟩ := ha
  obtain ⟨tb, hb⟩ := hb
  have he1 : Protocol.e1Fields a.erase b.erase = false := by
    cases hfa : a.erase.finality_pair with
    | none =>
        cases hfb : b.erase.finality_pair with
        | none => simp [Protocol.e1Fields, hfa, hfb]
        | some p =>
            have hconf := conflictsWithFinality_false_of_schedule S sch hb ha hfb
            simp [Protocol.e1Fields, hfa, hfb, hconf]
    | some p =>
        have hconfA := conflictsWithFinality_false_of_schedule S sch ha hb hfa
        cases hfb : b.erase.finality_pair with
        | none => simp [Protocol.e1Fields, hfa, hfb, hconfA]
        | some q =>
            have hconfB := conflictsWithFinality_false_of_schedule S sch hb ha hfb
            simp [Protocol.e1Fields, hfa, hfb, hconfA, hconfB]
  have he2 := e2Fields_false_of_schedule S sch ha hb
  simp [Protocol.Slashable, Protocol.slashable,
    Protocol.e1Slashable, Protocol.e2Slashable, he1, he2]

/-- Honest-attributed evidence in any two honest stores is not slashable. -/
theorem attributedVoteSafety (S : Setup V) : AttributedVoteSafety S := by
  intro rho sch auth u v t t' i hi hslash
  obtain ⟨a, ha, b, hb, hav, hbv, hsl⟩ := hslash
  have hcarA := Proofs.NamedStoreBridge.carriedByHonest_of_storeAt S sch.sorted auth u t
  have hcarB := Proofs.NamedStoreBridge.carriedByHonest_of_storeAt S sch.sorted auth v t'
  obtain ⟨ra, ta, hra, hea⟩ := hcarA a ha (by rw [hav]; exact hi)
  obtain ⟨rb, tb, hrb, heb⟩ := hcarB b hb (by rw [hbv]; exact hi)
  have hsafe := emissionVoteSafety S rho sch i ra rb
    ⟨ta, hav ▸ hea⟩ ⟨tb, hbv ▸ heb⟩
  rw [hra, hrb] at hsafe
  exact hsafe hsl

/-- The complete validator-client vote-safety contract. -/
theorem validatorVoteSafety (S : Setup V) : ValidatorVoteSafety S :=
  ⟨emissionVoteSafety S, attributedVoteSafety S⟩

#print axioms emissionVoteSafety
#print axioms attributedVoteSafety
#print axioms validatorVoteSafety

end Proofs
end DecoupledConsensusModel

end
