module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4GSTZeroOpeningLifecycle

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Proofs.HealingSurface
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The premise -/




/-! ## The bridge to the grade-forming majority -/

/-- Every honest validator awake in a round is an actual voter of that round:
the awake branch of the tick scheduler emits the round's attestation. -/
theorem awakeRound_subset_honestRoundVoters
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {r : Round} (hhor : S.a r ≤ rho.horizon) :
    rho.honest.filter (fun v => (S.node v).awake r = true) ⊆
      Internal.NamedOutageEntry.honestRoundVoters S rho r := by
  intro u hu
  obtain ⟨huHon, huAwake⟩ := Finset.mem_filter.mp hu
  refine (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mpr ?_
  exact ⟨huHon, actionAttestationAt S rho u r,
    (actionAttestationAt_shape S rho u r).1,
    (actionAttestationAt_shape S rho u r).2.1,
    honest_emits_exact_actionAttestationAt_of_awake S sch huHon r huAwake hhor⟩

#print axioms awakeRound_subset_honestRoundVoters



/-! ## The fast result -/



end Proofs
end DecoupledConsensusModel

end
