module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SlashableBound
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Accountable slashable-bound bridge

This module derives `SlashableBound` from core execution and the
one-third fault bound. No participation premise is required. The execution-specific
non-self-slashing support remains in `SlashableBoundRun`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `NoSelfSlashing` follows from the final Section 7 execution contract. It
is not an additional honest-behavior assumption. -/
theorem noSelfSlashing_of_admissibleCore (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) : AlignedRoundLemmas.NoSelfSlashing S rho := by
  intro v a b ha hb
  obtain ⟨ta, ha⟩ := ha
  obtain ⟨tb, hb⟩ := hb
  have he1 : Protocol.e1Fields a.erase b.erase = false := by
    cases hfa : a.erase.finality_pair with
    | none =>
        cases hfb : b.erase.finality_pair with
        | none => simp [Protocol.e1Fields, hfa, hfb]
        | some p =>
            have hconf := conflictsWithFinality_false_of_admissibleCore S adm hb ha hfb
            simp [Protocol.e1Fields, hfa, hfb, hconf]
    | some p =>
        have hconfA := conflictsWithFinality_false_of_admissibleCore S adm ha hb hfa
        cases hfb : b.erase.finality_pair with
        | none => simp [Protocol.e1Fields, hfa, hfb, hconfA]
        | some q =>
            have hconfB := conflictsWithFinality_false_of_admissibleCore S adm hb ha hfb
            simp [Protocol.e1Fields, hfa, hfb, hconfA, hconfB]
  have he2 := e2Fields_false_of_admissibleCore S adm ha hb
  simp [Protocol.slashable, Protocol.e1Slashable,
    Protocol.e2Slashable, he1, he2]

/-- On a core execution, `BelowOneThird` implies the accountable bound.
There is no participation or honest self-slashing hypothesis. -/
theorem slashableBound_of_admissibleCore_belowOneThird (S : Setup V)
    {rho : Run V} (adm : AdmissibleCore S rho)
    (hbot : BelowOneThird S rho.honest) : SlashableBound S rho :=
  AlignedRoundLemmas.slashableBound_of_belowOneThird hbot
    (noSelfSlashing_of_admissibleCore S adm)
    (fun _ hB => Proofs.NamedStoreBridge.carriedByHonest_of_runBlock S adm hB)


/-- Full-participation specialization of the accountable bound. -/
theorem slashableBound_of_admissible_belowOneThird (S : Setup V)
    {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest) : SlashableBound S rho :=
  slashableBound_of_admissibleCore_belowOneThird S adm.toNamedAdmissibleCore hbot

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
