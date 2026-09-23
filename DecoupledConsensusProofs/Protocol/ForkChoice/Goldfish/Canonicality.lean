module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.GSTZero
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The active relative-SG window -/

/-- The compatibility form of `Proofs.Optimistic.SupportAligned`.

Every honest validator is present in the denominator, and the exact support
vote selected for that validator resolves to a head compatible with `B`.
The predicate does not require that the head precede `B`; compatibility is the
smallest fact needed to exclude a relative-majority step onto a conflicting
branch. -/
structure SupportCompatible (pool : Round → Finset (Protocol.SGVote V))
    (etaSG : Round) (T : Finset (Block V)) (Hon : Finset V) (r : Round)
    (B : Block V) : Prop where
  /-- Every honest validator contributes to the represented-weight
  denominator. -/
  represented : ∀ v ∈ Hon, Protocol.represented pool etaSG v r = true
  /-- Every selected honest support head is compatible with `B`. -/
  heads : ∀ v ∈ Hon, ∀ u : Protocol.SGVote V,
    Protocol.latest_support_vote pool etaSG T v r = some u →
      Proofs.HealingLemmas.rootCompatible T B u.confirmed = true

omit [Fintype V] in
/-- A head below `Can` is compatible with every block compatible with `Can`.
This is the bridge from the existing directed alignment interfaces to the
compatibility invariant used here. -/
theorem rootCompatible_of_rootOnCan_of_compatible
    {T : Finset (Block V)} {Can B : Block V} {head : Option BlockId}
    (hon : Proofs.Optimistic.rootOnCan T Can head = true)
    (hCanB : Block.compatible Can B = true) :
    Proofs.HealingLemmas.rootCompatible T B head = true := by
  cases head with
  | none => rfl
  | some root =>
    simp only [Proofs.Optimistic.rootOnCan] at hon
    simp only [Proofs.HealingLemmas.rootCompatible]
    cases hfind : Block.find? T root with
    | none => rfl
    | some H =>
      rw [hfind] at hon
      change Block.preceq H Can = true at hon
      change Block.compatible H B = true
      simp only [Block.compatible, Bool.or_eq_true] at hCanB
      rcases hCanB with hCanB | hBCan
      · simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inl (Block.preceq_trans hon hCanB)
      · exact Block.compatible_of_preceq_common hon hBCan

omit [Fintype V] in
/-- Directed support alignment to a compatible tip supplies the local
compatibility window. Existing run-level agreement producers can therefore
be reused without changing their stronger statements. -/
theorem SupportCompatible.of_supportAligned
    {pool : Round → Finset (Protocol.SGVote V)} {etaSG : Round}
    {T : Finset (Block V)} {Hon : Finset V} {r : Round} {Can B : Block V}
    (hal : Proofs.Optimistic.SupportAligned pool etaSG T Hon r Can)
    (hCanB : Block.compatible Can B = true) :
    SupportCompatible pool etaSG T Hon r B :=
  ⟨hal.represented, fun v hv u hu =>
    rootCompatible_of_rootOnCan_of_compatible (hal.heads v hv u hu) hCanB⟩








/-! ## Honest target history and the FG root -/





/-! ## The composed local canonicality window -/



end Protocol
end DecoupledConsensusModel

end
