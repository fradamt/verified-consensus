module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroPreparedWalk

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Positive GST-zero prepared vote-store extension, prebuilt over pins -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem honestVoteStoresExtend_positive_of_gstZero_of_pins
    (hsucc : ∀ (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
      {d : Slot}, 1 ≤ d →
      Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon →
      S.E.proposer (d + 1) ∈ rho.honest →
      ∀ {B : NamedBlock V}, proposedBlockAt S rho (d + 1) = some B →
      ∀ v ∈ rho.honest,
        Proofs.Optimistic.NamedVoteStoreExtends S rho v (d + 1)
          (namedWalkTargetTree S rho (d + 1) v B)
          (proposedParent S rho (d + 1)) B)
    (hone : ∀ (S : Setup V) {rho : Run V} (h : WeakGenesis S rho),
      Protocol.confirmation_time S.E 1 ≤ rho.horizon →
      S.E.proposer 1 ∈ rho.honest →
      ∀ {B : NamedBlock V}, proposedBlockAt S rho 1 = some B →
      ∀ v ∈ rho.honest,
        Proofs.Optimistic.NamedVoteStoreExtends S rho v 1
          (namedWalkTargetTree S rho 1 v B)
          (proposedParent S rho 1) B)
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    ∀ v ∈ rho.honest,
      Proofs.Optimistic.NamedVoteStoreExtends S rho v s
        (namedWalkTargetTree S rho s v B)
        (proposedParent S rho s) B := by
  cases s with
  | zero => exact False.elim ((Nat.lt_irrefl 0) hs)
  | succ d =>
    cases d with
    | zero => exact hone S h hhor hprop hB
    | succ k =>
      exact hsucc S h (Nat.succ_le_succ (Nat.zero_le k)) hhor hprop hB

#print axioms honestVoteStoresExtend_positive_of_gstZero_of_pins

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
