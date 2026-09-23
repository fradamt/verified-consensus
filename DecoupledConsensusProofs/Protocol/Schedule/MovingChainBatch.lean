module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.MovingChainBase
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalRegimeRound

@[expose] public section

/-!
# The round batch is complete at every honest reader

`batchComplete` is the one field of the two finality hand-off records that is
not a geometric read of the moving chain: it says that every honest author is
represented in every honest reader's round batch by that author's exact
previous-round action vote, resolved before the batch cutoff.

Three of its five clauses are delivery facts that already exist
(`actionSGVote_mem_next_round_batch` and `actionSGVote_stamp_before_next_Γ_neg1`
in `GradeBootstrapCoreRun`, plus two definitional ones). The two that are not
concern the author's SG CARRIER BLOCK: the reader must be able to resolve it by
root, and its own receipt must precede the cutoff. Both come from the moving
chain: the carrier is below the fold's endpoint at the round's opening slot,
that endpoint is an ancestor of an available honest head of the slot before it,
and availability gives membership and a stamp for every ancestor at once.

The resolution clause is what forces `R ≥ 2`. The vote is emitted at
`a_r = t_{opening_slot r} + 6Δ` and is delivered within one further delay; the
cutoff is `Γ⁻¹_{r+1} = t_{opening_slot (r+1)} - Δ`. With `R = 2` those are
`t_{opening_slot r} + 7Δ` on both sides, so the vote lands exactly one delay
before the cutoff and no slack remains.
-/

/-! ## 1. Schedule facts around the batch cutoff -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]








/-- The action store's grade view is the plain read's. -/
theorem actionGradeView_eq_gradeViewAt'''
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).toHealing.gradeView = gradeViewAt S rho v r := by
  rfl



/-- An available honest slot-`c` head above `P` puts every ancestor of `P` in
the reader's tree, stamped before the slot-`c` support cutoff. -/
theorem storeBeforeTime_mem_stamp_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {c : Slot} {P A : Block V} {w : V} {Gamma : Time}
    (havailable : HonestHeadsAvailableBefore S rho c w
      (Protocol.support_cutoff S.E c))
    (hcut : Protocol.support_cutoff S.E c ≤ Gamma)
    (hvotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq P X))
    (hAP : Block.Preceq A P) :
    A ∈ (rho.storeBeforeTime S w Gamma).T ∧
      stampedBefore (rho.storeBeforeTime S w Gamma).timestamp_block
        (Protocol.support_cutoff S.E c) A = true := by
  have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
    have hcc := hcom c
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxCommittee : x ∈ S.E.committee c := (Finset.mem_inter.mp hx).1
  have hxHonest : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
  obtain ⟨X, hPX, hXrun, hXemit⟩ := hvotes x hxHonest hxCommittee
  have hAX : Block.Preceq A X.erase := Block.preceq_trans hAP hPX
  rcases havailable X.erase
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩ with
    hXgen | hXadmit
  · have hAgen : A = Block.genesis :=
      Block.preceq_antisymm (hXgen ▸ hAX) (Protocol.preceq_genesis A)
    rw [hAgen]
    exact genesis_mem_and_stamp_storeBeforeTime S adm.toNamedScheduleWellFormed
      w Gamma (Protocol.support_cutoff S.E c)
  · exact Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at
      S adm hXadmit hAX hcut




end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms actionGradeView_eq_gradeViewAt'''
#print axioms storeBeforeTime_mem_stamp_of_cone
end DecoupledConsensusModel.Proofs.HealingSurface

end
