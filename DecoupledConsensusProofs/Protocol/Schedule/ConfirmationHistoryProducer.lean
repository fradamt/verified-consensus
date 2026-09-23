module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.AttestationCanonicality
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Protocol.Grades.HonestMajority

@[expose] public section

/-!
# Event-prefix producer for confirmation history

The run list is the smallest well-founded order for canonical-history
production. It identifies the exact store that an attestation action reads,
and it does not impose an artificial order on different validators' ticks at
the same public time.

This file provides two independent prefix folds.

* `CanonicalHistoryAtIndex` accumulates honest target roots, confirmed roots,
  and concrete height-gate source blocks.
* `HonestSelectionChainAtIndex` accumulates pairwise compatibility of actual
  Section 7 confirmation selections. Its successor premise compares a new
  selection with all earlier selections; two selections at the same event
  index are definitionally equal.

Time- and proposal-facing histories are projections of these event-prefix
states. The round-action step is closed below from directed prior selections:
the same-event selection orients `live_confirmed`, the prefix orients grade 2,
and GST-zero relay orients the integrated SG root. The remaining protocol
boundary contains the concrete Goldfish vote duty and root resolution at a
confirmation tick. The assembled state also exposes the final honest-vote and
adoption facts. Neither prefix fold assumes proposer-walk transfer.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]




/-- Collision-free run blocks with the same root are the same block. -/
theorem runBlock_eq_of_root_eq
    {S : Setup V} {rho : Run V} (hcf : RootCollisionFree S rho)
    {X Y : NamedBlock V} (hX : RunBlock S rho X) (hY : RunBlock S rho Y)
    (hroot : X.erase.root = Y.erase.root) : X.erase = Y.erase := by
  have hinj := Proofs.Bridges.rootInjectiveBelow_of_runBlocks S hcf
    (T := ({X, Y} : Finset (NamedBlock V)))
    (by
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hX
      · rw [Finset.mem_singleton.mp hC]
        exact hY)
  exact hinj X.erase Y.erase
    ⟨X.erase, Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _),
      Block.preceq_self _⟩
    ⟨Y.erase, Finset.mem_image_of_mem _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
      Block.preceq_self _⟩ hroot

/-! ## Canonical history through an event prefix -/




















/-- A support cutoff that precedes slot `s`'s vote duty already precedes the
slot proposal. There is no confirmation-write instant in the open interval
from proposal to vote. -/
theorem support_cutoff_lt_vote_time_imp_lt_proposal_time
    (E : Env V) {k s : Slot}
    (h : Protocol.support_cutoff E k < Protocol.vote_time E s) :
    Protocol.support_cutoff E k < Protocol.proposal_time E s := by
  have hvoteCut : Protocol.vote_time E s < Protocol.support_cutoff E s := by
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ E.Δ_pos
  have hks : k < s := by
    by_contra hnot
    have hsk : s ≤ k := Nat.le_of_not_gt hnot
    have hmono := Proofs.Optimistic.support_cutoff_mono E hsk
    have hbad : Protocol.vote_time E s < Protocol.support_cutoff E k :=
      lt_of_lt_of_le hvoteCut hmono
    exact (not_lt_of_ge (le_of_lt h)) hbad
  have hnext : Protocol.support_cutoff E k <
      Protocol.proposal_time E (k + 1) := by
    unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
    push_cast
    have h24 : 2 * E.Δ < 4 * E.Δ :=
      Int.mul_lt_mul_of_pos_right (by decide : (2 : Int) < 4) E.Δ_pos
    calc
      4 * E.Δ * (k : Int) + 2 * E.Δ <
          4 * E.Δ * (k : Int) + 4 * E.Δ :=
        Int.add_lt_add_left h24 _
      _ = 4 * E.Δ * ((k : Int) + 1) := by ring
  have hmono : Protocol.proposal_time E (k + 1) ≤
      Protocol.proposal_time E s :=
    proposal_time_mono E (Nat.succ_le_iff.mpr hks)
  exact lt_of_lt_of_le hnext hmono

/-! ## Pairwise safety of actual selections -/










end Protocol
end DecoupledConsensusModel

end
