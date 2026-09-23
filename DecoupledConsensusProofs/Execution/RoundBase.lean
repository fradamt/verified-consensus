module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.CommonSupportBase
public import DecoupledConsensusProofs.Protocol.Grades.SGFromSupport
public import DecoupledConsensusProofs.Protocol.Handlers.CheckpointRows
public import DecoupledConsensusProofs.Execution.ConflictingCarrierBand

@[expose] public section

/-!
# L7: the round invariant at the first included round

`RoundInvariant S rho b0 Pn r` assembled at the first round whose action is at
or after the outage boundary. Every field is plumbing: `fg` is L4
(`fg_noninterference_after_boundary`) read at `S.a r`, `common_support` is L6
(`common_support_base`) and `sg` is L5 (`sg_at_checkpoint_of_common_support`);
the two row fields and the band are available production lemmas.

The one step with content is `hpost`. L5 needs every honest SG vote emitted at
or after `b0` in a round below `r` to confirm above the protected prefix; at
later rounds that comes from the invariant at the earlier included rounds, but
at the FIRST included round it is vacuous, because an honest round-`q` vote is
emitted at `S.a q ≤ S.a (r - 1) < b0` for every `q < r`. `base_hpost` below is
that observation.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


private theorem base_le_pred : ∀ q r : Nat, q < r → q ≤ r - 1 := by
  intro q r h; omega

/-- The post-boundary confirmation premise of L5 is vacuous at the first
included round: an honest attestation of a round below `r` is emitted at that
round's action time, which is at or below `S.a (r - 1)`, hence strictly before
`b0`. No hypothesis about the emission's content is used. -/
theorem base_hpost (S : Setup V) (rho : NamedRun V) (b0 : Time) (r : Round)
    (Pn : NamedBlock V) (hfirst : S.a (r - 1) < b0) :
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase := by
  intro a t _ha hem hb0t hlt key _hkey K _hKrun _hKroot
  exfalso
  obtain ⟨_, _, _, _, _, _, ht, _⟩ := Proofs.NamedOutageInputs.emitted_attestation_stages S rho hem
  subst ht
  exact absurd (le_trans hb0t
    (Assembly.a_mono S (base_le_pred a.round r hlt))) (not_le.mpr hfirst)


#print axioms base_hpost

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
