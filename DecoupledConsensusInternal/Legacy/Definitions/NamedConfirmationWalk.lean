module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.ConfirmationScore
public import DecoupledConsensusInternal.Legacy.Definitions.NamedDutyReads

@[expose] public section

/-!
# Named confirmation walk and genuine confirmation 

The confirmation duty's ordinary composed walk starts at the SG root of the
prepared read's contract, not at the prior core selector. The GF early/late
vote sets, score and gate are profile-independent and keep their bodies;
only the anchor changes. `confirmationInputStore` (Confirmation.lean:36) is
corrected to the named reader projection
`(NamedActionReads.confirmationReadAt S ρ v (confirmation_time s)).st.core`,
which needs no new import there. The five pure score/gate definitions
live in `ConfirmationScore.lean` (owner split); this file does
not import `Confirmation.lean`. `Confirmation.lean` imports both, drops its
own `confirmationWalk` and `GenuineConfirmationAt` (retired to prior), and
`Props/UserConfirmationHistory.lean:17` calls `namedConfirmationWalk S n
(S.E.slotOf time - 1)` on the prepared read it derives from.
-/


namespace DecoupledConsensusModel.Internal
open Execution NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The walk the named confirmation duty tests on the prepared read `n` at
slot `s`: ghost from the contract's SG root over the filtered tree, with the
profile-independent score and gate on the read's core store. -/
def namedConfirmationWalk (S : Setup V) (n : NamedNodeState V) (s : Slot) : Block V :=
  let st := n.st.core
  let A := Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc
    st.toHealing (S.hc.round_of st.s)
  let tree := Protocol.get_filtered_block_tree st.toHealing.toFG
  Protocol.ghost A tree (confirmationScore S.E st s) (confirmationEligible S.E st s)

/-- Replacement body for `GenuineConfirmationAt`: the actual slot-`s`
evaluation records the named walk and that walk clears the gate on the same
read's core store. The `get_fg_root` fallback stays excluded. -/
def GenuineConfirmationAt (S : Setup V) (ρ : Run V) (v : V) (s : Slot) : Prop :=
  let n := confirmationInputRead S ρ v s
  (ρ.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
      namedConfirmationWalk S n s ∧
    confirmationEligible S.E n.st.core s (namedConfirmationWalk S n s) = true

end DecoupledConsensusModel.Internal

end
