module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransport
public import DecoupledConsensusProofs.Protocol.Handlers.NonInterference
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Assembly

@[expose] public section

/-!
# Viability from the outage carrier band

This module exposes the read-level K6 split. A reader whose finalized block
has passed the protected block needs no viability witness. Otherwise the
intrinsic conflicting-carrier band supplies the witness through the named
`viable_after_boundary` route.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol

set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The read-level K6 split, with the band and entry history explicit. -/
theorem fgRootAbove_or_filtered_at_read
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hband : IntrinsicConflictingCarrierBand S rho Pn r)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (t : Time)
    (hb0 : b0 ≤ t) (ht : t < S.a r) :
    Block.Preceq Pn.erase
        (Protocol.get_fg_root
          (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
      Pn.erase ∈ Protocol.get_filtered_block_tree
        (NamedRun.readAt S rho t w).st.core.toHealing.toFG := by
  exact (fg_noninterference_after_boundary_readAt S rho b0 b1 s r Pn hexec
    hslash hmargin hsleep hscope hno hband hentry hheld0 w hw t hb0 ht).2.1

/-! The entry-history form derives the conflicting band from the same history.
This is the form used when the outage half supplies `hentry` directly. -/

theorem fgRootAbove_or_filtered_at_read_of_entry
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (t : Time)
    (hb0 : b0 ≤ t) (ht : t < S.a r) :
    Block.Preceq Pn.erase
        (Protocol.get_fg_root
          (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
      Pn.erase ∈ Protocol.get_filtered_block_tree
        (NamedRun.readAt S rho t w).st.core.toHealing.toFG := by
  exact fgRootAbove_or_filtered_at_read S rho b0 b1 s r Pn hexec hslash hmargin
    hsleep hscope hno
    (NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band S rho b0 b1 s r Pn
      hexec hmargin hsleep hentry)
    hentry hheld0 w hw t hb0 ht

/-! A future round can be covers any read: the next action is after the
read. The history family is the internal producer supplied by the outage or
healthy-prefix proof. -/


theorem fgRootAbove_or_filtered_at_stateBeforeTime_of_entry
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (t : Time)
    (hb0 : b0 ≤ t) (ht : t ≤ S.a r) :
    Block.Preceq Pn.erase
        (Protocol.get_fg_root
          (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG) ∨
      Pn.erase ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG := by
  exact (fg_noninterference_after_boundary S rho b0 b1 s r Pn hexec hslash
    hmargin hsleep hscope hno
    (NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band S rho b0 b1 s r Pn
      hexec hmargin hsleep hentry)
    hentry hheld0 w hw t hb0 ht).2.1

/-! The same history route supplies the FG-root compatibility family used by
the post-outage seed and continuation consumers. -/

theorem fg_compatible_at_read_of_entry
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (t : Time)
    (hb0 : b0 ≤ t) (ht : t < S.a r) :
    Block.compatible Pn.erase
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG) = true := by
  have hsplit := (fg_noninterference_after_boundary S rho b0 b1 s r Pn
    hexec hslash hmargin hsleep hscope hno
    (NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band S rho b0 b1 s r Pn
      hexec hmargin hsleep hentry)
    hentry hheld0 w hw t hb0 ht.le).2.1
  rcases hsplit with hroot | hmem
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl hroot
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Proofs.Records.preceq_get_fg_root_of_mem_filtered hmem)

theorem fg_compatible_at_confirmation_read_of_entry
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s q : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn (q + 2))
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (u : Time)
    (hhi : u < domain S.E S.hc (q + 2) .g2)
    (hb0 : b0 ≤ u) :
    Block.compatible Pn.erase
      (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true := by
  have hu : u < S.a (q + 2) :=
    hhi.trans_le ((domain_le_opening S (q + 2)).trans (incl_opening_le_a S (q + 2)))
  have hcompat := fg_compatible_at_read_of_entry S rho b0 b1 s (q + 2) Pn
    hexec hslash hmargin hsleep hscope hno hentry hheld0 w hw u hb0 hu
  change Block.compatible Pn.erase
    (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) = true
  exact hcompat

/-! The exact `hfg` family used by the post-outage transport. -/


/-! The checkpoint form used by `hjoint`. -/

theorem jointAt_of_entry_history
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hb0 : b0 ≤ S.a r) (_hhor : S.a r ≤ rho.horizon)
    (w : V) (hw : w ∈ rho.honest) :
    Internal.NamedJointOutage.JointAt S rho Pn r w := by
  have h := fg_noninterference_after_boundary S rho b0 b1 s r Pn hexec hslash
    hmargin hsleep hscope hno
    (NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band S rho b0 b1 s r Pn
      hexec hmargin hsleep hentry)
    hentry hheld0 w hw (S.a r) hb0 le_rfl
  have hpair :
      (Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Protocol.get_filtered_block_tree
          (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) ∧
      Block.compatible Pn.erase
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F = true :=
    ⟨h.2.1, h.2.2⟩
  simpa only [Internal.NamedJointOutage.JointAt,
    Internal.NamedJointOutage.checkpoint,
    Internal.NamedStableChainOutage.roundConfirmationRead,
    Internal.NamedOutageEntry.confirmationReadAt,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hpair

/-! Action and relative-G2 instances of the same disjunctive producer. -/






#print axioms fgRootAbove_or_filtered_at_read
#print axioms fgRootAbove_or_filtered_at_read_of_entry
#print axioms fgRootAbove_or_filtered_at_stateBeforeTime_of_entry
#print axioms fg_compatible_at_read_of_entry
#print axioms fg_compatible_at_confirmation_read_of_entry
#print axioms jointAt_of_entry_history

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
