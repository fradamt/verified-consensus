module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4D2PreparedFinality
public import DecoupledConsensusProofs.Generic.W4D3FinalitySpineCompose
public import DecoupledConsensusProofs.Protocol.Grades.W4D2LandedPins
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix
public import DecoupledConsensusProofs.Protocol.Grades.W4GSTZeroOpeningLifecycle
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedExecution
public import DecoupledConsensusProofs.Protocol.Grades.W4PredecessorSource
public import DecoupledConsensusProofs.Execution.W4RecoverySpine

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # D2 source callback at its actual selected-carrier call site
The existing prepared D2 theorem requests the predecessor-source callback at
every round after `q + 2`. Its body calls that callback only at the selected
carrier `r`, where `q + extra + 4 ≤ r` and the confirmation of
`opening_slot r + 2` is inside the run. This leaf retains that exact guard.
The source proof uses the selected named fold. The previous honest opening
lifecycle supplies the live confirmation, the prepared anchor bound, and G0
clearance. Non-lostness is obtained at `r - 1` from `w4NonLost_of_named`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The stage-1 named fold, specialized to the selected handoff round. -/
def W4SelectedNamedFoldAtEverySlot
    (S : Setup V) (rho : Run V) (q : Round) (M0 : Height)
    (D : NamedBlock V) : Prop :=
  ∀ {s : Slot}, S.hc.opening_slot q + 3 ≤ s →
    Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
    ∃ F : Slot → Block V, ∃ End : Block V,
      MovingSlotFoldAtN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (S.hc.opening_slot q + 3) s F End ∧
      F (S.hc.opening_slot q + 3) = D.erase

/-- The predecessor-source callback at D2's only call site. -/
def W4PreparedSelectedSourceAt
    (S : Setup V) (rho : Run V) (q : Round) (extra : Nat) : Prop :=
  ∀ (r : Round), q + extra + 4 ≤ r →
    ProposerOpeningCarrierAt S rho r →
    Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
    ∀ {Pprev : NamedBlock V},
      proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Pprev →
      S.a (r - 1) ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        actionFGSource S (actionReadAt S rho v (r - 1)) = some Pprev.erase

/-- Private arithmetic twin of `boundary_cutoff_le_next_action` from
`W4CarryWindowRun`; that declaration is private in its source leaf. -/
private theorem w4dt_boundaryCutoff_le_nextAction
    (S : Setup V) (q : Round) :
    Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤ S.a (q + 1) := by
  have hsupport : Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) =
      (4 * ((S.hc.opening_slot q + 2 : Slot) : Time) + 2) * S.E.Δ := by
    unfold Protocol.support_cutoff Env.t slotStart
    ring
  have haction : S.a (q + 1) =
      (4 * ((S.hc.opening_slot (q + 1) : Slot) : Time) + 6) * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a slotStart
    ring
  rw [hsupport, haction]
  apply Int.mul_le_mul_of_nonneg_right _ (le_of_lt S.E.Δ_pos)
  have hslots : S.hc.opening_slot q + 2 ≤ S.hc.opening_slot (q + 1) := by
    simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
      Nat.add_le_add_left S.hc.R_ge_two (q * S.hc.R)
  have hcast : ((S.hc.opening_slot q + 2 : Slot) : Time) ≤
      ((S.hc.opening_slot (q + 1) : Slot) : Time) := by
    exact_mod_cast hslots
  have hmul := Int.mul_le_mul_of_nonneg_left hcast (by norm_num : (0 : Int) ≤ 4)
  omega

/-- Private arithmetic twin of `gammaNegOne_le_action` from
`W4CarryWindowRun`; that declaration is private in its source leaf. -/
private theorem w4dt_gammaNegOne_le_action (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ r ≤ S.a r := by
  have hgamma : S.hc.Γ_neg1 S.E.Δ r =
      (4 * ((S.hc.opening_slot r : Slot) : Time) - 1) * S.E.Δ := by
    unfold Protocol.HealConfig.Γ_neg1 slotStart
    ring
  have haction : S.a r =
      (4 * ((S.hc.opening_slot r : Slot) : Time) + 6) * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a slotStart
    ring
  rw [hgamma, haction]
  apply Int.mul_le_mul_of_nonneg_right _ (le_of_lt S.E.Δ_pos)
  omega

private theorem w4dt_sourceGuard_prev
    {q r extra : Nat} (h : q + extra + 4 ≤ r) : q + 2 < r - 1 := by
  omega

private theorem w4dt_sourceGuard_start
    {q r extra : Nat} (h : q + extra + 4 ≤ r) : q + 1 ≤ r - 2 := by
  omega

/-- Close the selected predecessor-source callback from the stage-1 named
fold and the public finality premises. -/
theorem w4PreparedSelectedSourceAt_of_fold
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {gap extra q : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S extra)
    (rGST : Round) (hpost : S.E.t_GST ≤ S.a rGST)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap extra +
      3 * progressLag' gap extra + 1 ≤ q)
    {M0 : Height} {D : NamedBlock V}
    (hfoldAt : W4SelectedNamedFoldAtEverySlot S rho q M0 D) :
    W4PreparedSelectedSourceAt S rho q extra := by
  intro r hlate hopening hcarrierHor Pprev hPprev hprevHor
  change q + extra + 4 ≤ r at hlate
  have hprevLate : q + 2 < r - 1 := w4dt_sourceGuard_prev hlate
  have hqPrev : q + 1 ≤ r - 2 := w4dt_sourceGuard_start hlate
  have hdeadlinePrev :
      fgSafetyProgressDeadline S rho rGST gap extra + 2 ≤
        r - 1 := by
    have hL : 1 ≤ progressLag' gap extra := progressLag'_pos gap
    have hmul : 3 * 1 ≤ 3 * progressLag' gap extra :=
      Nat.mul_le_mul_left 3 hL
    have htail : 2 ≤ 3 * progressLag' gap extra + 1 :=
      (by decide : (2 : Nat) ≤ 4).trans
        (by simpa only [Nat.mul_one] using Nat.add_le_add_right hmul 1)
    have hdeadlineQ := (Nat.add_le_add_left htail
      (fgSafetyProgressDeadline S rho (rGST) gap extra)).trans hqLate
    exact hdeadlineQ.trans
      ((Nat.le_add_right q 2).trans (Nat.le_of_lt hprevLate))
  have hprevConfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hprevHor
  have hlifecycle :=
    honestProposal_actionSelectors_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay (hpost)
      hdeadlinePrev hopening.2.1 hPprev hprevConfHor
  have hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v (r - 1)).live_confirmed = Pprev.erase := by
    intro v hv
    exact honestProposal_liveConfirmed_at_action_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay (hpost)
      hdeadlinePrev hopening.2.1 hPprev hprevConfHor v hv
  have hanchor : ∀ v ∈ rho.honest,
      Block.Preceq
        (PhaseGrades.nodeAnchor S (actionReadAt S rho v (r - 1)) (r - 1))
        Pprev.erase := by
    intro v hv
    exact (hlifecycle v hv).2.1
  have hclear : ∀ v ∈ rho.honest,
      PhaseGrades.nodeClear S (actionReadAt S rho v (r - 1)) (r - 1)
        Pprev.erase = true := by
    intro v hv
    exact (hlifecycle v hv).2.2
  have hstartSlot : S.hc.opening_slot q + 3 ≤
      S.hc.opening_slot r + 3 := by
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right S.hc.R
        ((Nat.le_add_right q 2).trans
          (Nat.le_of_lt (hprevLate.trans_le (Nat.sub_le r 1))))) 3
  have hfoldHor : Protocol.confirmation_time S.E
      ((S.hc.opening_slot r + 3) - 1) ≤ rho.horizon := by
    simpa only [Nat.add_sub_cancel] using hcarrierHor
  obtain ⟨F, End, hfold, _hbase⟩ := hfoldAt hstartSlot hfoldHor
  have hfoldStart : S.hc.opening_slot q + 3 ≤
      S.hc.opening_slot (r - 1) := by
    have hq1 : q + 1 < r - 1 :=
      (Nat.le_succ (q + 1)).trans_lt hprevLate
    have hfirst := Nat.add_le_add_right
      (openingSlot_add_two_le_openingSlot_of_lt S (Nat.lt_succ_self q)) 1
    exact hfirst.trans ((Nat.le_succ (S.hc.opening_slot (q + 1) + 1)).trans
      (openingSlot_add_two_le_openingSlot_of_lt S hq1))
  have hfoldEnd : S.hc.opening_slot (r - 1) + 1 <
      S.hc.opening_slot r + 3 := by
    have hrpos : 0 < r :=
      Nat.zero_lt_of_lt ((Nat.zero_le (q + 2)).trans_lt
        (hprevLate.trans_le (Nat.sub_le r 1)))
    have hrlt : r - 1 < r := Nat.sub_lt hrpos (by decide)
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      ((openingSlot_add_two_le_openingSlot_of_lt S hrlt).trans
        (Nat.le_add_right (S.hc.opening_slot r) 3))
  have hstartPrev : Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤
      S.a (r - 2) :=
    (w4dt_boundaryCutoff_le_nextAction S q).trans (Assembly.a_mono S hqPrev)
  have hrGSTPrev : rGST ≤ r - 2 := by
    have hrGSTDeadline : rGST ≤
        fgSafetyProgressDeadline S rho rGST gap extra := by
      unfold fgSafetyProgressDeadline
      exact (Nat.le_succ _).trans (Nat.le_add_right _ _)
    exact hrGSTDeadline.trans
      ((Nat.le_add_right
        (fgSafetyProgressDeadline S rho rGST gap extra)
          (3 * progressLag' gap extra + 1)).trans
        (hqLate.trans ((Nat.le_succ q).trans hqPrev)))
  have hpostPrev : S.E.t_GST ≤ S.a (r - 2) :=
    hpost.trans (Assembly.a_mono S hrGSTPrev)
  have hcutPrev : S.hc.Γ_neg1 S.E.Δ (r - 1) ≤ rho.horizon :=
    (w4dt_gammaNegOne_le_action S (r - 1)).trans hprevHor
  have hnlPrev : ¬ LostRoundAt S rho (r - 1) :=
    w4NonLost_of_named_at S adm hcom hbelow hrec hdelay rGST hpost q hqLate
      (r - 1) hprevLate (by
        simpa only [Nat.sub_sub, Nat.reduceAdd] using hopening.1) (by
        have hmono : S.hc.opening_slot (r - 1) + 2 ≤
            S.hc.opening_slot r + 2 := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_right S.hc.R (Nat.sub_le r 1)) 2
        exact (Int.add_le_add_right (proposal_time_mono S.E hmono) _).trans
          hcarrierHor)
  exact w4_predecessorSourceAt_of_fold S adm hcom hbelow
    (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow) (q := q)
    (hprevLate.trans_le (Nat.sub_le r 1))
    hopening hPprev hprevHor hlive hanchor hclear hfold
    ⟨hfoldStart, hfoldEnd⟩ hstartPrev hpostPrev hcutPrev hnlPrev

#print axioms w4PreparedSelectedSourceAt_of_fold






end HealingSurface
end Proofs
end DecoupledConsensusModel

end
