module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.FGSafetyProgressDeadline
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightProgress
public import DecoupledConsensusProofs.Protocol.Grades.EventualHeightProgress
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightProgressFixedRoot
public import DecoupledConsensusProofs.Execution.SeedSourceCapClosure
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedRootSourceCap

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Finite handover height bounds from progress
Two height-progress increments put the previous frontier below the later honest
proposal. A delivery step puts every honest reader above the previous frontier.
The strong bootstrap supplies these finite facts; they are not standing
premises for the weaker continuation.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Internal.HealingSurface
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem action_eq_proposalTime_add (S : Setup V) (q : Round) :
    S.a q = Protocol.proposal_time S.E (S.hc.opening_slot q) + 6 * S.E.Δ := rfl

private theorem voteTime_eq_proposalTime_add (S : Setup V) (s : Slot) :
    Protocol.vote_time S.E s = Protocol.proposal_time S.E s + S.E.Δ := rfl

private theorem confirmationTime_eq_proposalTime_add (S : Setup V) (s : Slot) :
    Protocol.confirmation_time S.E s = Protocol.proposal_time S.E s + 6 * S.E.Δ :=
  rfl

private theorem voteTime_le_confirmationTime (S : Setup V) (s : Slot) :
    Protocol.vote_time S.E s ≤ Protocol.confirmation_time S.E s := by
  rw [voteTime_eq_proposalTime_add, confirmationTime_eq_proposalTime_add]
  have h : ∀ p d : Int, 0 < d → p + d ≤ p + 6 * d := by
    intro p d hd
    omega
  exact h _ _ S.E.Δ_pos

private theorem voteTime_add_delta_le_confirmationTime (S : Setup V) (s : Slot) :
    Protocol.vote_time S.E s + S.E.Δ ≤ Protocol.confirmation_time S.E s := by
  rw [voteTime_eq_proposalTime_add, confirmationTime_eq_proposalTime_add]
  have h : ∀ p d : Int, 0 < d → p + d + d ≤ p + 6 * d := by
    intro p d hd
    omega
  exact h _ _ S.E.Δ_pos


private theorem openingSlot_succ_lt_next (S : Setup V) (r : Round) :
    S.hc.opening_slot r + 1 < S.hc.opening_slot (r + 1) := by
  simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
    Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two) (r * S.hc.R)

private theorem openingSlot_succ_le_of_lt (S : Setup V) {m n : Round} (h : m < n) :
    S.hc.opening_slot m + 1 ≤ S.hc.opening_slot n :=
  (Nat.le_of_lt (openingSlot_succ_lt_next S m)).trans
    (Nat.mul_le_mul_right S.hc.R h)

private theorem two_le_openingSlot (S : Setup V) {r : Round} (hr : 1 ≤ r) :
    2 ≤ S.hc.opening_slot r :=
  S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hr)

theorem action_succ_delta_le_action_of_lt
    (S : Setup V) {r q : Round} (hrq : r < q) :
    S.a r + 1 + S.E.Δ ≤ S.a q := by
  have hprop := action_add_delta_le_openingProposal_of_round_lt S hrq
  have hq := action_eq_proposalTime_add S q
  rw [hq]
  have h : ∀ x y d : Int, 0 < d → x + d ≤ y → x + 1 + d ≤ y + 6 * d := by
    intro x y d hd hxy
    omega
  exact h _ _ _ S.E.Δ_pos hprop

theorem action_succ_delta_le_voteTime_of_lt
    (S : Setup V) {r q : Round} (hrq : r < q) :
    S.a r + 1 + S.E.Δ ≤ Protocol.vote_time S.E (S.hc.opening_slot q) := by
  have hprop := action_add_delta_le_openingProposal_of_round_lt S hrq
  have hv := voteTime_eq_proposalTime_add S (S.hc.opening_slot q)
  rw [hv]
  have h : ∀ x y d : Int, 0 < d → x + d ≤ y → x + 1 + d ≤ y + d := by
    intro x y d hd hxy
    omega
  exact h _ _ _ S.E.Δ_pos hprop

theorem action_le_voteTime_of_lt
    (S : Setup V) {r q : Round} (hrq : r < q) :
    S.a r ≤ Protocol.vote_time S.E (S.hc.opening_slot q) := by
  have h := action_succ_delta_le_voteTime_of_lt S hrq
  have harith : ∀ x y d : Int, 0 < d → x + 1 + d ≤ y → x ≤ y := by
    intro x y d hd hxy
    omega
  exact harith _ _ _ S.E.Δ_pos h

theorem gstRound_succ_le_deadline
    (S : Setup V) (rho : Run V) (rGST gap : Round) :
    rGST + 1 ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
  unfold fgSafetyProgressDeadline
  exact Nat.le_add_right (rGST + 1) _

theorem eventualHeightProgressFrom_of_standing
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST) :
    EventualHeightProgressFrom S rho (rGST + 1) (progressLag' gap delayExtra) := by
  have hpost' : S.E.t_GST ≤ S.a (rGST + 1) :=
    hpost.trans (Assembly.a_mono S (Nat.le_succ rGST))
  exact eventualHeightProgressFrom_of_seed S adm hcom hbelow hrec
    (heightProgressSeedFrom_of_canonicity S adm hcom hbelow hdelay hrec hpost'
      (seedPredPromotionInputs_of_public S adm hcom hbelow hdelay hrec))
    hdelay hpost'
    (fixedRootProgress_of_rows S adm hcom hbelow hrec hdelay
      (fixedRoot_sourceHeight_le_nextOpeningParent S adm hcom hbelow))

#print axioms eventualHeightProgressFrom_of_standing

theorem honestHMaxAt_gt_after_twoProgress
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra ≤ r)
    (hhor : S.a r ≤ rho.horizon) :
    honestHMaxAt S rho (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) + 1 <
      honestHMaxAt S rho (S.a r) := by
  set D := fgSafetyProgressDeadline S rho rGST gap delayExtra with hD
  have hprog := eventualHeightProgressFrom_of_standing S adm hcom hbelow hrec
    hdelay hpost
  have hstart : rGST + 1 ≤ D := gstRound_succ_le_deadline S rho rGST gap
  have hwindowHor : S.a (D + 2 * progressLag' gap delayExtra) ≤ rho.horizon :=
    (Assembly.a_mono S hr).trans hhor
  have hgain : honestHMaxAt S rho (S.a D) + 2 ≤
      honestHMaxAt S rho (S.a (D + 2 * progressLag' gap delayExtra)) :=
    eventualHeightProgress_iterate S hprog hstart 2 hwindowHor
  show honestHMaxAt S rho (S.a D) + 1 + 1 ≤ honestHMaxAt S rho (S.a r)
  exact hgain.trans (honestHMaxAt_mono S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (Assembly.a_mono S hr))

theorem honestHMaxAt_le_localFrontier_after_oneDelay
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hsb : SlashableBound S rho)
    {t read : Time} (hpost : S.E.t_GST ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read) (hreadHor : read ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      honestHMaxAt S rho t ≤ (rho.storeBeforeTime S w read).h_max := by
  obtain ⟨holder, carrier, hcarrier⟩ :=
    honestHMaxCarrierAt_of_eq S adm hcom (t := t) (H := honestHMaxAt S rho t) rfl
  exact hcarrier.localFrontier_ge_after_oneDelay S adm hsb hpost hdelay hreadHor

theorem frontierSeed_of_progress
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r0 : Round}
    (hr0 : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra ≤ r0)
    {read : Time}
    (hrelay : S.a r0 + 1 + S.E.Δ ≤ read) (hreadHor : read ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      honestHMaxAt S rho (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) + 1 <
        (rho.storeBeforeTime S w read).h_max := by
  intro w hw
  have hd := S.E.Δ_pos
  have hr0Hor : S.a r0 ≤ rho.horizon := by
    have harith : ∀ x y d : Int, 0 < d → x + 1 + d ≤ y → x ≤ y := by
      intro x y d hd hxy
      omega
    exact harith _ _ _ S.E.Δ_pos (hrelay.trans hreadHor)
  have hgain := honestHMaxAt_gt_after_twoProgress S adm hcom hbelow hrec hdelay
    hpost hr0 hr0Hor
  have hr0Round : rGST ≤ r0 :=
    (Nat.le_succ rGST).trans
      ((gstRound_succ_le_deadline S rho rGST gap).trans
        ((Nat.le_add_right _ (2 * progressLag' gap delayExtra)).trans hr0))
  have hr0Post : S.E.t_GST ≤ S.a r0 := hpost.trans (Assembly.a_mono S hr0Round)
  have hlocal := honestHMaxAt_le_localFrontier_after_oneDelay S adm hcom
    (slashableBound_of_admissible_belowOneThird S adm hbelow)
    hr0Post hrelay hreadHor w hw
  exact hgain.trans_le hlocal

theorem heightOld_assemble
    {x H hmax hT hP : Height}
    (hgain : x + 2 ≤ H) (hlocal : H ≤ hmax)
    (hband : hmax - 1 ≤ hT) (hTP : hT ≤ hP) :
    x < hP := by
  have h1 : x + 1 + 1 ≤ hmax := hgain.trans hlocal
  have h2 : x + 1 ≤ hmax - 1 := Nat.le_sub_of_add_le h1
  exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le (h2.trans hband)) hTP





structure HandoverHeights (S : Setup V) (rho : Run V)
    (base fresh : Round) (start : Slot) (P : NamedBlock V) : Prop where
  heightOld : honestHMaxAt S rho (S.a (fresh - 1)) <
    (Protocol.derive_named S.E S.cfg P).h
  frontierSeed : ∀ w ∈ rho.honest,
    honestHMaxAt S rho (S.a (fresh - 1)) + 1 <
      (rho.storeBeforeTime S w
        (min (S.a (base + S.hc.η_SG)) (Protocol.vote_time S.E start))).h_max

private theorem namedPreceq_of_runBlocks
    {S : Setup V} {rho : Run V} (roots : NamedRootCollisionFree S rho)
    {A B : NamedBlock V} (hArun : RunBlock S rho A)
    (hBrun : RunBlock S rho B) (hAB : Block.Preceq A.erase B.erase) :
    NamedBlock.Preceq A B := by
  obtain ⟨A', hA'B, hA'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hAB
  have hA'run : RunBlock S rho A' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hA'B
  have hroot : A.root = A'.root := by
    calc
      A.root = A.erase.root := (Proofs.NamedWire.erase_root A).symm
      _ = A'.erase.root := congrArg Block.root hA'erase.symm
      _ = A'.root := Proofs.NamedWire.erase_root A'
  have hEq : A = A' :=
    roots.root_injective A A' hArun hA'run A A'
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self A')) hroot
  rw [hEq]
  exact hA'B




/-- Direct named handover heights at an arbitrary honest carrier. The two
concurrent producers are stated with their pinned types. -/
theorem handoverHeights_of_carrier_named_of_pins
    (_of_frontier : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → BelowOneThird S rho.honest →
      ∀ {rGST gap : Round}, MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
      ∀ {read : Time},
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read →
      read ≤ rho.horizon → ∀ {s : Slot},
      S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s →
      read ≤ Protocol.confirmation_time S.E s →
      Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon →
      ∀ {u : V}, u ∈ rho.honest →
      ∃ T : NamedBlock V,
        RunBlock S rho T ∧
        (rho.storeBeforeTime S u read).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg T).h ∧
        ∀ w ∈ rho.honest, T.erase ⪯ voterHeadAt S rho w s)
    (_of_heads : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → BelowOneThird S rho.honest →
      ∀ {rGST gap : Round}, MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
      ∀ {m : Round},
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m →
      Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon →
      ProposerCarrierAt S rho m → ∀ {P : NamedBlock V},
      proposedBlockAt S rho (S.hc.opening_slot m) = some P →
      ∀ v ∈ rho.honest,
        voterHeadAt S rho v (S.hc.opening_slot m) = P.erase)
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {base m : Round}
    (hbaseLo : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra + 1 ≤ base)
    (hcutm : base + S.hc.η_SG ≤ m)
    (hcarrier : ProposerCarrierAt S rho m)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    HandoverHeights S rho base
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1)
      (S.hc.opening_slot m) P := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let L := progressLag' gap delayExtra
  let r0 : Round := D + 2 * L
  let cut : Round := base + S.hc.η_SG
  let start : Slot := S.hc.opening_slot m
  have hr0cut : r0 < cut :=
    Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self r0)
        (by simpa only [D, L, r0] using hbaseLo))
      (by simpa only [cut] using Nat.le_add_right base S.hc.η_SG)
  have hr0m : r0 < m := hr0cut.trans_le (by simpa only [cut] using hcutm)
  have hDr0 : D ≤ r0 := by
    simpa only [r0] using Nat.le_add_right D (2 * L)
  have hDm : D < m := Nat.lt_of_le_of_lt hDr0 hr0m
  have hDtwoM : D + 2 < m := by
    have hLpos : 1 ≤ L := by simpa only [L] using progressLag'_pos gap
    have h2L : 2 ≤ 2 * L := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hLpos
    exact Nat.lt_of_le_of_lt (by
      simpa only [r0] using Nat.add_le_add_left h2L D) hr0m
  have hmPos : 1 ≤ m :=
    Nat.lt_of_le_of_lt (Nat.zero_le (D + 2)) hDtwoM
  have hstartPos : 1 ≤ start := by
    simpa only [start] using
      (show 1 ≤ S.hc.opening_slot m from
        (by decide : (1 : Nat) ≤ 2).trans (two_le_openingSlot S hmPos))
  have hhorVote : Protocol.vote_time S.E start ≤ rho.horizon :=
    (voteTime_le_confirmationTime S start).trans
      (by simpa only [start] using hhor)
  have hhorVoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon :=
    (voteTime_add_delta_le_confirmationTime S start).trans
      (by simpa only [start] using hhor)
  let read : Time := min (S.a cut) (Protocol.vote_time S.E start)
  have hreadVote : read ≤ Protocol.vote_time S.E start := min_le_right _ _
  have hreadHor : read ≤ rho.horizon := hreadVote.trans hhorVote
  have hrelay : S.a r0 + 1 + S.E.Δ ≤ read :=
    le_min (action_succ_delta_le_action_of_lt S hr0cut)
      (action_succ_delta_le_voteTime_of_lt S hr0m)
  have hreadLo : S.a D ≤ read :=
    le_min (Assembly.a_mono S (hDr0.trans (Nat.le_of_lt hr0cut)))
      (action_le_voteTime_of_lt S hDm)
  have hreadConf : read ≤ Protocol.confirmation_time S.E start :=
    hreadVote.trans (voteTime_le_confirmationTime S start)
  obtain ⟨u, hu⟩ := honest_nonempty_of_honestCommittees hcom
  obtain ⟨T, hTrun, hbandT, hheadsT⟩ :=
    _of_frontier S adm hcom hbelow hrec hdelay hpost hreadLo hreadHor
      (s := start) (by
        simpa only [D, start] using openingSlot_succ_le_of_lt S hDm)
      hreadConf hhorVoteDelta hu
  have hhead : voterHeadAt S rho u start = P.erase :=
    _of_heads S adm hcom hbelow hrec hdelay hpost
      (by simpa only [D] using Nat.le_of_lt hDtwoM) hhorVote hcarrier
      (by simpa only [start] using hP) u hu
  have hTP : Block.Preceq T.erase P.erase := by
    have h := hheadsT u hu
    rwa [hhead] at h
  have hhorProp : Protocol.proposal_time S.E start ≤ rho.horizon :=
    (le_of_lt (proposal_time_lt_vote_time S.E start)).trans hhorVote
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      start hstartPos (by simpa only [start] using hcarrier.1) hhorProp
      (by simpa only [start] using hP)
  have hTPNamed : NamedBlock.Preceq T P :=
    namedPreceq_of_runBlocks adm.toNamedRootCollisionFree hTrun hPrun hTP
  have hTheight : (Protocol.derive_named S.E S.cfg T).h ≤
      (Protocol.derive_named S.E S.cfg P).h :=
    Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTPNamed
  have hr0Hor : S.a r0 ≤ rho.horizon := by
    have harith : ∀ x y d : Int, 0 < d → x + 1 + d ≤ y → x ≤ y := by
      intro x y d hd hxy
      omega
    exact harith _ _ _ S.E.Δ_pos (hrelay.trans hreadHor)
  have hgain : honestHMaxAt S rho (S.a D) + 2 ≤
      honestHMaxAt S rho (S.a r0) := by
    have h := honestHMaxAt_gt_after_twoProgress S adm hcom hbelow hrec
      hdelay hpost (r := r0) (show D + 2 * L ≤ r0 by rfl) hr0Hor
    simpa only [Nat.add_assoc] using h
  have hr0Post : S.E.t_GST ≤ S.a r0 :=
    hpost.trans (Assembly.a_mono S
      ((Nat.le_succ rGST).trans
        ((gstRound_succ_le_deadline S rho rGST gap).trans
          (by simpa only [D] using hDr0))))
  have hlocal := honestHMaxAt_le_localFrontier_after_oneDelay S adm hcom
    (slashableBound_of_admissible_belowOneThird S adm hbelow)
    hr0Post hrelay hreadHor u hu
  have hfresh : D + 1 - 1 = D := Nat.add_sub_cancel _ _
  refine { heightOld := ?_, frontierSeed := ?_ }
  · rw [show fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 - 1 = D by
      simpa only [D] using hfresh]
    exact heightOld_assemble hgain hlocal hbandT hTheight
  · rw [show fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 - 1 = D by
      simpa only [D] using hfresh]
    exact frontierSeed_of_progress S adm hcom hbelow hrec hdelay hpost
      (r0 := r0) (show D + 2 * L ≤ r0 by rfl) hrelay hreadHor

#print axioms handoverHeights_of_carrier_named_of_pins




end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
