module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedFrontier
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeiling
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The first round ceiling from the healing entry property

`roundCeiling_base_of_carrierFrontier` starts the half-open ceiling induction
from three things: a run block above every honest round-`q` action carrier, a
viability witness for it, and the round's last honest votes above it. The
first two are `exists_seedActionFrontier`. The third is the healing entry
property, named here as `SeedBoundaryAdoptionAt`: at the last vote duty of the
round every honest Goldfish head reaches the local viability boundary and is
above every carrier bound of the round.

That is the only remaining protocol input of the gate-off seed. Everything
downstream — the ceiling, its re-basing successor, the opening lifecycle and
the promotion — is regime-only from there.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! The active declarations below use the named ceiling interface. The
earlier source is retained above byte-exactly. -/

/-- **The healing entry property at the boundary of round `q`.**

`headThin` is the local viability floor of the round's last honest votes.
`entry` is the adoption itself: one run block sits above every honest round-`q`
SG action carrier and below every honest Goldfish head of the round's last vote
duty, and it reaches the viability boundary through a witness.

The block is EXISTENTIAL on purpose. The deepest carrier bound
(`exists_seedActionFrontier`) is the witness whenever the round's anchors are
ordered against the round's confirmations, and `seedBoundaryAdoption_of_arms`
builds the record that way. It is NOT the witness in general: an honest fresh
anchor may conflict with another honest reader's genuine confirmation
(`deepest_clear_none_of_conflicting_fresh_anchor` is that case in the model),
and then the anchor holder's own head conflicts with that confirmation, so no
recorded confirmation can be the entry block. The divergence point of the two
branches is, and it is not a carrier bound. -/
structure SeedBoundaryAdoptionAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round) : Prop where
  headThin : ∀ X : NamedBlock V,
    NamedHonestHead S rho (S.hc.opening_slot (q + 1) - 1) X →
      M - 1 ≤ (derive_named S.E S.cfg X).h
  entry : ∃ C : NamedBlock V, RunBlock S rho C ∧
    (∃ W : NamedBlock V, RunBlock S rho W ∧
      Block.Preceq C.erase W.erase ∧
        M - 1 ≤ (derive_named S.E S.cfg W).h) ∧
    (∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) C.erase) ∧
    (∀ X : NamedBlock V,
      NamedHonestHead S rho (S.hc.opening_slot (q + 1) - 1) X →
        Block.Preceq C.erase X.erase)

/-- A block below every honest head of the round's last vote duty has the
boundary cone of a first ceiling. -/
theorem seedBoundaryCone_of_belowHeads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {C : Block V}
    (hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon)
    (hbelow : ∀ X : NamedBlock V,
      NamedHonestHead S rho (S.hc.opening_slot (q + 1) - 1) X →
        Block.Preceq C X.erase) :
    NamedHonestVotesCone S rho (S.hc.opening_slot (q + 1) - 1)
      (fun X => Block.Preceq C X) := by
  intro w hw hwcommittee
  have hs : 0 < S.hc.opening_slot (q + 1) - 1 := by
    unfold Protocol.HealConfig.opening_slot
    have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
    have hmul : 2 ≤ (q + 1) * S.hc.R := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le q)) hR
    exact Nat.sub_pos_iff_lt.mpr ((by decide : 1 < 2).trans_le hmul)
  obtain ⟨H, hHerase, hHrun⟩ := seedVoteDutyHead_runBlock S adm hw
    (S.hc.opening_slot (q + 1) - 1)
  have hHemit := seedVoteDutyHead_emits S adm hw hs hwcommittee hvoteHor
  have hHemit' : NamedRun.emits S rho w
      (.gfVote ⟨w, S.hc.opening_slot (q + 1) - 1, H.erase.root⟩)
      (Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1)) := by
    simpa only [hHerase] using hHemit
  have hHhead : NamedHonestHead S rho
      (S.hc.opening_slot (q + 1) - 1) H := by
    exact ⟨w, hw, hwcommittee, hHrun, hHemit'⟩
  exact ⟨H, hbelow H hHhead, hHrun, hHemit'⟩

/-- **The first round ceiling of the gate-off seed.** The healing entry
property and the next-round regime are the whole input; the re-basing base
constructor absorbs any certificate revealed inside round `q + 1`. -/
theorem exists_roundCeiling_of_seedBoundaryAdoption
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hpostAction : S.E.t_GST ≤ S.a q)
    (hpostBoundaryVote : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1))
    (hboundaryConfirmationInHorizon :
      Protocol.confirmation_time S.E
        (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon)
    (hadoption : SeedBoundaryAdoptionAt S rho M q)
    (hreg : RoundCeilingNextRegimeAt S rho M q) :
    ∃ B : NamedBlock V, RoundCeilingAt S rho M (q + 1) B := by
  obtain ⟨C, hCrun, ⟨W, hWrun, hCW, hWthin⟩, hcarriers, hbelow⟩ :=
    hadoption.entry
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans
      hboundaryConfirmationInHorizon
  obtain ⟨B, hB, _⟩ := roundCeiling_base_of_carrierFrontier S adm hcom hfb
    hpostAction hpostBoundaryVote hboundaryConfirmationInHorizon hCrun hWrun
    hCW hWthin hcarriers
    (seedBoundaryCone_of_belowHeads S adm hvoteHor hbelow)
    hadoption.headThin hreg
  exact ⟨B, hB⟩

/-- Confirmation reads are monotone in the slot. -/
private theorem seedConfirmationTime_mono
    (E : Env V) {s t : Slot} (hst : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right hst 1)

/-- The action read of a round is its opening confirmation read. -/
private theorem seedAction_eq_openingConfirmation
    (S : Setup V) (q : Round) :
    S.a q = Protocol.confirmation_time S.E (S.hc.opening_slot q) := by
  rw [Setup.a, Protocol.a_eq_confirmation_time]

/-- Round-slot arithmetic with bare `Nat` binders. -/
private theorem seedRoundSlot_nat {a b : Nat} (hb : 2 ≤ b) :
    a ≤ a + b - 1 ∧ a + b - 1 ≤ a + b ∧ a + b - 1 - 1 ≤ a + b := by
  omega


/-- Everything the round-ceiling machinery reads at round `q`. -/
structure SeedRoundRegimeAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round) : Prop where
  postAction : S.E.t_GST ≤ S.a q
  postOpeningProposal : S.E.t_GST ≤
    Protocol.proposal_time S.E (S.hc.opening_slot q)
  postBoundaryVote : S.E.t_GST ≤
    Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1)
  openingConfirmationInHorizon :
    Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon
  boundaryConfirmationInHorizon :
    Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon
  frontier : ∀ v ∈ rho.honest,
    (rho.storeBeforeTime S v (S.a q)).h_max = M
  gate : ∀ v ∈ rho.honest,
    (rho.storeBeforeTime S v (S.a q)).h_j + 2 ≤ M
  ready : Internal.HealingSurface.GradeRoundReady S rho q
  settled : SelectedG2SettledAt S rho q
  next : RoundCeilingNextRegimeAt S rho M q

/-- **The round regime from the raw gate-off window.** A post-GST base round
whose window of honest strict reads is gate off at the exact frontier `M`
through the action read of round `q + 2` supplies every regime input of round
`q`. -/
theorem seedRoundRegime_of_window
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {base q : Round}
    (hpostBase : gstLagged S ≤ S.a base)
    (hbaseq : base + 1 ≤ q)
    (hhor : S.a (q + 2) ≤ rho.horizon)
    (hwindow : ∀ read : Time, S.a base ≤ read → read ≤ S.a (q + 2) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M) :
    SeedRoundRegimeAt S rho M q := by
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (Nat.succ_pos base) hbaseq
  have hqPredAdd : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos)
  have hbasePred : base ≤ q - 1 := Nat.le_sub_one_of_lt hbaseq
  have hpostPredLagged : gstLagged S ≤ S.a (q - 1) :=
    hpostBase.trans (Assembly.a_mono S hbasePred)
  have hpostActionLagged : gstLagged S ≤ S.a q :=
    hpostBase.trans (Assembly.a_mono S ((Nat.le_succ base).trans hbaseq))
  have hpostPred : S.E.t_GST ≤ S.a (q - 1) :=
    (t_GST_le_gstLagged S).trans hpostPredLagged
  have hpostAction : S.E.t_GST ≤ S.a q :=
    (t_GST_le_gstLagged S).trans hpostActionLagged
  have hsucc : S.hc.opening_slot (q + 1) =
      S.hc.opening_slot q + S.hc.R := opening_slot_succ_eq S.hc q
  obtain ⟨hboundaryLo, hboundaryHi, hboundaryHi2⟩ :=
    seedRoundSlot_nat (a := S.hc.opening_slot q) (b := S.hc.R) hR
  have hopenBoundary : S.hc.opening_slot q ≤
      S.hc.opening_slot (q + 1) - 1 := by
    rw [hsucc]
    exact hboundaryLo
  have hpostProposal : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q) := by
    refine hpostPred.trans ?_
    refine (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans ?_
    exact action_add_delta_le_openingProposal_of_round_lt S
      (by simpa only [hqPredAdd] using Nat.sub_lt hqpos Nat.zero_lt_one)
  have hpostBoundaryVote : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (q + 1) - 1) := by
    refine hpostProposal.trans ?_
    refine (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _)).trans ?_
    exact Protocol.vote_time_mono_slots S.E hopenBoundary
  have hactionHor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right q 2)).trans hhor
  have hopeningHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon := by
    rw [← seedAction_eq_openingConfirmation S q]
    exact hactionHor
  have hnextActionHor : S.a (q + 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.add_le_add_left (by decide : 1 ≤ 2) q)).trans hhor
  have hboundaryHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon := by
    refine (seedConfirmationTime_mono S.E (Nat.sub_le _ 1)).trans ?_
    rw [← seedAction_eq_openingConfirmation S (q + 1)]
    exact hnextActionHor
  have hfrontier : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a q)).h_max = M := fun v hv =>
    (hwindow (S.a q)
      (Assembly.a_mono S ((Nat.le_succ base).trans hbaseq))
      (Assembly.a_mono S (Nat.le_add_right q 2)) v hv).2
  have hgate : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a q)).h_j + 2 ≤ M := fun v hv =>
    (hwindow (S.a q)
      (Assembly.a_mono S ((Nat.le_succ base).trans hbaseq))
      (Assembly.a_mono S (Nat.le_add_right q 2)) v hv).1
  have hprevFrontier : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a (q - 1))).h_max = M := fun v hv =>
    (hwindow (S.a (q - 1)) (Assembly.a_mono S hbasePred)
      (Assembly.a_mono S ((Nat.sub_le q 1).trans (Nat.le_add_right q 2)))
      v hv).2
  have hready : Internal.HealingSurface.GradeRoundReady S rho q := by
    refine gradeRoundReady_of_action_horizon S ?_ (le_refl q) hactionHor
    have h := gstLagged_le_Γ_neg1_succ S (q - 1) hpostPredLagged
    rwa [hqPredAdd] at h
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S q .g2).trans hactionHor
  have hrel := relativeCarrierWindowAt_of_gateOff S adm hfb hqpos hpostPred
    hprevFrontier hfrontier hgate hdomainHor
  have hmajority := gradeFormingMajority_of_admissible_belowOneThird S adm hfb
    hqpos hdomainHor
  have hsettled : SelectedG2SettledAt S rho q :=
    selectedG2SettledAt_of_gateOff S adm hfb hqpos hrel hmajority hpostPred
      hprevFrontier hfrontier hgate hactionHor
  have hlastHor : Protocol.confirmation_time S.E
      (seedRoundLastSlot S (q + 1) - 1) ≤ rho.horizon := by
    have hslot : seedRoundLastSlot S (q + 1) - 1 ≤
        S.hc.opening_slot (q + 2) := by
      unfold seedRoundLastSlot
      have h : q + 1 + 1 = q + 2 := rfl
      rw [h]
      exact (Nat.sub_le _ 1).trans (Nat.sub_le _ 1)
    refine (seedConfirmationTime_mono S.E hslot).trans ?_
    rw [← seedAction_eq_openingConfirmation S (q + 2)]
    exact hhor
  have hnext : RoundCeilingNextRegimeAt S rho M q := by
    refine roundCeilingNextRegime_of_window S adm hfb hpostAction hlastHor ?_
    intro read hlo hhi w hw
    refine hwindow read
      ((Assembly.a_mono S ((Nat.le_succ base).trans hbaseq)).trans hlo) ?_ w hw
    refine hhi.trans ?_
    rw [seedAction_eq_openingConfirmation S (q + 2)]
    refine seedConfirmationTime_mono S.E ?_
    unfold seedRoundLastSlot
    have h : q + 1 + 1 = q + 2 := rfl
    rw [h]
    exact (Nat.sub_le _ 1).trans (Nat.sub_le _ 1)
  exact
    { postAction := hpostAction
      postOpeningProposal := hpostProposal
      postBoundaryVote := hpostBoundaryVote
      openingConfirmationInHorizon := hopeningHor
      boundaryConfirmationInHorizon := hboundaryHor
      frontier := hfrontier
      gate := hgate
      ready := hready
      settled := hsettled
      next := hnext }

/-- **The first ceiling from the raw gate-off window.** This is the complete
gate-off seed base: the healing entry property at the round's boundary is the
only protocol input. -/
theorem exists_roundCeiling_of_window_of_adoption
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {base q : Round}
    (hpostBase : gstLagged S ≤ S.a base)
    (hbaseq : base + 1 ≤ q)
    (hhor : S.a (q + 2) ≤ rho.horizon)
    (hwindow : ∀ read : Time, S.a base ≤ read → read ≤ S.a (q + 2) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M)
    (hadoption : SeedBoundaryAdoptionAt S rho M q) :
    ∃ B : NamedBlock V, RoundCeilingAt S rho M (q + 1) B := by
  have hregime := seedRoundRegime_of_window S adm hfb hpostBase hbaseq hhor
    hwindow
  exact exists_roundCeiling_of_seedBoundaryAdoption S adm hcom hfb
    hregime.postAction hregime.postBoundaryVote
    hregime.boundaryConfirmationInHorizon hadoption hregime.next

/-- The ceiling carries through the gate-off window to every later round. -/
theorem roundCeiling_through_of_window
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {base first last : Round} {C : NamedBlock V}
    (hpostBase : gstLagged S ≤ S.a base)
    (hbaseFirst : base + 1 ≤ first)
    (hhor : S.a (last + 2) ≤ rho.horizon)
    (hwindow : ∀ read : Time, S.a base ≤ read → read ≤ S.a (last + 2) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M)
    (hbase : RoundCeilingAt S rho M first C) :
    ∀ k : Round, first ≤ k → k ≤ last →
      ∃ B : NamedBlock V, RoundCeilingAt S rho M k B ∧
        Block.Preceq C.erase B.erase := by
  intro k hfirstk hklast
  exact roundCeiling_through_or_rebase S adm hcom hfb hbase
    (fun j hjlo hjhi => (seedRoundRegime_of_window S adm hfb hpostBase
      (hbaseFirst.trans hjlo)
      ((Assembly.a_mono S
        (Nat.add_le_add_right (Nat.le_of_lt hjhi) 2)).trans hhor)
      (fun read hlo hhi w hw => hwindow read hlo
        (hhi.trans (Assembly.a_mono S
          (Nat.add_le_add_right (Nat.le_of_lt hjhi) 2))) w hw)).next)
    k hfirstk hklast






end HealingSurface
end Proofs
end DecoupledConsensusModel

end

