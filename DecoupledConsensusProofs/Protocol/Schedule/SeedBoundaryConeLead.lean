module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedAssembly
public import DecoupledConsensusProofs.Protocol.Schedule.SeedEntry
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedNextActionExact
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedBandGrade
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedOpeningWindow
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedActivity
public import DecoupledConsensusProofs.Objects.SGTargetCompatibility
public import DecoupledConsensusProofs.Protocol.Grades.Ladder
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalCanonicality
public import DecoupledConsensusProofs.Protocol.Grades.SeedBaseCeiling
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Store.RecoveryG1AfterCutoffPersistence
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryG1AfterCutoffReflection
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Objects.BlockVisibilityCore
public import DecoupledConsensusProofs.Protocol.Schedule.AdoptionTransport
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.VoteDutyHeadBand
public import DecoupledConsensusProofs.Execution.SeedBaseCone
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainSupporter
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBase
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Execution.RecoveryActionLiveSourceSplit
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroHeadResolution
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


/-!
# The boundary cone at a carrier round (lead's construction)

`SeedAssemblyRun` states the one fact the round-ceiling induction cannot get
from the fixed-frontier gate-off frame: that the last honest Goldfish votes of a
round extend the thin block above the round's deepest SG carrier. This module
builds that fact from Claim 1 (every honest vote of the slot after the opening
supports every honest SG target of the round) and the seed's own one-slot cone
persistence, so that `roundCeiling_base_of_carrierFrontier` can start the
induction and the band cover follows at the second carrier of a consecutive
carrier pair.

Section 1 is the persistence step: a cone above a block `C` at slot `s`,
together with a thin honest head above `C` at `s`, the gate-off frame at the
next vote duties, and the anchors' compatibility with `C`, gives the same two
facts at `s + 1`.
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

private theorem namedSucc_le_add_sub_one {x a : Nat} (h : 2 ≤ a) :
    x + 1 ≤ x + a - 1 := by omega

/-- Every honest read in the interval has the gate off and exact frontier. -/
def NamedGateOffFrameAt (S : Setup V) (rho : Run V) (M : Height)
    (lo hi : Round) : Prop :=
  ∀ read : Time, S.a lo ≤ read → read ≤ S.a hi →
    ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w read).core.h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w read).core.h_max = M

private theorem namedOpeningSucc_le_boundary (S : Setup V) (c : Round) :
    S.hc.opening_slot c + 1 ≤ S.hc.opening_slot (c + 1) - 1 := by
  have hsucc : S.hc.opening_slot (c + 1) =
      S.hc.opening_slot c + S.hc.R := by
    simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
  rw [hsucc]
  exact namedSucc_le_add_sub_one S.hc.R_ge_two

private theorem namedNat_pred_pred_lt {x y : Nat} (h : x + 1 ≤ y - 1) :
    y - 1 - 1 < y := by omega

private theorem namedConfirmationTime_mono
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right hab 1)


/-- The next-round regime records from a named gate-off frame. -/
theorem regime_of_gateOffFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round}
    (hpostAction : S.E.t_GST ≤ S.a c)
    (hhor : S.a (c + 2) ≤ rho.horizon)
    (hframe : NamedGateOffFrameAt S rho M c (c + 2)) :
    RoundCeilingNextRegimeAt S rho M c := by
  have hlastLe : Protocol.confirmation_time S.E
      (seedRoundLastSlot S (c + 1) - 1) ≤ S.a (c + 2) := by
    have hlt : seedRoundLastSlot S (c + 1) - 1 <
        S.hc.opening_slot (c + 2) := by
      unfold seedRoundLastSlot
      exact namedNat_pred_pred_lt
        (namedOpeningSucc_le_boundary S (c + 1))
    have hmono := namedConfirmationTime_mono S.E (le_of_lt hlt)
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hmono
  refine roundCeilingNextRegime_of_window S adm hfb hpostAction
    (hlastLe.trans hhor) ?_
  intro read hlo hhi w hw
  simpa only [Run.storeBeforeTime] using
    hframe read hlo (hhi.trans hlastLe) w hw

/-- Every honest head of a slot is the erasure of that voter's named cone vote. -/
theorem honestHead_preceq_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {d : Slot} {C : Block V}
    (hcone : NamedHonestVotesCone S rho d (fun X => Block.Preceq C X)) :
    ∀ X : Block V, HonestHead S rho d X → Block.Preceq C X := by
  intro X hX
  obtain ⟨x, hxHonest, hxCommittee, ⟨Xn, hXerase, hXrun⟩, hXemit⟩ := hX
  obtain ⟨Y, hCY, hYrun, hYemit⟩ := hcone x hxHonest hxCommittee
  have hvote : (⟨x, d, X.root⟩ : GoldfishVote V) =
      ⟨x, d, Y.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hXemit hYemit rfl
  have hXY : Xn.erase = Y.erase :=
    Protocol.runBlock_eq_of_root_eq
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree hXrun hYrun
      (by simpa only [hXerase] using congrArg GoldfishVote.head hvote)
  rw [← hXerase, hXY]
  exact hCY


#print axioms regime_of_gateOffFrame

/-! ## 1. One-slot persistence of a cone with a thin head -/






/-! ## 2. From the base cone at the slot after the opening to a round ceiling -/









/-! ## 3. Discharging the per-duty binders from the seed's gate-off frame -/





/-- Every honest head of a slot is the emitter's own vote-duty head, so the
band reach of the vote-duty heads gives the thinness of every honest head.

design note (statement change, ledger row): heads are named bodies, so the
conclusion quantifies over `NamedHonestHead` and reads
`Protocol.derive_named`, and the band premise carries the retained named
witness of the vote head alongside its height — exactly what
`SeedViabilityRun.voteDutyHead_height_ge_frontier_sub_one_of_candidate`
concludes. earlier text, byte-exact:

    theorem headThin_of_band
        (S: Setup V) {rho: Run V} (adm: Admissible S rho)
        {M: Height} {d: Slot} (hd: 0 < d)
        (hhor: Protocol.vote_time S.E d ≤ rho.horizon)
        (hfrontier: ∀ w ∈ rho.honest, (voteDutyStore S rho w d).h_max = M)
        (hband: ∀ w ∈ rho.honest,
          (voteDutyStore S rho w d).h_max - 1 ≤
            (derived_state S.E S.cfg (voteDutyHead S rho w d)).h):
        ∀ X: Block V, HonestHead S rho d X →
          M - 1 ≤ (derived_state S.E S.cfg X).h -/
theorem headThin_of_band
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {d : Slot} (hd : 0 < d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hfrontier : ∀ w ∈ rho.honest, (voteDutyStore S rho w d).h_max = M)
    (hband : ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w d).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg Hn).h) :
    ∀ X : NamedBlock V, NamedHonestHead S rho d X →
      M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h := by
  intro X hX
  obtain ⟨x, hxHonest, hxCommittee, hXrun, hXemit⟩ := hX
  have hemit := seedVoteDutyHead_emits S adm hxHonest hd hxCommittee hhor
  have hrootEq : X.erase.root = (voterHeadAt S rho x d).root :=
    congrArg GoldfishVote.head
      (emits_gfVote_unique S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hXemit hemit rfl)
  obtain ⟨H, hHerase, hHrun, hfloor⟩ := hband x hxHonest
  have hrootNamed : X.root = H.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root H, hHerase]
    exact hrootEq
  have hXH : X = H :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      X H hXrun hHrun X H (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hrootNamed
  rw [hXH]
  simpa only [hfrontier x hxHonest] using hfloor



#print axioms headThin_of_band


/-! ## 4. The cover at the second carrier, from the round ceiling -/






/-- Two honest SG targets both below one honest Goldfish vote head are
compatible, so Claim 1 at one slot puts every honest carrier of the round on
one chain.: the cone is the named cone. -/
theorem honestActionCarriersOneChainAt_of_secondSlotCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) {c : Round}
    (hclaim1 : ∀ v ∈ rho.honest,
      NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
        (fun X => Block.Preceq (actionSGBlockAt S rho v c) X)) :
    HonestActionCarriersOneChainAt S rho c := by
  intro u hu v hv
  have hpositive :
      0 < ((S.E.committee (S.hc.opening_slot c + 1)) ∩ rho.honest).card := by
    have hc := hcom (S.hc.opening_slot c + 1)
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee (S.hc.opening_slot c + 1) :=
    (Finset.mem_inter.mp hw).1
  have hwHonest : w ∈ rho.honest := (Finset.mem_inter.mp hw).2
  obtain ⟨X, hXu, hXrun, hXemit⟩ := hclaim1 u hu w hwHonest hwCommittee
  obtain ⟨Y, hYv, hYrun, hYemit⟩ := hclaim1 v hv w hwHonest hwCommittee
  have hXY : X.erase = Y.erase :=
    Protocol.runBlock_eq_of_root_eq
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree hXrun hYrun
      (congrArg GoldfishVote.head
        (emits_gfVote_unique S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hXemit hYemit rfl))
  rw [hXY] at hXu
  exact compatible_of_common_honest_goldfish_head hXu hYv





#print axioms honestActionCarriersOneChainAt_of_secondSlotCone






















/-! ## 8. The boundary cone, the ceiling, the adoption and the cover from the
common root -/








/-! ## 7. Claim 1 at the second slot, from the common root

Every honest Goldfish vote of the slot after round `c`'s opening extends every
honest round-`c` SG target. The target is one of three: the common root
itself (every vote descends from its FG root), a clear block below a genuine
confirmation (tier 1: `baseCone_succ_of_genuineSupporter`), or the selected
grade-2 block (tier 2: it is grade 1 at every honest duty store, so below
every fresh anchor, so below every vote head). The raw-anchor tier is
unreachable: with one FG root the root is grade 2 everywhere. -/






/-! ## 8. The band cover at a carrier round from its opening adoption -/


/-- The band cover at a carrier round from its opening adoption: the honest
opening proposal sits on a parent at the band and is below every honest action
carrier of the round. -/
theorem seedBandCarrierCover_of_adoption_window
    (S : Setup V) {rho : Run V} {M : Height} {q : Round}
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hband : M - 1 ≤ (Protocol.derive_named S.E S.cfg P).h)
    (hadoption : GateOffOpeningAdoption S rho q) :
    SeedBandCarrierCoverAt S rho M q :=
  ⟨P, (hadoption.lifecycle P hP).runBlock, hband, hadoption.actionCover P hP⟩

#print axioms seedBandCarrierCover_of_adoption_window





#print axioms honestHead_preceq_of_cone

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
