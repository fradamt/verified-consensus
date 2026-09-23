module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Grades.LifecycleActionSource
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressLadder
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightActiveEliminator
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootClaimFourOuter
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierFirst
public import DecoupledConsensusProofs.Protocol.Grades.EventualHeightProgressAssembler
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



/-!
# Numeric height-progress composition

This module composes the closed fixed-root height ladder. The only remaining
protocol leaf is the named gate-off seed hypothesis `HeightProgressSeedFrom`.
The public result uses only the numeric arm of
`BoundedHeightGradeOrProgressFrom`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- The gate-off seed's own round budget, now exact rather than provisional.
The run reads three carrier rounds, and the `M - 1` opening case reads two
more: `base + 4` to the first carrier, `gap` to each of the four later ones,
and the fixed spacing between them. The deepest round the seed reads is
`base + 4 * gap + 12 + 2 * delayExtra`. At zero extra rounds, this is
the existing seed budget. -/
def seedLag (gap : Round) (delayExtra : Nat := 0) : Round :=
  4 * gap + 12 + 2 * delayExtra

/-- The numeric height-progress lag includes the relay round before the seed
and the two Claim-4 lifecycle selections after it. Each extra timeout round
adds two rounds to the seed and two rounds to the later selections. -/
def progressLag' (gap : Round) (delayExtra : Nat := 0) : Round :=
  seedLag gap delayExtra + 3 * gap + 10 + 2 * delayExtra





theorem progressLag'_pos (gap : Round) : 0 < progressLag' gap delayExtra := by
  simp [progressLag', seedLag]

private theorem lowPrelude_nat {start gap endpoint : Nat}
    (h : start + 3 + delayExtra + gap ≤ endpoint) :
    start + 2 ≤ endpoint ∧ start ≤ start + 1 ∧ start ≤ start + 2 := by
  omega

private theorem lowSelected_nat {start q : Nat}
    (h : start + 3 + delayExtra ≤ q) :
    0 < q ∧ start + 2 ≤ q ∧ start + 2 ≤ q - 1 ∧ start ≤ q - 1 := by
  omega

private theorem lowSelected_delay_nat {start q delayExtra : Nat}
    (h : start + 3 + delayExtra ≤ q) : 2 + delayExtra ≤ q := by omega







private theorem composeStaticBounds_nat (start gap : Nat) :
    let seed := 4 * gap + 12 + 2 * delayExtra
    let endpoint := start + (seed + 3 * gap + 10 + 2 * delayExtra)
    start ≤ endpoint ∧
      start + 1 ≤ endpoint ∧
        start + 1 + 3 * gap + 8 + 2 * delayExtra ≤ endpoint ∧
          start + 1 + seed ≤ endpoint ∧
            (start + 1 + seed) + 3 * gap + 8 + 2 * delayExtra ≤ endpoint ∧
              start + 3 + delayExtra + gap ≤ endpoint := by
  dsimp only
  omega

private theorem seedGradeBounds_nat {start gap seedEnd endpoint q : Nat}
    (hseedBound : seedEnd + 3 * gap + 8 + 2 * delayExtra ≤ endpoint)
    (hlo : start + 2 ≤ q) (hhi : q ≤ seedEnd) :
    0 < q ∧ start ≤ q - 1 ∧ q + 3 * gap + 8 + 2 * delayExtra ≤ endpoint := by
  omega

private theorem height_eq_one_nat {M : Nat}
    (hone : 1 ≤ M) (hnotTwo : ¬ 2 ≤ M) : M = 1 := by
  omega

/-- Named form of the three gate-off seed outcomes. The grade arm binds both
opening proposals and the later proposal's actual named parent. -/
def HeightProgressSeedOutcome
    (S : Setup V) (rho : Run V) (M : Height)
    (base endpointRound : Round) (delayExtra : Nat := 0) : Prop :=
  M < honestHMaxAt S rho (S.a endpointRound) ∨
    (∃ u read,
      u ∈ rho.honest ∧
        S.E.t_GST ≤ read ∧
          read ≤ S.a endpointRound ∧
            FixedHeightJustificationRootAtRead S rho M u read) ∨
      ∃ entry q Q Next Parent,
        base + 1 ≤ entry ∧
          entry + 2 + delayExtra ≤ q ∧
          q ≤ endpointRound ∧
          ProposerCarrierAt S rho q ∧
          proposedBlockAt S rho (S.hc.opening_slot entry) = some Q ∧
          NamedGradeFormsAt S rho (q - 1) Q.erase ∧
          RunBlock S rho Q ∧
          (Protocol.derive_named S.E S.cfg Q).h = M ∧
          proposedBlockAt S rho (S.hc.opening_slot q) = some Next ∧
          NamedBlock.parent? Next = some Parent ∧
          NamedBlock.Preceq Q Parent ∧
          (Protocol.derive_named S.E S.cfg Parent).h =
            (Protocol.derive_named S.E S.cfg Q).h

/-- The named gate-off seed contract used by the public height handoff. -/
def HeightProgressSeedFrom
    (S : Setup V) (rho : Run V) (r0 gap : Round) (delayExtra : Nat := 0) : Prop :=
  ∀ base, r0 ≤ base →
    S.E.t_GST ≤ S.a base →
    (∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a base)).h_max =
        honestHMaxAt S rho (S.a base)) →
    (∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a base)).h_j + 2 ≤
        honestHMaxAt S rho (S.a base)) →
    S.a (base + seedLag gap delayExtra) ≤ rho.horizon →
    HeightProgressSeedOutcome (delayExtra := delayExtra) S rho
      (honestHMaxAt S rho (S.a base)) base (base + seedLag gap delayExtra)

/-- Under a public height-one cap, every honest strict store has exact local
frontier one and selects genesis as its FG root. -/
private theorem honestStrictRead_root_eq_genesis_and_hMax_eq_one
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time}
    (hcap : honestHMaxAt S rho read ≤ 1) :
    Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG = Block.genesis ∧
      (rho.storeBeforeTime S w read).h_max = 1 := by
  let st := rho.storeBeforeTime S w read
  have hlocalUpper : st.core.h_max ≤ 1 := by
    exact ((storeBeforeTime_hMax_le_storeAt
      S adm.toNamedScheduleWellFormed w read).trans
        (localHMax_le_honestHMaxAt S rho read hw)).trans hcap
  obtain ⟨D, _hDbody, hDheight⟩ :=
    Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime S rho read w
  have hlocalLower : 1 ≤ st.core.h_max := by
    have hDheight' : (Protocol.derive_named S.E S.cfg D).h =
        st.core.h_max := by
      simpa only [st] using hDheight
    rw [← hDheight']
    exact Protocol.one_le_derive_named_h S.E S.cfg D
  have hlocal : st.core.h_max = 1 :=
    Nat.le_antisymm hlocalUpper hlocalLower
  have hbelow : st.core.h_j < st.core.h_max := by
    simpa only [st] using
      NamedJustificationBound.justificationBelowMax_stateBeforeTime
        S rho read w
  have hhj : st.core.h_j = 0 := by
    rw [hlocal] at hbelow
    exact Nat.lt_one_iff.mp hbelow
  obtain ⟨Jc, _hJbody, hJ, hJh⟩ :=
    Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho read w
  have hJgen : st.core.J = Block.genesis := by
    have hJ' : (Protocol.derive_named S.E S.cfg Jc).J =
        st.core.J := by
      simpa only [st] using hJ
    have hJh' : (Protocol.derive_named S.E S.cfg Jc).h_j =
        st.core.h_j := by
      simpa only [st] using hJh
    rw [← hJ']
    exact NamedJustificationCertificates.justified_zero_is_genesis
      S.E S.cfg Jc (hJh'.trans hhj)
  have hgate : st.core.h_max = st.core.h_j + 1 := by
    rw [hlocal, hhj]
  refine ⟨?_, by simpa only [st] using hlocal⟩
  simpa only [st, Protocol.get_fg_root, Protocol.Store.toHealing,
    if_pos hgate, hJgen]

/-- A named derivation at height one still has the genesis height entry. -/
private theorem derivedTarget_eq_genesis_of_height_one
    (E : Env V) (cfg : Protocol.HeightConfig) : ∀ B : NamedBlock V,
    (Protocol.derive_named E cfg B).h = 1 →
      (Protocol.derive_named E cfg B).T_h = Block.genesis := by
  intro B
  induction B with
  | genesis => intro _; rfl
  | node p s root votes support rows proposer ih =>
      intro hheight
      rcases Proofs.NamedEntryHeight.transition_height_entry_cases E cfg
          (Protocol.derive_named E cfg p)
          (.node p s root votes support rows proposer) with hstay | hstep
      · change (Protocol.named_transition E cfg
          (Protocol.derive_named E cfg p)
          (.node p s root votes support rows proposer)).T_h =
            Block.genesis
        rw [hstay.2]
        apply ih
        change (Protocol.named_transition E cfg
          (Protocol.derive_named E cfg p)
          (.node p s root votes support rows proposer)).h = 1 at hheight
        exact hstay.1.symm.trans hheight
      · have hp : 1 ≤ (Protocol.derive_named E cfg p).h :=
          Protocol.one_le_derive_named_h E cfg p
        change (Protocol.named_transition E cfg
          (Protocol.derive_named E cfg p)
          (.node p s root votes support rows proposer)).h = 1 at hheight
        exfalso
        have heq : (Protocol.derive_named E cfg p).h + 1 = 1 :=
          hstep.1.symm.trans hheight
        have hz : (Protocol.derive_named E cfg p).h = 0 := by
          simpa only [Nat.add_eq_one_iff, Nat.one_ne_zero, and_false,
            or_false, and_true] using heq
        rw [hz] at hp
        exact Nat.not_succ_le_zero 0 hp

private theorem compose_namedParent_preceq_of_parent?
    {B P : NamedBlock V} (h : NamedBlock.parent? B = some P) :
    NamedBlock.Preceq P B := by
  cases B with
  | genesis => cases h
  | node parent slot root votes support rows proposer =>
      have hparent : parent = P := Option.some.inj h
      subst P
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr (Proofs.NamedAncestry.named_self parent)

/-- At an exact height-one public frontier, every sufficiently late opening
proposal satisfies the configured Rule-A wait. -/
private theorem heightOne_opening_timeoutMature
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hdelay : TimeoutDelayBound S delayExtra) {q : Round}
    (hqWait : 2 + delayExtra ≤ q) (hcarrier : ProposerCarrierAt S rho q)
    {endpoint : Time}
    (hproposalEnd :
      Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon)
    (hcapEnd : honestHMaxAt S rho endpoint ≤ 1) :
    ProposalTimeoutMatureAt S rho (S.hc.opening_slot q) := by
  intro Q hQ P hP
  have hqpos : 0 < q :=
    (by decide : 0 < 2).trans_le
      ((Nat.le_add_right 2 delayExtra).trans hqWait)
  have hspos : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hqpos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon := hproposalEnd.trans hendHor
  have hQheight : (Protocol.derive_named S.E S.cfg Q).h ≤ 1 :=
    (honestProposedBlock_height_le_honestHMaxAt
      S adm hspos hcarrier.1 hproposalHor hQ).trans
        ((honestHMaxAt_mono S adm.toNamedScheduleWellFormed
          hproposalEnd).trans hcapEnd)
  have hPQ : NamedBlock.Preceq P Q :=
    compose_namedParent_preceq_of_parent? hP
  have hPupper : (Protocol.derive_named S.E S.cfg P).h ≤ 1 :=
    (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hPQ).trans hQheight
  have hPheight : (Protocol.derive_named S.E S.cfg P).h = 1 :=
    Nat.le_antisymm hPupper
      (Protocol.one_le_derive_named_h S.E S.cfg P)
  rw [derivedTarget_eq_genesis_of_height_one S.E S.cfg P hPheight]
  simp only [Block.slot, Nat.zero_add, Protocol.HealConfig.opening_slot]
  exact (timeoutDelay_le_roundBound S hdelay).trans
    (Nat.mul_le_mul_right S.hc.R hqWait)

/-- Genesis is filtered at an honest strict read under a public height-one
cap. -/
private theorem genesis_filtered_of_heightOneCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time}
    (hcap : honestHMaxAt S rho read ≤ 1) :
    (Block.genesis : Block V) ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).core.toHealing.toFG := by
  have hroot :=
    (honestStrictRead_root_eq_genesis_and_hMax_eq_one S adm hw hcap).1
  have hmem := named_fgRoot_mem_filtered_stateBeforeTime S rho read w
  have hroot' : Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG =
        Block.genesis := by
    simpa only [Run.storeBeforeTime] using hroot
  rw [hroot'] at hmem
  simpa only [Run.storeBeforeTime] using hmem

/-- A genesis grade persists through a public height-one window in the named
relative-grade runtime. -/
private theorem genesisGradeFormsAt_persist_of_heightOneCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {base q' : Round}
    (hseed : NamedGradeFormsAt S rho base (Block.genesis : Block V))
    (hpost : S.E.t_GST ≤ S.a base)
    (hwindow : base ≤ q')
    (hendpoint : S.a q' ≤ rho.horizon)
    (hcapEnd : honestHMaxAt S rho (S.a q') ≤ 1) :
    (∀ r', base ≤ r' → r' ≤ q' →
      NamedGradeFormsAt S rho r' (Block.genesis : Block V)) ∧
    ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a q') Block.genesis := by
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hcapAt : ∀ {t : Time}, t ≤ S.a q' →
      honestHMaxAt S rho t ≤ 1 := by
    intro t ht
    exact (honestHMaxAt_mono S adm.toNamedScheduleWellFormed ht).trans hcapEnd
  have hforms : ∀ r', base ≤ r' → r' ≤ q' →
      NamedGradeFormsAt S rho r' (Block.genesis : Block V) := by
    intro r' hbase hr'end
    rcases eq_or_lt_of_le hbase with hEq | hlt
    · subst r'
      exact hseed
    · cases r' with
      | zero => exact (Nat.not_lt_zero _ hlt).elim
      | succ r =>
          have hbasePrev : base ≤ r := Nat.le_of_lt_succ hlt
          have hrendPrev : r ≤ q' := (Nat.le_succ r).trans hr'end
          have hactionNext : S.a (r + 1) ≤ S.a q' :=
            (action_strictMono S).monotone hr'end
          have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) .g2 ≤
              S.a (r + 1) := FrameForward.domain_le_a S (r + 1) .g2
          have hdomainEnd : DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) .g2 ≤
              S.a q' := hdomainAction.trans hactionNext
          have hactive : ∀ w ∈ rho.honest,
              (Block.genesis : Block V) ∈
                Protocol.get_filtered_block_tree
                  (healStoreAt S rho w (r + 1)).toFG := by
            intro w hw
            simpa only [healStoreAt] using
              genesis_filtered_of_heightOneCap S adm hw (hcapAt hactionNext)
          have hactiveDomain : ∀ w ∈ rho.honest,
              (Block.genesis : Block V) ∈ PhaseGrades.filteredTree
                (relativeG2Read S rho (r + 1) w) := by
            intro w hw
            have hmem := genesis_filtered_of_heightOneCap
              S adm hw (hcapAt hdomainEnd)
            simpa only [PhaseGrades.filteredTree, relativeG2Read,
              PhaseGrades.readAt, Run.storeBeforeTime] using hmem
          have hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon := by
            rw [gammaNeg1_eq_domain_g2_succ S r]
            exact hdomainEnd.trans hendpoint
          exact namedGradeFormsAt_succ_of_fgRootFloor
            S adm hmajority (r := r) (P := (Block.genesis : Block V))
              (F := (Block.genesis : Block V))
              (fun v hv => Protocol.preceq_genesis _)
              (hpost.trans ((action_strictMono S).monotone hbasePrev))
              hcut hactive hactiveDomain
  refine ⟨hforms, ?_⟩
  intro v hv
  unfold FinalityFilterRetainedAtRead
  exact genesis_filtered_of_heightOneCap S adm hv
    (hcapAt (show S.a q' ≤ S.a q' from le_rfl))

/-- At an exact height-one public frontier, a genesis grade and the active
opening eliminator force progress. -/
private theorem heightOneFrontier_rise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {start endpointRound gap : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a start)
    (hbound : start + 3 + delayExtra + gap ≤ endpointRound)
    (hendHor : S.a endpointRound ≤ rho.horizon)
    (hcapEnd : honestHMaxAt S rho (S.a endpointRound) ≤ 1) :
    1 < honestHMaxAt S rho (S.a endpointRound) := by
  have hcapAt : ∀ {k : Round}, k ≤ endpointRound →
      honestHMaxAt S rho (S.a k) ≤ 1 := by
    intro k hk
    exact (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (Assembly.a_mono S hk)).trans hcapEnd
  have hhorAt : ∀ {k : Round}, k ≤ endpointRound →
      S.a k ≤ rho.horizon := by
    intro k hk
    exact (Assembly.a_mono S hk).trans hendHor
  have hpostAt : ∀ {k : Round}, start ≤ k → S.E.t_GST ≤ S.a k := by
    intro k hk
    exact hpost.trans (Assembly.a_mono S hk)
  have hactiveGenesis : ∀ {k : Round}, k ≤ endpointRound →
      ∀ w ∈ rho.honest,
        (Block.genesis : Block V) ∈
          Protocol.get_filtered_block_tree
            (healStoreAt S rho w k).toFG := by
    intro k hk w hw
    simpa only [healStoreAt] using
      genesis_filtered_of_heightOneCap S adm hw (hcapAt hk)
  have hactiveGenesisDomain : ∀ {k : Round}, k ≤ endpointRound →
      ∀ w ∈ rho.honest,
        (Block.genesis : Block V) ∈ PhaseGrades.filteredTree
          (relativeG2Read S rho k w) := by
    intro k hk w hw
    have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2 ≤ S.a k :=
      FrameForward.domain_le_a S k .g2
    have hmem := genesis_filtered_of_heightOneCap S adm hw
      (hcapAt (k := k) hk |> fun hcap =>
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hdomainAction).trans hcap)
    simpa only [PhaseGrades.filteredTree, relativeG2Read,
      PhaseGrades.readAt, Run.storeBeforeTime] using hmem
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  obtain ⟨hseedRoundEnd, hstartOne, hstartTwo⟩ := lowPrelude_nat hbound
  have hseedHor : S.a (start + 2) ≤ rho.horizon :=
    hhorAt (k := start + 2) hseedRoundEnd
  have hcut : S.hc.Γ_neg1 S.E.Δ (start + 2) ≤ rho.horizon :=
    (le_of_lt (next_Γ_neg1_lt_action S (start + 1))).trans hseedHor
  have hseed : NamedGradeFormsAt S rho (start + 2)
      (Block.genesis : Block V) := by
    simpa only [Nat.add_assoc] using
      (namedGradeFormsAt_succ_of_fgRootFloor
        S adm hmajority (r := start + 1)
          (P := (Block.genesis : Block V))
          (F := (Block.genesis : Block V))
          (fun v hv => Protocol.preceq_genesis _)
          (hpostAt (k := start + 1) hstartOne) hcut
          (hactiveGenesis (k := start + 2) hseedRoundEnd)
          (hactiveGenesisDomain (k := start + 2) hseedRoundEnd))
  have htrigger : start < start + 3 + delayExtra :=
    (Nat.lt_add_of_pos_right (by decide : 0 < 3)).trans_le
      (Nat.le_add_right (start + 3) delayExtra)
  obtain ⟨q, hqlo, hqhi, hcarrier⟩ := hrec (start + 3 + delayExtra)
    (hpost.trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (action_add_delta_le_openingProposal_of_round_lt S htrigger)))
    ((openingProposal_window_le_action S (start + 3 + delayExtra) gap).trans
      ((Assembly.a_mono S hbound).trans hendHor))
  have hqEnd : q ≤ endpointRound := hqhi.trans hbound
  obtain ⟨hqpos, hseedQ, hseedQPred, hstartQPred⟩ :=
    lowSelected_nat hqlo
  have hqHor : S.a q ≤ rho.horizon := hhorAt (k := q) hqEnd
  have hproposalEnd : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ S.a endpointRound := by
    calc
      Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ S.a q := by
        rw [Setup.a, Protocol.a_eq_confirmation_time]
        exact Protocol.proposal_time_le_confirmation_time S.E _
      _ ≤ S.a endpointRound := Assembly.a_mono S hqEnd
  have hprevEnd : q - 1 ≤ endpointRound :=
    (Nat.sub_le q 1).trans hqEnd
  obtain ⟨hforms, hwindowPrev⟩ :=
    genesisGradeFormsAt_persist_of_heightOneCap
      S adm hfb hseed (hpostAt (k := start + 2) hstartTwo)
        hseedQPred (hhorAt hprevEnd) (hcapAt hprevEnd)
  have hformsPrev : NamedGradeFormsAt S rho (q - 1)
      (Block.genesis : Block V) :=
    hforms (q - 1) hseedQPred (Nat.le_refl _)
  have hpostPrev : S.E.t_GST ≤ S.a (q - 1) :=
    hpostAt (k := q - 1) hstartQPred
  have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ S.a q :=
    FrameForward.domain_le_a S q .g2
  have hdomainWindow : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) Block.genesis := by
    intro w hw
    unfold FinalityFilterRetainedAtRead
    exact genesis_filtered_of_heightOneCap S adm hw
      ((honestHMaxAt_mono S adm.toNamedScheduleWellFormed hdomainAction).trans
        (hcapAt hqEnd))
  obtain ⟨v0, hv0⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hgenTree : (Block.genesis : Block V) ∈
      (rho.storeBeforeTime S v0
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q - 1) .g2)).core.T := by
    have hfiltered := (hformsPrev v0 hv0).1
    have htree := Proofs.Records.get_filtered_block_tree_subset _ hfiltered
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
      Run.storeBeforeTime] using htree
  obtain ⟨G, hGerase, hGRun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime
      S adm.toNamedScheduleWellFormed hv0
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q - 1) .g2) hgenTree
  have hG : G = NamedBlock.genesis := by
    cases G with
    | genesis => rfl
    | node p s root votes support rows proposer =>
        cases hGerase
  subst G
  have hactive : ∀ w ∈ rho.honest,
      (Block.genesis : Block V) ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG :=
    hactiveGenesis hqEnd
  rcases activeExactHeightOpening_fixedInterference_or_hMaxRise
      S adm hfb (H := 1) (source := (NamedBlock.genesis : NamedBlock V))
        hqpos hcarrier hformsPrev hwindowPrev hdomainWindow hGRun rfl
        hpostPrev
        (heightOne_opening_timeoutMature S adm hdelay
          (q := q) (hcarrier := hcarrier)
          (hqWait := lowSelected_delay_nat hqlo) hproposalEnd hendHor hcapEnd)
        hactive (Assembly.a_mono S hqEnd) hendHor with
    hrise | hfixed
  · exact hrise
  · have himpossible : 0 < 0 := by
      simpa only using hfixed.1.targetHeightPositive
    exact False.elim ((Nat.lt_irrefl 0) himpossible)

#print axioms honestStrictRead_root_eq_genesis_and_hMax_eq_one
#print axioms derivedTarget_eq_genesis_of_height_one
#print axioms heightOne_opening_timeoutMature
#print axioms genesisGradeFormsAt_persist_of_heightOneCap
#print axioms heightOneFrontier_rise



end HealingSurface
end Proofs
end DecoupledConsensusModel




namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}








private theorem compose_storeBeforeTime_eq_storeAt_sub_one
    (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    rho.storeBeforeTime S v t = rho.storeAt S v (t - 1) := by
  have hfilter :
      (fun e : Event V => decide (e.time < t)) =
        (fun e : Event V => decide (e.time ≤ t - 1)) := by
    funext e
    exact Bool.decide_congr (Int.le_sub_one_iff).symm
  unfold Run.storeBeforeTime Run.storeAt NamedRun.stateBeforeTime NamedRun.readAt
  rw [hfilter]

/-- A named exact-height grade remains filtered at the preceding action and
the next G2-domain read when the next action is still in the gate-off regime.
The public cap supplies the missing upper bound at both earlier reads. -/
private theorem gradeWindows_of_gateOff_at_nextAction
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {Q : NamedBlock V}
    (hq : 0 < q)
    (hforms : NamedGradeFormsAt S rho (q - 1) Q.erase)
    (hQrun : RunBlock S rho Q)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = M)
    (hM : 1 ≤ M)
    (hcapQ : honestHMaxAt S rho (S.a q) ≤ M)
    (hgateQ : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a q)).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w (S.a q)).h_max = M)
    (hhorQ : S.a q ≤ rho.horizon) :
    (∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q - 1)) Q.erase) ∧
    (∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) Q.erase) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hretain : ∀ {target : Time}, S.a (q - 1) ≤ target →
      target ≤ S.a q → target ≤ rho.horizon →
      ∀ w ∈ rho.honest,
        FinalityFilterRetainedAtRead S rho w target Q.erase := by
    intro target hafter hbefore htargetHor w hw
    have hprocessed : Q.erase ∈
        (rho.storeBeforeTime S w target).core.T :=
      gradeFormsAt_processedAtRead_of_action_le
        S adm hforms hw hafter
    obtain ⟨D, hDbody, hDerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho target w hprocessed
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho adm.toNamedScheduleWellFormed.sorted target
    have hDprefix : D ∈ (rho.stateBefore S i w).st.bodies := by
      change D ∈ (NamedRun.stateBefore S rho i w).st.bodies
      rw [← hi]
      exact hDbody
    have hDrun : RunBlock S rho D :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hw hDprefix
    have hrootEq : D.root = Q.root := by
      rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root Q, hDerase]
    have hDQ : D = Q :=
      adm.toNamedRootCollisionFree.root_injective D Q hDrun hQrun D Q
        (Or.inl (Proofs.NamedAncestry.named_self D))
        (Or.inr (Proofs.NamedAncestry.named_self Q)) hrootEq
    have hQle : (Protocol.derive_named S.E S.cfg Q).h ≤
        (rho.storeBeforeTime S w target).core.h_max := by
      rw [← hDQ]
      exact Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
        S rho target w D hDbody
    have hlocalUpper :
        (rho.storeBeforeTime S w target).core.h_max ≤ M := by
      exact ((storeBeforeTime_hMax_le_storeAt
        S adm.toNamedScheduleWellFormed w target).trans
          (localHMax_le_honestHMaxAt S rho target hw)).trans
            ((honestHMaxAt_mono S adm.toNamedScheduleWellFormed hbefore).trans
              hcapQ)
    have hlocal : (rho.storeBeforeTime S w target).core.h_max = M :=
      Nat.le_antisymm hlocalUpper (by rw [← hQheight]; exact hQle)
    have hjmono : (rho.storeBeforeTime S w target).core.h_j ≤
        (rho.storeBeforeTime S w (S.a q)).core.h_j :=
      by
        rw [compose_storeBeforeTime_eq_storeAt_sub_one,
          compose_storeBeforeTime_eq_storeAt_sub_one]
        exact stateAt_h_j_mono S adm.toNamedScheduleWellFormed w
          (Int.sub_le_sub_right hbefore 1)
    have hgate : (rho.storeBeforeTime S w target).core.h_j + 2 ≤ M :=
      (Nat.add_le_add_right hjmono 2).trans (hgateQ w hw).1
    unfold FinalityFilterRetainedAtRead
    exact frontierBlock_filtered_of_gateOff S adm hsb hw htargetHor
      hprocessed rfl hQrun (by rw [hQheight]; exact Nat.sub_le M 1)
        hM hlocal hgate
  have hpredAction : S.a (q - 1) ≤ S.a q :=
    Assembly.a_mono S (Nat.sub_le q 1)
  have hdomainAction :
      DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ S.a q :=
    FrameForward.domain_le_a S q .g2
  have hpredDomain : S.a (q - 1) ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 := by
    have hstep := NamedOutageClosure.action_le_domain
      S S.hc.R_ge_three (Nat.sub_lt hq (by decide : 0 < 1))
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hq))] using hstep
  refine ⟨?_, ?_⟩
  · exact hretain (le_refl _) hpredAction (hpredAction.trans hhorQ)
  · exact hretain hpredDomain hdomainAction (hdomainAction.trans hhorQ)



/-- The numeric pointwise height-progress theorem under the named gate-off
seed hypothesis. -/
theorem heightProgress_pointwise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {r0 gap start : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hseed : HeightProgressSeedFrom (delayExtra := delayExtra) S rho r0 gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a r0)
    (_of_fixedRootProgress : ∀ {M : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      FixedHeightJustificationRootAtRead S rho M u read →
      S.E.t_GST ≤ read → read ≤ S.a r →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      S.a endpointRound ≤ rho.horizon →
      honestHMaxAt S rho (S.a endpointRound) ≤ M →
      M < honestHMaxAt S rho (S.a endpointRound))
    (hr0 : r0 ≤ start)
    (hhor : S.a (start + progressLag' gap delayExtra) ≤ rho.horizon) :
    honestHMaxAt S rho (S.a start) <
      honestHMaxAt S rho (S.a (start + progressLag' gap delayExtra)) := by
  let M : Height := honestHMaxAt S rho (S.a start)
  let endpointRound : Round := start + progressLag' gap delayExtra
  have hstatic :
      start ≤ endpointRound ∧
        start + 1 ≤ endpointRound ∧
          start + 1 + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound ∧
            start + 1 + seedLag gap delayExtra ≤ endpointRound ∧
              (start + 1 + seedLag gap delayExtra) + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound ∧
                start + 3 + delayExtra + gap ≤ endpointRound := by
    simpa only [endpointRound, progressLag', seedLag] using
      (composeStaticBounds_nat start gap)
  by_cases hrise : M < honestHMaxAt S rho (S.a endpointRound)
  · simpa only [M, endpointRound] using hrise
  · have hcapEnd : honestHMaxAt S rho (S.a endpointRound) ≤ M :=
      Nat.le_of_not_gt hrise
    have hMone : 1 ≤ M := by
      simpa only [M] using one_le_honestHMaxAt S adm hcom (S.a start)
    by_cases hMtwo : 2 ≤ M
    · have hsb : SlashableBound S rho :=
        slashableBound_of_admissible_belowOneThird S adm hfb
      have hpostStart : S.E.t_GST ≤ S.a start :=
        hpost.trans (Assembly.a_mono S hr0)
      have hcapAt : ∀ {k : Round}, k ≤ endpointRound →
          honestHMaxAt S rho (S.a k) ≤ M := by
        intro k hk
        exact (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
          (Assembly.a_mono S hk)).trans hcapEnd
      have hhorAt : ∀ {k : Round}, k ≤ endpointRound →
          S.a k ≤ rho.horizon := by
        intro k hk
        exact (Assembly.a_mono S hk).trans (by simpa only [endpointRound] using hhor)
      have hrelayEnd : start + 1 ≤ endpointRound := hstatic.2.1
      rcases frontierRegime_after_oneDelay
          S adm hfb hsb (M := M) (hM := rfl) hpostStart
            (hcapAt (k := start + 1) hrelayEnd)
            (hhorAt (k := start + 1) hrelayEnd) hMtwo with
        ⟨u, hu, hfix⟩ | hgateOff
      · have hfixedBound : start + 1 + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound :=
          hstatic.2.2.1
        have hr := _of_fixedRootProgress hfix
          (hpostStart.trans (Assembly.a_mono S (Nat.le_succ start)))
          (le_refl _) hfixedBound
          (by simpa only [endpointRound] using hhor) hcapEnd
        simpa only [M, endpointRound] using hr
      · let base : Round := start + 1
        let seedEnd : Round := base + seedLag gap delayExtra
        have hbaseEnd : base ≤ endpointRound := by
          simpa only [base] using hstatic.2.1
        have hseedEnd : seedEnd ≤ endpointRound := by
          simpa only [seedEnd, base] using hstatic.2.2.2.1
        have hstartBase : start ≤ base := by
          simp only [base]
          exact Nat.le_succ start
        have hfrontierBase : ∀ w ∈ rho.honest,
            (rho.storeBeforeTime S w (S.a base)).h_max =
              honestHMaxAt S rho (S.a base) := by
          intro w hw
          have hpublic : honestHMaxAt S rho (S.a base) = M :=
            Nat.le_antisymm (hcapAt hbaseEnd)
              (by
                simpa only [M] using
                  honestHMaxAt_mono S adm.toNamedScheduleWellFormed
                    (Assembly.a_mono S hstartBase))
          simpa only [base, hpublic] using (hgateOff w hw).2
        have hgateBase : ∀ w ∈ rho.honest,
            (rho.storeBeforeTime S w (S.a base)).h_j + 2 ≤
              honestHMaxAt S rho (S.a base) := by
          intro w hw
          have hpublic : honestHMaxAt S rho (S.a base) = M :=
            Nat.le_antisymm (hcapAt hbaseEnd)
              (by
                simpa only [M] using
                  honestHMaxAt_mono S adm.toNamedScheduleWellFormed
                    (Assembly.a_mono S hstartBase))
          simpa only [base, hpublic] using (hgateOff w hw).1
        have hseedOutcome := hseed base
          (hr0.trans hstartBase)
          (hpostStart.trans (Assembly.a_mono S hstartBase))
          hfrontierBase hgateBase
          (by simpa only [seedEnd] using hhorAt (k := seedEnd) hseedEnd)
        change HeightProgressSeedOutcome (delayExtra := delayExtra) S rho
          (honestHMaxAt S rho (S.a base)) base seedEnd at hseedOutcome
        have hbaseFrontier : honestHMaxAt S rho (S.a base) = M := by
          apply Nat.le_antisymm (hcapAt hbaseEnd)
          simpa only [M] using
            honestHMaxAt_mono S adm.toNamedScheduleWellFormed
              (Assembly.a_mono S hstartBase)
        rw [hbaseFrontier] at hseedOutcome
        rcases hseedOutcome with
          hseedRise | hseedFix | hseedGrade
        · have hr := hseedRise.trans_le
            (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
              (Assembly.a_mono S hseedEnd))
          simpa only [M, endpointRound] using hr
        · rcases hseedFix with ⟨u, read, hu, hpostRead, hread, hfix⟩
          have hfixedBound : seedEnd + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound := by
            simpa only [seedEnd, base] using hstatic.2.2.2.2.1
          have hstartSeedEnd : start ≤ seedEnd :=
            hstartBase.trans (by
              simp only [seedEnd]
              exact Nat.le_add_right base (seedLag gap delayExtra))
          have hr := _of_fixedRootProgress hfix hpostRead hread hfixedBound
            (by simpa only [endpointRound] using hhor) hcapEnd
          simpa only [M, endpointRound] using hr
        · rcases hseedGrade with
            ⟨entry0, q0, Q, Next, Parent, hentry0lo, hentry0space, hq0hi,
              hcarrier0, hQentry, hforms0, hQrun, hQheight,
              hNext, hParent, hQpreceq, hQsameHeight⟩
          have hq0loBase : base + 3 ≤ q0 := by
            calc
              base + 3 = (base + 1) + 2 := by simp [Nat.add_assoc]
              _ ≤ entry0 + 2 := Nat.add_le_add_right hentry0lo 2
              _ ≤ entry0 + 2 + delayExtra := Nat.le_add_right _ delayExtra
              _ ≤ q0 := hentry0space
          have hq0lo' : start + 2 ≤ q0 := by
            apply (show start + 2 ≤ base + 3 by
              simpa only [base, Nat.add_assoc] using
                (Nat.le_add_right (start + 2) 2)).trans
            exact hq0loBase
          have hseedFixedBound : seedEnd + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound := by
            simpa only [seedEnd, base] using hstatic.2.2.2.2.1
          obtain ⟨hq0pos, hstartQ0Pred, hq0FixedBound⟩ :=
            seedGradeBounds_nat hseedFixedBound hq0lo' hq0hi
          have hentry0pos : 0 < entry0 := by
            exact (Nat.zero_lt_succ base).trans_le hentry0lo
          have hq0PredAdd : q0 - 1 + 1 = q0 := Nat.sub_add_cancel hq0pos
          have hq0End : q0 ≤ endpointRound := hq0hi.trans hseedEnd
          have hq0PredEnd : q0 - 1 ≤ endpointRound :=
            (Nat.sub_le q0 1).trans hq0End
          have hfrontierQ0Pred : honestHMaxAt S rho (S.a (q0 - 1)) = M :=
            Nat.le_antisymm (hcapAt hq0PredEnd) (by
              simpa only [M] using
                honestHMaxAt_mono S adm.toNamedScheduleWellFormed
                  (Assembly.a_mono S hstartQ0Pred))
          have hpostQ0Pred : S.E.t_GST ≤ S.a (q0 - 1) :=
            hpostStart.trans (Assembly.a_mono S hstartQ0Pred)
          have hcapQ0 : honestHMaxAt S rho (S.a q0) ≤ M :=
            hcapAt (k := q0) hq0End
          have hhorQ0 : S.a q0 ≤ rho.horizon :=
            hhorAt (k := q0) hq0End
          have hmatureQ0 : ProposalTimeoutMatureAt S rho
              (S.hc.opening_slot q0) :=
            laterOpening_timeoutMature_of_sameHeight
              S adm hdelay hentry0pos hentry0space hQentry hNext hParent
                hQpreceq hQsameHeight
          have hregimeQ0Raw := frontierRegime_after_oneDelay
            S adm hfb hsb (start := q0 - 1) (M := M)
              hfrontierQ0Pred hpostQ0Pred
                (by simpa only [hq0PredAdd] using hcapQ0)
                (by simpa only [hq0PredAdd] using hhorQ0) hMtwo
          have hregimeQ0 :
              (∃ u ∈ rho.honest,
                FixedHeightJustificationRootAtRead S rho M u (S.a q0)) ∨
              (∀ w ∈ rho.honest,
                (rho.storeBeforeTime S w (S.a q0)).h_j + 2 ≤ M ∧
                  (rho.storeBeforeTime S w (S.a q0)).h_max = M) := by
            simpa only [hq0PredAdd] using hregimeQ0Raw
          rcases hregimeQ0 with ⟨u, hu, hfix⟩ | hgateQ0
          · have hr := _of_fixedRootProgress hfix
              (by
                exact hpostQ0Pred.trans
                  (Assembly.a_mono S (Nat.sub_le q0 1)))
              (le_refl _) hq0FixedBound
              (by simpa only [endpointRound] using hhor) hcapEnd
            simpa only [M, endpointRound] using hr
          · have hactiveQ0 : ∀ w ∈ rho.honest,
                Q.erase ∈ Protocol.get_filtered_block_tree
                  (healStoreAt S rho w q0).toFG := by
              intro w hw
              have hprocessed : Q.erase ∈ (healStoreAt S rho w q0).T :=
                gradeFormsAt_processedAtRead_of_action_le
                  S adm hforms0 hw
                    ((action_strictMono S).monotone (Nat.sub_le q0 1))
              exact frontierBlock_filtered_at_healStoreAt_of_gateOff
                S adm hsb hw (hhorAt (k := q0) hq0End) hprocessed rfl hQrun
                  (by rw [hQheight]; exact Nat.sub_le M 1) hMone
                  (by simpa only [healStoreAt] using (hgateQ0 w hw).2)
                  (by simpa only [healStoreAt] using (hgateQ0 w hw).1)
            obtain ⟨hwindowPrev, hdomainWindow⟩ :=
              gradeWindows_of_gateOff_at_nextAction
                S adm hfb hq0pos hforms0 hQrun hQheight hMone hcapQ0
                  hgateQ0 hhorQ0
            rcases activeExactHeightOpening_fixedInterference_or_hMaxRise
                S adm hfb hq0pos hcarrier0 hforms0 hwindowPrev hdomainWindow
                  hQrun hQheight hpostQ0Pred hmatureQ0 hactiveQ0
                  (Assembly.a_mono S hq0End)
                    (by simpa only [endpointRound] using hhor) with
              hrise0 | hfixed0
            · simpa only [M, endpointRound] using hrise0
            · have hpostProposal : S.E.t_GST ≤
                  Protocol.proposal_time S.E (S.hc.opening_slot q0) := by
                have hnonneg : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
                calc
                  S.E.t_GST ≤ S.a (q0 - 1) := hpostQ0Pred
                  _ ≤ S.a (q0 - 1) + S.E.Δ :=
                    Int.le_add_of_nonneg_right hnonneg
                  _ ≤ Protocol.proposal_time S.E (S.hc.opening_slot q0) :=
                    action_add_delta_le_openingProposal_of_round_lt S
                      (Nat.sub_lt hq0pos (by decide))
              have hr := _of_fixedRootProgress
                hfixed0.1.toJustificationRootAtRead hpostProposal
                  hfixed0.2.1 hq0FixedBound
                  (by simpa only [endpointRound] using hhor) hcapEnd
              simpa only [M, endpointRound] using hr
    · have hMeq : M = 1 := height_eq_one_nat hMone hMtwo
      have hbound : start + 3 + delayExtra + gap ≤ endpointRound := hstatic.2.2.2.2.2
      have hr := heightOneFrontier_rise S adm hcom hfb hrec
        hdelay (hpost.trans (Assembly.a_mono S hr0)) hbound
        (by simpa only [endpointRound] using hhor) (by simpa only [hMeq] using hcapEnd)
      have : M < honestHMaxAt S rho (S.a endpointRound) := by
        simpa only [hMeq] using hr
      simpa only [M, endpointRound] using this


/-- The pointwise numeric theorem supplies the numeric arm of the bounded
mixed assembler contract. -/
theorem boundedHeightGradeOrProgressFrom_of_seed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {r0 gap : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hseed : HeightProgressSeedFrom (delayExtra := delayExtra) S rho r0 gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a r0)
    (_of_fixedRootProgress : ∀ {M : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      FixedHeightJustificationRootAtRead S rho M u read →
      S.E.t_GST ≤ read → read ≤ S.a r →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      S.a endpointRound ≤ rho.horizon →
      honestHMaxAt S rho (S.a endpointRound) ≤ M →
      M < honestHMaxAt S rho (S.a endpointRound))
    :
    BoundedHeightGradeOrProgressFrom S rho r0 (progressLag' gap delayExtra) := by
  refine ⟨progressLag'_pos (delayExtra := delayExtra) gap, ?_⟩
  intro start hr0 hhor
  exact Or.inr
    (heightProgress_pointwise S adm hcom hfb hrec hseed hdelay hpost
      _of_fixedRootProgress hr0 hhor)


/-- Public eventual numeric height progress under the one named seed
hypothesis. -/
theorem eventualHeightProgressFrom_of_seed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {r0 gap : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hseed : HeightProgressSeedFrom (delayExtra := delayExtra) S rho r0 gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a r0)
    (_of_fixedRootProgress : ∀ {M : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      FixedHeightJustificationRootAtRead S rho M u read →
      S.E.t_GST ≤ read → read ≤ S.a r →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      S.a endpointRound ≤ rho.horizon →
      honestHMaxAt S rho (S.a endpointRound) ≤ M →
      M < honestHMaxAt S rho (S.a endpointRound))
    :
    EventualHeightProgressFrom S rho r0 (progressLag' gap delayExtra) :=
  eventualHeightProgressFrom_of_boundedHeightGradeOrProgress
    S adm hcom
      (boundedHeightGradeOrProgressFrom_of_seed
        S adm hcom hfb hrec hseed hdelay hpost
          _of_fixedRootProgress)


#print axioms heightProgress_pointwise
#print axioms boundedHeightGradeOrProgressFrom_of_seed
#print axioms eventualHeightProgressFrom_of_seed
#print axioms gradeWindows_of_gateOff_at_nextAction

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
