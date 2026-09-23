module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedOpeningWindow
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SeedPredPromotion
public import DecoupledConsensusProofs.Execution.SeedGradeExistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedBandGrade
public import DecoupledConsensusProofs.Protocol.Grades.SeedLifecyclePacket
public import DecoupledConsensusProofs.Execution.SeedCommonRootComplement
public import DecoupledConsensusProofs.Execution.SeedPromotionAncestor
public import DecoupledConsensusProofs.Execution.SeedFreshPromotion
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressCompose

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The gate-off height-progress seed

`HeightProgressSeedFrom` from the seed base. The run splits the opening height
of a carrier round of the window into three cases: the exact frontier height
`M` (leaf (c)), the predecessor height `M - 1`, and a public rise.

The `M - 1` case is closed by `SeedPredPromotionRun`, which carries the round's
own action rows to the next carrier round's opening and lands back in the exact
case there. Its only extra input is `TimeoutDelayBound S delayExtra`, already a
hypothesis of the final assembly. The export that uses it is
`heightProgressSeedFrom_of_graded`, on the two protocol residuals of the base
alone. `heightProgressSeedFrom_of_residual` is kept unchanged for the current
assembly wiring: it names the `M - 1` case as `SeedPromotionResidualFrom` and
takes no delay bound.

## Named runtime

Each opening proposal is a named witness: `proposedBlockAt S rho s = some P`
with `P: NamedBlock V`, and its height is `Protocol.derive_named S.E S.cfg P`.
The three-way opening split is proved here, on earlier's route, over the named
opening window `NamedGateOffOpeningWindowAt`, and so is the seed entry
`seedFixedRoot_or_gateOffWindow`, whose own producer
(`frontierRegime_window_after_oneDelay`) is live.

`SeedRetiredProducers` and `SeedPredPromotionInputs` state the two
additional producer conditions consumed by this seed.
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

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-! ## Pinned producers (PRE-BUILDING) -/



/-- **The pinned inputs of
`SeedPredPromotionRun.seedPredOpening_exactAtNextCarrier`**, at the carrier
round `q` whose opening proposal `B` is at height `M - 1` and at the next
carrier round `q'` with opening proposal `B'`.

Four of that theorem's original seven `_of_*` arguments are now proved there
(the action-Q2 G1 grade, the action-read derivation, the gate-off own lock, and
the prepared `nodeQ2` selection under ), and its row-coverage fusion is
proved from `actionAttestationAt_coveredAtProposal_of_chainRows`. The lifecycle
records is derived at the promotion call from the seed's local frame. The two
fields left concern later-parent ancestry and row carriage. The promotion
theorem is live and is used, never re-proved. -/
structure SeedPredPromotionInputsAt
    (S : Setup V) (rho : Run V) (M : Height) (q q' : Round)
    (B B' : NamedBlock V) : Prop where
  /-- A current FG source is no higher than the later opening's parent. This
  is used only in the still-`M - 1` branch, where fresh rows are renewed at
  the immediately preceding round. -/
  sourceHeightLeNextOpeningParent :
    ∀ v ∈ rho.honest, ∀ Q : Block V,
      PhaseGrades.nodeFGSource S (actionReadAt S rho v (q' - 1)) (q' - 1) = some Q →
      ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h ≤
        (Protocol.derive_named S.E S.cfg B'.parent).h

/-- The promotion inputs wherever the `M - 1` closer reaches for them: at a
graded carrier round with a ceiling, a named opening window and an opening
proposal one height below the frontier, and at the next carrier round.
The closer also supplies its full read frame and the persisted grade at the
last action before that next opening. These are internal context, not public
assumptions. -/
def SeedPredPromotionInputs
    (S : Setup V) (rho : Run V) (delayExtra : Nat := 0) : Prop :=
  ∀ (M : Height) (q q' : Round) (C C' B B' : NamedBlock V),
    2 ≤ M →
    SeedRoundGradedAt S rho q →
    ProposerCarrierAt S rho q →
    RoundCeilingAt S rho M q C →
    NamedGateOffOpeningWindowAt S rho M q B →
    (Protocol.derive_named S.E S.cfg B).h = M - 1 →
    q + 2 + delayExtra ≤ q' →
    ProposerCarrierAt S rho q' →
    RoundCeilingAt S rho M q' C' →
    NamedGateOffOpeningWindowAt S rho M q' B' →
    S.E.t_GST ≤ S.a (q' - 2) →
    S.a q' ≤ rho.horizon →
    (∀ read : Time, S.a (q' - 2) ≤ read → read ≤ S.a q' →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M) →
    RunBlock S rho B →
    NamedGradeFormsAt S rho (q' - 1) B.erase →
    (∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q' - 1)) B.erase) →
    SeedPredPromotionInputsAt S rho M q q' B B'

/-! ## Named parents of an opening proposal -/

omit [Fintype V] in
/-- A retained named parent is a named ancestor of its own block. -/
private theorem namedParent_preceq
    {B p : NamedBlock V} (hp : NamedBlock.parent? B = some p) :
    NamedBlock.Preceq p B := by
  cases B with
  | genesis => cases hp
  | node parent slot root votes support rows proposer =>
      have hparent : parent = p := Option.some.inj hp
      subst p
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

/-- An accepted proposal is never genesis, so its `parent` accessor is exactly
the parent its `parent?` query returns. -/
private theorem namedProposal_parent?_eq
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    NamedBlock.parent? P = some P.parent := by
  obtain ⟨p, hp, -⟩ := proposedBlockAt_parent S rho s hP
  cases P with
  | genesis => cases hp
  | node parent slot root votes support rows proposer => rfl

/-- The opening proposal's own named parent precedes it. -/
private theorem namedProposalParent_preceq
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    NamedBlock.Preceq P.parent P :=
  namedParent_preceq (namedProposal_parent?_eq S rho s hP)

/-! ## The seed entry -/

/-- One relay after the base action read the window is open. -/
private theorem seedRelayStep (S : Setup V) (base : Round) :
    S.a base + 1 + S.E.Δ ≤ S.a (base + 1) := by
  have hlt : S.a base + S.E.Δ < S.a (base + 1) :=
    lt_of_le_of_lt (action_add_delta_le_next_Γ_neg1 S base)
      (next_Γ_neg1_lt_action S base)
  calc
    S.a base + 1 + S.E.Δ = S.a base + S.E.Δ + 1 := by ring
    _ ≤ S.a (base + 1) := (Int.add_one_le_iff).mpr hlt

/-- **The seed entry.** From an exact honest frontier at a post-GST base
round, either the unique fixed-height justification root is exposed at an
honest read of the window — the gate-on outcome of the height-progress seed —
or every honest strict read from the next action read to the window's end is
gate off at that exact frontier.

earlier's `SeedBaseCeilingRun.seedFixedRoot_or_gateOffWindow` on earlier's route; the
route's own producer `frontierRegime_window_after_oneDelay` is live, so the
statement is proved here. -/
private theorem seedBaseFixedRoot_or_gateOffWindow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {base endpoint : Round}
    (hM : honestHMaxAt S rho (S.a base) = M)
    (hpost : S.E.t_GST ≤ S.a base)
    (h2 : 2 ≤ M)
    (hcap : honestHMaxAt S rho (S.a endpoint) ≤ M)
    (hhor : S.a endpoint ≤ rho.horizon) :
    (∃ u ∈ rho.honest, ∃ read : Time, S.E.t_GST ≤ read ∧
      read ≤ S.a endpoint ∧
      FixedHeightJustificationRootAtRead S rho M u read) ∨
    (∀ read : Time, S.a (base + 1) ≤ read → read ≤ S.a endpoint →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  rcases frontierRegime_window_after_oneDelay S adm hfb hsb hM hpost
      (seedRelayStep S base) hcap hhor h2 with
    ⟨u, hu, read, hlo, hhi, hfix⟩ | hgate
  · exact Or.inl ⟨u, hu, read, hpost.trans
      ((Assembly.a_mono S (Nat.le_succ base)).trans hlo), hhi, hfix⟩
  · exact Or.inr hgate

/-- **The gate-off opening floor, over the named proposal.** earlier's route of
`SeedPromotionRun.gateOff_openingProposal_pred_or_exact_or_hMaxRise`: the
selected parent already reaches `M - 1`, so the proposal does; under no public
rise the honest proposal height gives the matching upper bound, and the two
leave only `M - 1` and `M`. -/
private theorem namedGateOffOpening_pred_or_exact_or_hMaxRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {q : Round} {P : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho q)
    (hwindow : NamedGateOffOpeningWindowAt S rho M q P) :
    (Protocol.derive_named S.E S.cfg P).h = M - 1 ∨
      (Protocol.derive_named S.E S.cfg P).h = M ∨
      M < honestHMaxAt S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot q)) := by
  have hproposalHor : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E _).trans
      (by simpa only [Setup.a, Protocol.a_eq_confirmation_time] using
        ((Assembly.a_mono S (Nat.le_succ q)).trans hwindow.nextActionInHorizon))
  have hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest := hcarrier.1
  have hs : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hwindow.roundPositive
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hlower : M - 1 ≤ (Protocol.derive_named S.E S.cfg P).h :=
    hwindow.parentHeight.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        (namedProposalParent_preceq S rho _ hwindow.proposal))
  by_cases hrise : M < honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q))
  · exact Or.inr (Or.inr hrise)
  · have hupper : (Protocol.derive_named S.E S.cfg P).h ≤ M :=
      (honestProposedBlock_height_le_honestHMaxAt S adm hs hprop hproposalHor
        hwindow.proposal).trans (Nat.le_of_not_gt hrise)
    rcases Nat.eq_or_lt_of_le hupper with heq | hlt
    · exact Or.inr (Or.inl heq)
    · exact Or.inl (Nat.le_antisymm (Nat.le_pred_of_lt hlt) hlower)

/-! ## The lifecycle's next-domain activity, supplied rather than pinned -/

/-- The processed tree of one validator only grows in the reading time. -/
private theorem seedStore_T_subset
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) {t u : Time} (htu : t ≤ u) :
    (rho.storeBeforeTime S v t).T ⊆ (rho.storeBeforeTime S v u).T := by
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch,
    storeBeforeTime_eq_stateBefore_strictEventIndex S sch]
  exact stateBefore_T_subset S rho v _ (strictEventIndex_mono rho htu)

/-- **The opening proposal is active at the next round's G2-domain read.**

`NamedGradeFormsAt` reads the G2 domain of round `q + 1`, which is
`Gamma[-1] (q+1)`, one phase before that round's action, and the gate-off
window record has no field there. The seed does not need one: the proposal is
already processed at the round-`q` confirmation read, which IS the round
action; the processed tree only grows with the reading time; and the gate-off
frame at the domain read turns processed membership into filter membership.

This is the `hnextActiveDomain` input of
`gateOff_openingLifecycle_of_roundCeiling`, which that theorem's own doc says
is not a pin. The seed supplies it.

Public because `SeedEntryCanonicalRun` applies the same lifecycle producer and
needs the same input; it holds the carrier, the named window and the frame
clause already. -/
theorem seedOpeningProposal_nextActiveDomain
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {P : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho q)
    (hwindow : NamedGateOffOpeningWindowAt S rho M q P)
    (hframe : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q + 1))).h_max = M ∧
        (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q + 1))).h_j + 2 ≤ M) :
    ∀ w ∈ rho.honest,
      P.erase ∈ PhaseGrades.filteredTree
        (relativeG2Read S rho (q + 1) w) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hs : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hwindow.roundPositive
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hactionHor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hwindow.nextActionInHorizon
  have hproposalHor : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E _).trans
      (by simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hactionHor)
  have hPrun : RunBlock S rho P :=
    Protocol.proposedBlock_runBlock S adm hs hcarrier.1 hproposalHor
      hwindow.proposal
  have hM : 1 ≤ M := by
    have htwo : 2 ≤ M :=
      (Nat.le_add_left 2
        (proposerDutyStore S rho (S.hc.opening_slot q)).h_j).trans
          hwindow.proposerGateOff
    exact (by decide : (1 : Nat) ≤ 2).trans htwo
  have hheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg P).h :=
    hwindow.parentHeight.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        (namedProposalParent_preceq S rho _ hwindow.proposal))
  have hcutLo : S.a q ≤ S.hc.Γ_neg1 S.E.Δ (q + 1) :=
    le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (action_add_delta_le_next_Γ_neg1 S q)
  have hcutHor : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (next_Γ_neg1_lt_action S q)).trans hwindow.nextActionInHorizon
  refine activeDomain_of_retainedAtDomainRead S ?_
  intro w hw
  have hdom : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2 =
      S.hc.Γ_neg1 S.E.Δ (q + 1) :=
    (gammaNeg1_eq_domain_g2_succ S q).symm
  rw [hdom]
  have hconf : P.erase ∈ (rho.storeBeforeTime S w (S.a q)).T := by
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, Setup.a, Protocol.a_eq_confirmation_time] using
      hwindow.proposalAtConfirmation w hw
  have hproc : P.erase ∈
      (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q + 1))).T :=
    seedStore_T_subset S adm.toNamedScheduleWellFormed w hcutLo hconf
  exact frontierBlock_filtered_of_gateOff S adm hsb hw hcutHor hproc rfl
    hPrun hheight hM (hframe w hw).1 (hframe w hw).2

/-- The previous round of a carrier is inside the window, with bare `Nat`
binders. -/
private theorem seedPrevRound_nat {a b : Nat} (h : a + 1 + 2 ≤ b) :
    a + 1 ≤ b - 1 := by
  omega

/-- The previous round of a carrier is inside the horizon, with bare `Nat`
binders. -/
private theorem seedPrevRoundEnd_nat {b e : Nat} (h : b + 1 ≤ e) :
    b - 1 ≤ e := by
  omega

/-- **The gate-off opening lifecycle at a round ceiling**, from the one pinned
input and the two the seed supplies itself. -/
private theorem seedOpeningLifecycle_of_inputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {C P : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho q)
    (hceiling : RoundCeilingAt S rho M q C)
    (hwindow : NamedGateOffOpeningWindowAt S rho M q P)
    (hprevFrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M)
    (hframe : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q + 1))).h_max = M ∧
        (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q + 1))).h_j + 2 ≤ M) :
    GateOffOpeningAdoption S rho q :=
  gateOff_openingLifecycle_of_roundCeiling S adm hcom hfb hcarrier hceiling
    hwindow hprevFrontier
    (seedOpeningProposal_nextActiveDomain S adm hfb hcarrier hwindow hframe)

/-! ## The open lag of the ceiling producers -/


/-- One round of slack turns a post-GST action into a post-`gstLagged` action:
the action time advances by exactly `4ΔR` per round and `gstLagged` is
`t_GST + 4ΔR` because `readyLag = 1`. -/
private theorem gstLagged_le_a_succ (S : Setup V) {r : Round}
    (hgst : S.E.t_GST ≤ S.a r) : gstLagged S ≤ S.a (r + 1) := by
  have hstep : S.a (r + 1) = S.a r + 4 * S.E.Δ * (S.hc.R : Nat) := by
    show S.hc.a S.E.Δ (r + 1) = S.hc.a S.E.Δ r + 4 * S.E.Δ * (S.hc.R : Nat)
    unfold Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  have hlag : gstLagged S = S.E.t_GST + 4 * S.E.Δ * (S.hc.R : Nat) := by
    simp [gstLagged, readyLag]
  rw [hstep, hlag]
  exact Int.add_le_add_right hgst _

/-! ## The seed's leaves -/










/-- The `M - 1` case of the seed run, with everything the run has in hand at
that point: the carrier round, its ceiling and opening window, the gate-off
time window of the whole run, and the budget left for two more carriers. -/
def SeedPredCloserFrom
    (S : Setup V) (rho : Run V) (r0 gap : Round) (delayExtra : Nat := 0) : Prop :=
  ∀ (base q : Round) (Cq P : NamedBlock V), r0 ≤ base → base + 4 ≤ q →
    q + 2 * gap + 6 + 2 * delayExtra ≤ base + seedLag gap delayExtra →
    S.E.t_GST ≤ S.a base →
    S.a (base + seedLag gap delayExtra) ≤ rho.horizon →
    honestHMaxAt S rho (S.a (base + seedLag gap delayExtra)) ≤
      honestHMaxAt S rho (S.a base) →
    2 ≤ honestHMaxAt S rho (S.a base) →
    (∀ read : Time, S.a (base + 1) ≤ read →
      read ≤ S.a (base + seedLag gap delayExtra) → ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤
            honestHMaxAt S rho (S.a base) ∧
          (rho.storeBeforeTime S w read).h_max =
            honestHMaxAt S rho (S.a base)) →
    SeedRoundGradedAt S rho q →
    ProposerCarrierAt S rho q →
    RoundCeilingAt S rho (honestHMaxAt S rho (S.a base)) q Cq →
    NamedGateOffOpeningWindowAt S rho (honestHMaxAt S rho (S.a base)) q P →
    (Protocol.derive_named S.E S.cfg P).h =
        honestHMaxAt S rho (S.a base) - 1 →
    HeightProgressSeedOutcome (delayExtra := delayExtra) S rho (honestHMaxAt S rho (S.a base)) base
      (base + seedLag gap delayExtra)




/-- The gate-off frame of a stretch of the run, in the shape the seed's two
producer obligations consume it: every honest read from the action of `lo` to
the action of `hi` has exact frontier `M` and the gate off. -/
def SeedGateOffFrameAt
    (S : Setup V) (rho : Run V) (M : Height) (lo hi : Round) : Prop :=
  ∀ read : Time, S.a lo ≤ read → read ≤ S.a hi → ∀ w ∈ rho.honest,
    (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
      (rho.storeBeforeTime S w read).h_max = M

/-! ## Leaf (c) at an exact-height opening -/



/-- Round arithmetic of leaf (c), with bare `Nat` binders. -/
private theorem seedLeafRounds_nat {base entry q endpoint : Nat}
    (hbe : base + 1 ≤ entry) (heq : entry + 2 + delayExtra ≤ q) (hq : q ≤ endpoint) :
    0 < entry ∧ 0 < q ∧ entry ≤ endpoint ∧ entry + 1 ≤ endpoint ∧
      q - 1 ≤ endpoint ∧ base + 1 ≤ entry + 1 ∧ base + 1 ≤ q - 1 ∧
        entry + 1 ≤ q - 1 ∧ base ≤ entry := by
  omega

/-- **Leaf (c).** An honest opening proposal at the exact frontier height is
the seed's third outcome, with the grade taken at a carrier round at least two
rounds later. -/
private theorem seedExactOpening_outcome
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {base endpoint entry q : Round} {C Pentry Pq : NamedBlock V}
    (hM : 2 ≤ M)
    (hbaseEntry : base + 1 ≤ entry)
    (hentryQ : entry + 2 + delayExtra ≤ q)
    (hqEnd : q ≤ endpoint)
    (hpostBase : S.E.t_GST ≤ S.a base)
    (hhorEnd : S.a endpoint ≤ rho.horizon)
    (hcap : honestHMaxAt S rho (S.a endpoint) ≤ M)
    (hwindow : ∀ read : Time, S.a (base + 1) ≤ read → read ≤ S.a endpoint →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M)
    (hcarrierEntry : ProposerCarrierAt S rho entry)
    (hcarrier : ProposerCarrierAt S rho q)
    (hceiling : RoundCeilingAt S rho M q C)
    (hPentry : proposedBlockAt S rho (S.hc.opening_slot entry) = some Pentry)
    (hPq : proposedBlockAt S rho (S.hc.opening_slot q) = some Pq)
    (hgradeNext : NamedGradeFormsAt S rho (entry + 1) Pentry.erase)
    (hexact : (Protocol.derive_named S.E S.cfg Pentry).h = M) :
    HeightProgressSeedOutcome (delayExtra := delayExtra) S rho M base endpoint := by
  obtain ⟨hentryPos, hqPos, hentryEnd, hentry1End, hqPredEnd, hbaseEntry1,
    hbaseQPred, hspan, hbaseEntry'⟩ :=
    seedLeafRounds_nat hbaseEntry hentryQ hqEnd
  have hM1 : 1 ≤ M := (by decide : (1 : Nat) ≤ 2).trans hM
  have hhorAt : ∀ {k : Round}, k ≤ endpoint → S.a k ≤ rho.horizon := by
    intro k hk
    exact (Assembly.a_mono S hk).trans hhorEnd
  have hopenPos : 0 < S.hc.opening_slot entry := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hentryPos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hproposalHorEntry : Protocol.proposal_time S.E
      (S.hc.opening_slot entry) ≤ rho.horizon := by
    refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact hhorAt hentryEnd
  have hPrun : RunBlock S rho Pentry :=
    Protocol.proposedBlock_runBlock S adm hopenPos hcarrierEntry.1
      hproposalHorEntry hPentry
  have hactionRead : ∀ k : Round, entry + 1 ≤ k → k ≤ q - 1 →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w (S.a k)).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w (S.a k)).h_max = M := by
    intro k hklo hkhi w hw
    exact hwindow (S.a k) (Assembly.a_mono S (hbaseEntry1.trans hklo))
      (Assembly.a_mono S (hkhi.trans hqPredEnd)) w hw
  have hpostEntryNext : S.E.t_GST ≤ S.a (entry + 1) :=
    hpostBase.trans (Assembly.a_mono S (hbaseEntry'.trans (Nat.le_succ _)))
  have hopenPosQ : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hqPos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hproposalHorQ : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon := by
    refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact hhorAt hqEnd
  have hparentCap : (Protocol.derive_named S.E S.cfg Pq.parent).h ≤ M := by
    have hupper := honestProposedBlock_height_le_honestHMaxAt
      S adm hopenPosQ hcarrier.1 hproposalHorQ hPq
    refine le_trans (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
      (namedProposalParent_preceq S rho _ hPq)) ?_
    refine hupper.trans ?_
    refine le_trans (honestHMaxAt_mono S adm.toNamedScheduleWellFormed ?_) hcap
    refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact Assembly.a_mono S hqEnd
  have hactionFrontier : ∀ k, entry + 1 ≤ k → k ≤ q - 1 → ∀ w ∈ rho.honest,
      (actionStoreAt S rho w k).h_max = M := by
    intro k hklo hkhi w hw
    exact (hactionRead k hklo hkhi w hw).2
  have hactionGate : ∀ k, entry + 1 ≤ k → k ≤ q - 1 → ∀ w ∈ rho.honest,
      (actionStoreAt S rho w k).h_j + 2 ≤ M := by
    intro k hklo hkhi w hw
    exact (hactionRead k hklo hkhi w hw).1
  have hframeRead : ∀ read : Time, S.a (entry + 1) ≤ read →
      read ≤ S.a (q - 1) → ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M := by
    intro read hlo hhi w hw
    exact hwindow read ((Assembly.a_mono S hbaseEntry1).trans hlo)
      (hhi.trans (Assembly.a_mono S hqPredEnd)) w hw
  have hanchors : ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (q - 1))
        (proposedParent S rho (S.hc.opening_slot q)) := by
    have haligned := openingAnchorsAligned_of_roundCeiling
      S adm hcom hcarrier hceiling
    exact haligned.previousCarriersBelowParent
  obtain ⟨hforms, hbelow, hheights⟩ := seedExactOpening_gradePackage
    S adm hcom hfb hPentry hPq hcarrier hceiling hgradeNext hPrun hexact hM1
    ((Nat.le_add_right _ delayExtra).trans hentryQ)
    hpostEntryNext (hhorAt hqPredEnd) hactionFrontier hactionGate
    (namedGradeFormsAt_persists_through_gateOffActionWindow S adm hfb
      (r0 := entry + 1) (q := q - 1) (Nat.succ_pos entry) hgradeNext hPrun
      (by rw [hexact]; exact Nat.sub_le M 1) hM1 hpostEntryNext
      (hhorAt hqPredEnd)
      (fun read hlo hhi w hw =>
        ⟨(hframeRead read hlo hhi w hw).2, (hframeRead read hlo hhi w hw).1⟩)
      (q - 1) hspan (le_refl _))
    hanchors
    hparentCap
  exact Or.inr (Or.inr ⟨entry, q, Pentry, Pq, Pq.parent, hbaseEntry, hentryQ,
    hqEnd, hcarrier, hPentry, hforms, hPrun, hexact, hPq,
    namedProposal_parent?_eq S rho _ hPq, hbelow, hheights⟩)

/-! ## The `M - 1` case is closed by the timeout-delay bound -/

/-- Round arithmetic of the two extra carriers, with bare `Nat` binders. -/
private theorem seedCloserSelectRound4_nat {base gap q endpoint delayExtra : Nat}
    (hbaseq : base + 4 ≤ q)
    (hbudget : q + 2 * gap + 6 + 2 * delayExtra ≤ endpoint) :
    base < q + 2 + delayExtra ∧
      q + 2 + delayExtra + gap ≤ endpoint := by
  omega

private theorem seedCloserSelectRound5_nat {base gap q q4 endpoint delayExtra : Nat}
    (hbaseq : base + 4 ≤ q)
    (hbudget : q + 2 * gap + 6 + 2 * delayExtra ≤ endpoint)
    (hq4lo : q + 2 + delayExtra ≤ q4)
    (hq4hi : q4 ≤ q + 2 + delayExtra + gap) :
    base < q4 + 2 + delayExtra ∧
      q4 + 2 + delayExtra + gap ≤ endpoint := by
  omega

private theorem seedAdoptionSelectRound1_nat {base gap delayExtra : Nat} :
    base < base + 4 ∧
      base + 4 + gap ≤ base + (4 * gap + 12 + 2 * delayExtra) := by
  omega

private theorem seedAdoptionSelectRound2_nat {base gap q1 delayExtra : Nat}
    (hq1lo : base + 4 ≤ q1)
    (hq1hi : q1 ≤ base + 4 + gap) :
    base < q1 + 2 ∧
      q1 + 2 + gap ≤ base + (4 * gap + 12 + 2 * delayExtra) := by
  omega

private theorem seedAdoptionSelectRound3_nat {base gap q1 q2 delayExtra : Nat}
    (hq1lo : base + 4 ≤ q1)
    (hq1hi : q1 ≤ base + 4 + gap)
    (hq2lo : q1 + 2 ≤ q2)
    (hq2hi : q2 ≤ q1 + 2 + gap) :
    base < q2 + 2 + delayExtra ∧
      q2 + 2 + delayExtra + gap ≤ base + (4 * gap + 12 + 2 * delayExtra) := by
  omega

private theorem seedCloserRounds_nat {base gap q q4 q5 endpoint : Nat}
    (hbaseq : base + 4 ≤ q)
    (hbudget : q + 2 * gap + 6 + 2 * delayExtra ≤ endpoint)
    (h4lo : q + 2 + delayExtra ≤ q4) (h4hi : q4 ≤ q + 2 + delayExtra + gap)
    (h5lo : q4 + 2 + delayExtra ≤ q5) (h5hi : q5 ≤ q4 + 2 + delayExtra + gap) :
    base + 2 ≤ q ∧ q ≤ q4 ∧ q ≤ q5 ∧ q4 + 2 ≤ endpoint ∧
      q4 + 1 ≤ endpoint ∧ q4 ≤ endpoint ∧ q5 + 2 ≤ endpoint ∧
        q5 ≤ endpoint ∧ q4 - 1 ≤ endpoint ∧ base + 1 + 2 ≤ q4 ∧
          base + 1 ≤ q4 ∧ q + 1 ≤ q4 - 1 ∧ base + 1 ≤ q + 1 ∧
            q + 2 + delayExtra ≤ q4 ∧ q4 + 2 + delayExtra ≤ q5 ∧ base ≤ q := by
  omega

/-- The closer's existing window starts before both predecessor reads. -/
private theorem seedSourceFrameRounds_nat {base q q' : Nat}
    (hbase : base + 4 ≤ q) (hnext : q ≤ q') : base + 1 ≤ q' - 2 := by
  omega

/-- **The `M - 1` opening case, discharged.** Two more carrier rounds are
inside the seed's budget; the first of them has its opening proposal at the
exact frontier height by `seedPredOpening_exactAtNextCarrier`, and leaf (c)
then closes at the second. -/
theorem seedPredCloser_of_timeoutDelay
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    (hdelayBound : TimeoutDelayBound S delayExtra)
    (hpromotion : SeedPredPromotionInputs (delayExtra := delayExtra) S rho)
    {r0 gap : Round}
    (hrec : MultiProposerRecurrence S rho gap) :
    SeedPredCloserFrom (delayExtra := delayExtra) S rho r0 gap := by
  intro base q Cq Pq _hr0 hbaseq hbudget hpostBase hhorEnd hcap hM hgateWindow
    hgradedQ hcarrier hceiling hwindowQ hpred
  set M : Height := honestHMaxAt S rho (S.a base) with hMdef
  set endpoint : Round := base + seedLag gap delayExtra with hendpoint
  have hselect (k : Round) (hbk : base < k) (hk : k + gap ≤ endpoint) :
      ∃ c : Round, k ≤ c ∧ c ≤ k + gap ∧ ProposerCarrierAt S rho c :=
    hrec k
      (hpostBase.trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (action_add_delta_le_openingProposal_of_round_lt S hbk)))
      ((openingProposal_window_le_action S k gap).trans
        ((Assembly.a_mono S hk).trans hhorEnd))
  obtain ⟨h4base, h4end⟩ := seedCloserSelectRound4_nat hbaseq hbudget
  obtain ⟨q4, hq4lo, hq4hi, hcar4⟩ := hselect (q + 2 + delayExtra)
    h4base h4end
  obtain ⟨h5base, h5end⟩ := seedCloserSelectRound5_nat hbaseq hbudget hq4lo hq4hi
  obtain ⟨q5, hq5lo, hq5hi, hcar5⟩ := hselect (q4 + 2 + delayExtra)
    h5base h5end
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,
    m16⟩ :=
    seedCloserRounds_nat hbaseq hbudget hq4lo hq4hi hq5lo hq5hi
  obtain ⟨P4, hP4⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q4)
  obtain ⟨P5, hP5⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q5)
  have hpostBase1 : S.E.t_GST ≤ S.a (base + 1) :=
    hpostBase.trans (Assembly.a_mono S (Nat.le_succ base))
  have hpostBase1L : gstLagged S ≤ S.a (base + 1) := gstLagged_le_a_succ S hpostBase
  have hhorAt : ∀ {k : Round}, k ≤ endpoint → S.a k ≤ rho.horizon := by
    intro k hk
    exact (Assembly.a_mono S hk).trans hhorEnd
  have hwindowAt : ∀ (k : Round), k ≤ endpoint →
      ∀ read : Time, S.a (base + 1) ≤ read → read ≤ S.a k →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M := by
    intro k hk read hlo hhi w hw
    exact hgateWindow read hlo (hhi.trans (Assembly.a_mono S hk)) w hw
  -- the ceilings of the two extra carrier rounds
  obtain ⟨B4, hceil4, -⟩ := roundCeiling_through_of_window S adm hcom hfb
    (base := base + 1) (first := q) (last := q4) (C := Cq)
    hpostBase1L m1 (hhorAt m4)
    (fun read hlo hhi w hw => hwindowAt (q4 + 2) m4 read hlo hhi w hw)
    hceiling q4 m2 (le_refl _)
  obtain ⟨B5, hceil5, -⟩ := roundCeiling_through_of_window S adm hcom hfb
    (base := base + 1) (first := q) (last := q5) (C := Cq)
    hpostBase1L m1 (hhorAt m7)
    (fun read hlo hhi w hw => hwindowAt (q5 + 2) m7 read hlo hhi w hw)
    hceiling q5 m3 (le_refl _)
  -- the opening window of the first extra carrier round
  have hwindow4 : NamedGateOffOpeningWindowAt S rho M q4 P4 :=
    gateOffOpeningWindow_of_window S adm hfb (base := base + 1) (q := q4)
      hpostBase1 m10 (hhorAt m5) hcar4.1 hP4
      (fun read hlo hhi w hw => hwindowAt (q4 + 1) m5 read hlo hhi w hw)
  -- the parent cap at the first extra carrier round
  have hparentCap4 : ∀ Parent : NamedBlock V,
      NamedBlock.parent? P4 = some Parent →
      (Protocol.derive_named S.E S.cfg Parent).h ≤ M := by
    intro Parent hParent
    have hParentEq : Parent = P4.parent := by
      have hp := namedProposal_parent?_eq S rho (S.hc.opening_slot q4) hP4
      rw [hp] at hParent
      exact (Option.some.inj hParent).symm
    subst hParentEq
    have hopenPos4 : 0 < S.hc.opening_slot q4 := by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos hwindow4.roundPositive
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have hproposalHor4 : Protocol.proposal_time S.E
        (S.hc.opening_slot q4) ≤ rho.horizon := by
      refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
      rw [← Protocol.a_eq_confirmation_time]
      exact hhorAt m6
    have hupper := honestProposedBlock_height_le_honestHMaxAt
      S adm hopenPos4 hcar4.1 hproposalHor4 hP4
    refine le_trans (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
      (namedProposalParent_preceq S rho _ hP4)) ?_
    refine hupper.trans ?_
    refine le_trans (honestHMaxAt_mono S adm.toNamedScheduleWellFormed ?_) hcap
    refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact Assembly.a_mono S m6
  -- the persisted grade and retained action read at the immediately preceding
  -- round. These are the local inputs of the fresh-row coverage route.
  have hqNextEnd : q + 1 ≤ endpoint := (Nat.add_le_add_right m2 1).trans m5
  have hbasePred : base + 1 ≤ q - 1 := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.add_assoc] using m1
  have hprevQ : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M := by
    intro u hu
    exact (hwindowAt (q + 1) hqNextEnd (S.a (q - 1))
      (Assembly.a_mono S hbasePred)
      (Assembly.a_mono S ((Nat.sub_le q 1).trans (Nat.le_succ q))) u hu).2
  have hbaseQ : base + 1 ≤ q := hbasePred.trans (Nat.sub_le q 1)
  have hnextQ := seedOpeningProposal_nextActiveDomain S adm hfb hcarrier hwindowQ
    (fun w hw => by
      have hframeQ := hwindowAt (q + 1) hqNextEnd
        (S.hc.Γ_neg1 S.E.Δ (q + 1))
        ((Assembly.a_mono S hbaseQ).trans
          ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
            (action_add_delta_le_next_Γ_neg1 S q)))
        (le_of_lt (next_Γ_neg1_lt_action S q)) w hw
      exact ⟨hframeQ.2, hframeQ.1⟩)
  have hpacketQ := seedLifecyclePacket_of_roundCeiling
    S adm hcom hfb hcarrier hceiling hwindowQ hprevQ hnextQ
  have hM1 : 1 ≤ M := (by decide : (1 : Nat) ≤ 2).trans hM
  have hqPlusTwo : q + 2 ≤ q4 :=
    (Nat.le_add_right (q + 2) delayExtra).trans m14
  have hframePromotion : ∀ read : Time, S.a (q + 1) ≤ read →
      read ≤ S.a (q4 - 1) → ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M := by
    intro read hlo hhi w hw
    exact hwindowAt (q4 - 1) m9 read
      ((Assembly.a_mono S m13).trans hlo) hhi w hw
  have hpostQ1 : S.E.t_GST ≤ S.a (q + 1) :=
    hpostBase.trans (Assembly.a_mono S (m16.trans (Nat.le_succ q)))
  have hqPred : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hwindowQ.roundPositive)
  have hgradeNextQ : NamedGradeFormsAt S rho (q + 1) Pq.erase := by
    simpa only [hqPred] using hpacketQ.lifecycle.gradeNext
  have hopening := seedOpeningProposal_preceq_nextOpeningParent_of_grade
    (M := M) (q := q) (q' := q4) (C' := B4) (B := Pq) (B' := P4)
    S adm hcom hfb hwindow4 hcar4 hceil4 hgradeNextQ
      hpacketQ.lifecycle.runBlock hpred hM1 hqPlusTwo
      (hpostBase.trans (Assembly.a_mono S (m16.trans (Nat.le_succ q))))
      (hhorAt m9) hframePromotion
  have hformsAtPromotion := namedGradeFormsAt_persists_through_gateOffActionWindow
    S adm hfb (Nat.succ_pos q) (r0 := q + 1) (q := q4 - 1) hgradeNextQ
    hpacketQ.lifecycle.runBlock (by rw [hpred])
    hM1 hpostQ1 (hhorAt m9)
    (fun read hlo hhi w hw =>
      let h := hframePromotion read hlo hhi w hw
      ⟨h.2, h.1⟩)
  have hformsPromotion : NamedGradeFormsAt S rho (q4 - 1) Pq.erase :=
    (hformsAtPromotion (q4 - 1) m12 (le_refl _)).1
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hwindowPromotion : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q4 - 1)) Pq.erase := by
    intro w hw
    have hprocessed := namedGradeFormsAt_processedAtRead_of_action_le
      S adm hformsPromotion hw (le_refl _)
    have hframeAtQ4 := hframePromotion (S.a (q4 - 1))
      (Assembly.a_mono S m12) le_rfl w hw
    have hfiltered := frontierBlock_filtered_of_gateOff S adm hsb hw
      (hhorAt m9) hprocessed rfl hpacketQ.lifecycle.runBlock
      (by rw [hpred]) hM1 hframeAtQ4.2 hframeAtQ4.1
    simpa only [FinalityFilterRetainedAtRead] using hfiltered
  have hbaseSourceFrame : base + 1 ≤ q4 - 2 :=
    seedSourceFrameRounds_nat hbaseq m2
  have hpromotionAt := hpromotion M q q4 Cq B4 Pq P4 hM hgradedQ hcarrier
    hceiling hwindowQ hpred m14 hcar4 hceil4 hwindow4
    (hpostBase1.trans (Assembly.a_mono S hbaseSourceFrame)) (hhorAt m6)
    (fun read hlo hhi w hw => hwindowAt q4 m6 read
      ((Assembly.a_mono S hbaseSourceFrame).trans hlo) hhi w hw)
    hpacketQ.lifecycle.runBlock hformsPromotion hwindowPromotion
  have hq4PredPos : 0 < q4 - 1 := (Nat.succ_pos q).trans_le m12
  have hbaseQ4Pred : base + 1 ≤ q4 - 1 := m13.trans m12
  have hq4PredSucc : q4 - 1 + 1 = q4 :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hwindow4.roundPositive)
  have hpostQ4Pred : S.E.t_GST ≤ S.a (q4 - 1) :=
    hpostBase1.trans (Assembly.a_mono S hbaseQ4Pred)
  have hgateQ4Pred : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a (q4 - 1))).h_j + 2 ≤ M := by
    intro w hw
    exact (hwindowAt (q4 - 1) m9 (S.a (q4 - 1))
      (Assembly.a_mono S hbaseQ4Pred) le_rfl w hw).1
  have hparentQ4 : P4.parent? = some P4.parent :=
    namedProposal_parent?_eq S rho _ hP4
  have hbelowPq : NamedBlock.Preceq Pq P4.parent :=
    hopening P4.parent hparentQ4
  have hparentCap4' : (Protocol.derive_named S.E S.cfg P4.parent).h ≤ M :=
    hparentCap4 P4.parent hparentQ4
  have hproposalHor4 : Protocol.proposal_time S.E
      (S.hc.opening_slot q4) ≤ rho.horizon := by
    refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact hhorAt m6
  have hmatureOfParentPred :
      (Protocol.derive_named S.E S.cfg P4.parent).h = M - 1 →
        ProposalTimeoutMatureAt S rho (S.hc.opening_slot q4) := by
    intro hparentPred
    have hsame : (Protocol.derive_named S.E S.cfg Pq).h =
        (Protocol.derive_named S.E S.cfg P4.parent).h := by
      rw [hpred, hparentPred]
    exact laterOpening_timeoutMature_of_sameHeight S adm hdelayBound
      hwindowQ.roundPositive m14 hwindowQ.proposal hwindow4.proposal
      hparentQ4 hbelowPq hsame.symm
  -- The source-height callback is the only remaining local producer input.
  rcases seedFreshOpening_promotion_of_persistedGrade S adm hfb hM hq4PredPos
      hpostQ4Pred hpacketQ.lifecycle.runBlock hpred hformsPromotion
      hwindowPromotion hpromotionAt.sourceHeightLeNextOpeningParent hgateQ4Pred
      (by simpa only [hq4PredSucc] using hP4) hbelowPq hparentCap4'
      (by simpa only [hq4PredSucc] using hcar4.1)
      (by simpa only [hq4PredSucc] using hproposalHor4)
      (by simpa only [hq4PredSucc] using hmatureOfParentPred) with
    hexact4 | hrise4
  · -- leaf (c) at the two extra carriers
    have hcutFrame4 : ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q4 + 1))).h_max = M ∧
          (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q4 + 1))).h_j + 2 ≤ M := by
      intro w hw
      have h := hwindowAt (q4 + 1) m5 (S.hc.Γ_neg1 S.E.Δ (q4 + 1))
        ((Assembly.a_mono S m11).trans
          (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
            (action_add_delta_le_next_Γ_neg1 S q4)))
        (le_of_lt (next_Γ_neg1_lt_action S q4)) w hw
      exact ⟨h.2, h.1⟩
    have hprevFrontier4 : ∀ u ∈ rho.honest,
        (rho.storeBeforeTime S u (S.a (q4 - 1))).h_max = M := by
      intro u hu
      exact (hwindowAt (q4 - 1) m9 (S.a (q4 - 1))
        (Assembly.a_mono S (seedPrevRound_nat m10)) le_rfl u hu).2
    have hadopt4 := seedOpeningLifecycle_of_inputs S adm hcom hfb hcar4 hceil4
      hwindow4 hprevFrontier4
      hcutFrame4
    exact seedExactOpening_outcome S adm hcom hfb hM m11 m15 m8 hpostBase
      hhorEnd hcap hgateWindow hcar4 hcar5 hceil5 hP4 hP5
      (hadopt4.gradeNext P4 hP4) hexact4
  · -- the public frontier rose at the later proposal read
    rw [hq4PredSucc] at hrise4
    refine Or.inl (lt_of_lt_of_le hrise4 ?_)
    refine honestHMaxAt_mono S adm.toNamedScheduleWellFormed ?_
    refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact Assembly.a_mono S m6



/-! ## The seed run -/


set_option maxHeartbeats 1000000 in
-- three carrier rounds, two ceilings carried through the window, one opening
-- window and the three-way height split elaborate in one tactic block










/-! ## The seed on one premise about carriers -/

/-- The last slot of a round is at or before the next round's opening. -/
private theorem seedLastSlot_le_nextOpening (S : Setup V) (q : Round) :
    seedRoundLastSlot S q ≤ S.hc.opening_slot (q + 1) :=
  Nat.sub_le _ 1


/-- Round arithmetic of the two-cover step, with bare `Nat` binders. -/
private theorem seedCoverRounds_nat {q : Nat} (h : 2 ≤ q) :
    q - 2 + 1 = q - 1 ∧ q - 1 + 1 = q ∧ q - 2 ≤ q - 1 ∧ q - 1 ≤ q ∧
      q - 2 ≤ q := by
  omega


/-- **The seed's grade obligation at a round, from the band-carrier covers
of the two rounds below it.**

The cover gives the band grade one round later
(`seedBandGrade_of_bandCarrierCover`), the band grade at rounds `q - 1` and `q`
is the selected grade at the round-`q` action stores
(`seedRoundGraded_of_bandGrade`). -/
private theorem seedGradedAndClear_of_covers
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hq2 : 2 ≤ q)
    (hpostPrev : S.E.t_GST ≤ S.a (q - 2))
    (hhor : S.a (q + 1) ≤ rho.horizon)
    (hframe : SeedGateOffFrameAt S rho M (q - 2) (q + 1))
    (hcoverPrev : SeedBandCarrierCoverAt S rho M (q - 2))
    (hcoverCur : SeedBandCarrierCoverAt S rho M (q - 1)) :
    SeedRoundGradedAt S rho q := by
  obtain ⟨hstep2, hstep1, hle21, hle1, hle2⟩ := seedCoverRounds_nat hq2
  have hhorQ : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hhor
  have hhorPred : S.a (q - 1) ≤ rho.horizon :=
    (Assembly.a_mono S hle1).trans hhorQ
  have hframeAt : ∀ {k : Round}, q - 2 ≤ k → k ≤ q + 1 →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w (S.a k)).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w (S.a k)).h_max = M := by
    intro k hlo hhi w hw
    exact hframe (S.a k) (Assembly.a_mono S hlo) (Assembly.a_mono S hhi) w hw
  have hrelay : ∀ {k : Round}, q - 2 ≤ k → k + 1 ≤ q + 1 →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w (S.a k + S.E.Δ)).h_max = M ∧
          (rho.storeBeforeTime S w (S.a k + S.E.Δ)).h_j + 2 ≤ M := by
    intro k hlo hhi w hw
    have hstep : S.a k + S.E.Δ ≤ S.a (k + 1) :=
      le_trans (action_add_delta_le_next_Γ_neg1 S k)
        (le_of_lt (next_Γ_neg1_lt_action S k))
    have := hframe (S.a k + S.E.Δ)
      (le_trans (Assembly.a_mono S hlo)
        (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)))
      (hstep.trans (Assembly.a_mono S hhi)) w hw
    exact ⟨this.2, this.1⟩
  have hgradePrev : SeedRoundBandGradeAt S rho M (q - 1) := by
    have h := seedBandGrade_of_bandCarrierCover S adm hcom hfb
      (M := M) (q := q - 2) hpostPrev
      (by rw [hstep2]; exact hhorPred)
      (hrelay (le_refl _) (by rw [hstep2]; exact hle1.trans (Nat.le_succ q)))
      (fun w hw => by
        rw [hstep2]
        exact ⟨(hframeAt hle21 (hle1.trans (Nat.le_succ q)) w hw).2,
          (hframeAt hle21 (hle1.trans (Nat.le_succ q)) w hw).1⟩)
      hcoverPrev
    rwa [hstep2] at h
  have hgradeCur : SeedRoundBandGradeAt S rho M q := by
    have h := seedBandGrade_of_bandCarrierCover S adm hcom hfb
      (M := M) (q := q - 1)
      (hpostPrev.trans (Assembly.a_mono S hle21))
      (by rw [hstep1]; exact hhorQ)
      (hrelay hle21 (by rw [hstep1]; exact Nat.le_succ q))
      (fun w hw => by
        rw [hstep1]
        exact ⟨(hframeAt hle2 (Nat.le_succ q) w hw).2,
          (hframeAt hle2 (Nat.le_succ q) w hw).1⟩)
      hcoverCur
    rwa [hstep1] at h
  -- the selected grade at the action stores of rounds `q - 1` and `q`
  have hframeStore : ∀ {k : Round}, q - 2 ≤ k → k ≤ q + 1 →
      ∀ w ∈ rho.honest,
        S.a k ≤ rho.horizon ∧
          (healStoreAt S rho w k).h_max = M ∧
            (healStoreAt S rho w k).h_j + 2 ≤ M := by
    intro k hlo hhi w hw
    have hread := hframe (S.a k) (Assembly.a_mono S hlo)
      (Assembly.a_mono S hhi) w hw
    exact ⟨(Assembly.a_mono S hhi).trans hhor,
      by simpa only [healStoreAt] using hread.2,
      by simpa only [healStoreAt] using hread.1⟩
  exact seedRoundGraded_of_bandGrade S adm hfb
    (hframeStore hle21 (hle1.trans (Nat.le_succ q)))
    (hframeStore hle2 (Nat.le_succ q)) hgradePrev hgradeCur

/-- Round arithmetic of the carrier-adoption seed, with bare `Nat` binders. -/
private theorem seedAdoptionRounds_nat {base gap q1 q2 q3 : Nat}
    (h1lo : base + 4 ≤ q1) (h1hi : q1 ≤ base + 4 + gap)
    (h2lo : q1 + 2 ≤ q2) (h2hi : q2 ≤ q1 + 2 + gap)
    (h3lo : q2 + 2 + delayExtra ≤ q3) (h3hi : q3 ≤ q2 + 2 + delayExtra + gap) :
    q1 + 2 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧ q2 + 2 ≤ base + (4 * gap + 12 + 2 *
      delayExtra) ∧
      q3 + 2 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧ q3 ≤ base + (4 * gap + 12 + 2 * delayExtra)
        ∧
        q2 + 1 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧ q3 - 1 ≤ base + (4 * gap + 12 + 2 *
          delayExtra) ∧
          base + 1 + 1 ≤ q1 ∧ base + 1 + 1 ≤ q1 + 1 ∧
            q1 + 1 ≤ q2 ∧ q1 + 1 ≤ q3 ∧ base + 1 + 2 ≤ q2 ∧
              base + 1 ≤ q2 ∧ base + 4 ≤ q2 ∧ q2 + 2 + delayExtra ≤ q3 ∧
                q2 + 1 ≤ q3 - 1 ∧ 0 < q2 ∧ base ≤ q1 ∧ base ≤ q2 ∧
                  base + 1 ≤ q1 + 2 ∧ base + 1 ≤ q2 + 2 ∧
                    base + 1 ≤ q3 + 2 ∧ base + 1 ≤ q2 + 1 ∧
                      q2 + 2 * gap + 6 + 2 * delayExtra ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧
                        q1 + 1 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧
                          q2 + 1 ≤ base + (4 * gap + 12 + 2 * delayExtra) ∧
                            base + 1 ≤ q1 - 2 ∧ base + 1 ≤ q2 - 2 ∧
                              2 ≤ q2 ∧ q1 ≤ q2 - 2 ∧ q1 ≤ q2 - 1 ∧
                                q2 - 2 ≤ q2 + 1 ∧ q2 - 1 ≤ q2 + 1 := by
  omega

set_option maxHeartbeats 1000000 in
/-- **The gate-off height-progress seed**, from the carrier-round adoption
witness `hadopt` in place of the graded/clear premises. -/
theorem heightProgressSeedFrom_of_carrierAdoption
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hfb : BelowOneThird S rho.honest)
    {r0 gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (_hpost : S.E.t_GST ≤ S.a r0)
    (hadopt : ∀ (M : Height) (base q : Round), r0 ≤ base → base + 4 ≤ q →
      S.E.t_GST ≤ S.a base → S.a (q + 2) ≤ rho.horizon →
      SeedGateOffFrameAt S rho M (base + 1) (q + 2) → ProposerCarrierAt S rho q →
      SeedBoundaryAdoptionAt S rho M q ∧ SeedBandCarrierCoverAt S rho M q)
    (hclose : SeedPredCloserFrom (delayExtra := delayExtra) S rho r0 gap) :
    HeightProgressSeedFrom (delayExtra := delayExtra) S rho r0 gap := by
  intro base hr0 hpostBase hfrontierBase hgateBase hhorEnd
  set M : Height := honestHMaxAt S rho (S.a base) with hM
  set endpoint : Round := base + seedLag gap delayExtra with hendpoint
  by_cases hrise : M < honestHMaxAt S rho (S.a endpoint)
  · exact Or.inl hrise
  have hcap : honestHMaxAt S rho (S.a endpoint) ≤ M := Nat.le_of_not_gt hrise
  -- an honest validator exists, and gate off forces `2 ≤ M`
  have hpositive : 0 < ((S.E.committee 0) ∩ rho.honest).card := by
    have hc := hcom 0
    omega
  obtain ⟨x0, hx0mem⟩ := Finset.card_pos.mp hpositive
  have hx0 : x0 ∈ rho.honest := (Finset.mem_inter.mp hx0mem).2
  have h2 : 2 ≤ M :=
    (Nat.le_add_left 2 (rho.storeBeforeTime S x0 (S.a base)).h_j).trans
      (hgateBase x0 hx0)
  rcases seedBaseFixedRoot_or_gateOffWindow S adm hfb (M := M) (base := base)
      (endpoint := endpoint) rfl hpostBase h2 hcap hhorEnd with
    hfix | hgateWindow
  · obtain ⟨u, hu, read, hread1, hread2, hfixRead⟩ := hfix
    exact Or.inr (Or.inl ⟨u, read, hu, hread1, hread2, hfixRead⟩)
  -- the three carrier rounds
  have hselect (k : Round) (hbk : base < k) (hk : k + gap ≤ endpoint) :
      ∃ c : Round, k ≤ c ∧ c ≤ k + gap ∧ ProposerCarrierAt S rho c :=
    hrec k
      (hpostBase.trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (action_add_delta_le_openingProposal_of_round_lt S hbk)))
      ((openingProposal_window_le_action S k gap).trans
        ((Assembly.a_mono S hk).trans hhorEnd))
  have hfirst : base < base + 4 ∧ base + 4 + gap ≤ endpoint := by
    simpa only [hendpoint, seedLag] using
      (seedAdoptionSelectRound1_nat (base := base) (gap := gap) (delayExtra := delayExtra))
  obtain ⟨q1, hq1lo, hq1hi, hcar1⟩ := hselect (base + 4)
    hfirst.1 hfirst.2
  have hsecond : base < q1 + 2 ∧ q1 + 2 + gap ≤ endpoint := by
    simpa only [hendpoint, seedLag] using
      (seedAdoptionSelectRound2_nat (delayExtra := delayExtra) hq1lo hq1hi)
  obtain ⟨q2, hq2lo, hq2hi, hcar2⟩ := hselect (q1 + 2)
    hsecond.1 hsecond.2
  have hthird : base < q2 + 2 + delayExtra ∧
      q2 + 2 + delayExtra + gap ≤ endpoint := by
    simpa only [hendpoint, seedLag] using
      (seedAdoptionSelectRound3_nat hq1lo hq1hi hq2lo hq2hi)
  obtain ⟨q3, hq3lo, hq3hi, hcar3⟩ := hselect (q2 + 2 + delayExtra)
    hthird.1 hthird.2
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
    n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29,
    n30, n31⟩ :=
    seedAdoptionRounds_nat hq1lo hq1hi hq2lo hq2hi hq3lo hq3hi
  obtain ⟨P2, hP2⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q2)
  obtain ⟨P3, hP3⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q3)
  have hq1end1 : q1 + 1 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n24
  have hq2end1 : q2 + 1 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n25
  have hq1end2 : q1 + 2 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n1
  have hq2end2 : q2 + 2 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n2
  have hq3end2 : q3 + 2 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n3
  have hq3end : q3 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n4
  have hq2budget : q2 + 2 * gap + 6 + 2 * delayExtra ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n23
  have hpostBase1 : S.E.t_GST ≤ S.a (base + 1) :=
    hpostBase.trans (Assembly.a_mono S (Nat.le_succ base))
  have hpostBase1L : gstLagged S ≤ S.a (base + 1) := gstLagged_le_a_succ S hpostBase
  have hhorAt : ∀ {k : Round}, k ≤ endpoint → S.a k ≤ rho.horizon := by
    intro k hk
    exact (Assembly.a_mono S hk).trans hhorEnd
  have hwindow : ∀ (k : Round), k ≤ endpoint →
      ∀ read : Time, S.a (base + 1) ≤ read → read ≤ S.a k → ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M := by
    intro k hk read hlo hhi w hw
    exact hgateWindow read hlo (hhi.trans (Assembly.a_mono S hk)) w hw
  have hframeAt : ∀ {lo hi : Round}, base + 1 ≤ lo → hi ≤ endpoint →
      SeedGateOffFrameAt S rho M lo hi := by
    intro lo hi hlo hhi read hread1 hread2 w hw
    exact hgateWindow read ((Assembly.a_mono S hlo).trans hread1)
      (hread2.trans (Assembly.a_mono S hhi)) w hw
  -- the first ceiling, at `q1 + 1`, from the carrier-adoption witness
  obtain ⟨hadoption, hcover1⟩ := hadopt M base q1 hr0 hq1lo hpostBase
    (hhorAt hq1end2) (hframeAt (le_refl (base + 1)) hq1end2)
    hcar1
  obtain ⟨B1, hceil1⟩ := exists_roundCeiling_of_window_of_adoption S adm hcom
    hfb (base := base + 1) (q := q1) hpostBase1L n7 (hhorAt hq1end2)
    (fun read hlo hhi w hw => hwindow (q1 + 2) hq1end2 read hlo hhi w hw)
    hadoption
  -- carried to `q2` and to `q3`
  obtain ⟨B2, hceil2, -⟩ := roundCeiling_through_of_window S adm hcom hfb
    (base := base + 1) (first := q1 + 1) (last := q2) (C := B1)
    hpostBase1L n8 (hhorAt hq2end2)
    (fun read hlo hhi w hw => hwindow (q2 + 2) hq2end2 read hlo hhi w hw)
    hceil1 q2 n9 (le_refl _)
  obtain ⟨B3, hceil3, -⟩ := roundCeiling_through_of_window S adm hcom hfb
    (base := base + 1) (first := q1 + 1) (last := q3) (C := B1)
    hpostBase1L n8 (hhorAt hq3end2)
    (fun read hlo hhi w hw => hwindow (q3 + 2) hq3end2 read hlo hhi w hw)
    hceil1 q3 n10 (le_refl _)
  -- the opening window of the second carrier round
  have hwindow2 : NamedGateOffOpeningWindowAt S rho M q2 P2 :=
    gateOffOpeningWindow_of_window S adm hfb (base := base + 1) (q := q2)
      hpostBase1 n11 (hhorAt hq2end1) hcar2.1 hP2
      (fun read hlo hhi w hw => hwindow (q2 + 1) hq2end1 read hlo hhi w hw)
  -- the band-carrier cover carried from `q1` to `q2 + 1`, and the derived grade
  -- of `q2` from the covers at `q2 - 2` and `q2 - 1`
  have hcovers := seedBandCarrierCover_through S adm hcom hfb (M := M) (lo := q1)
    (hi := q2 + 1) (hpostBase.trans (Assembly.a_mono S n17))
    (hhorAt hq2end1) (hframeAt ((Nat.le_succ (base + 1)).trans n7) hq2end1)
    hcover1
  have hgraded2 := seedGradedAndClear_of_covers S adm hcom hfb (q := q2)
    n28 (hpostBase.trans (Assembly.a_mono S ((Nat.le_succ base).trans n27)))
    (hhorAt hq2end1) (hframeAt n27 hq2end1)
    (hcovers (q2 - 2) n29 n31.1) (hcovers (q2 - 1) n30 n31.2)
  -- the opening proposal of the second carrier round
  rcases namedGateOffOpening_pred_or_exact_or_hMaxRise S adm hcar2
      hwindow2 with hpred | hexact | hriseProposal
  · -- height `M - 1`
    exact hclose base q2 B2 P2 hr0 n13 hq2budget hpostBase hhorEnd hcap h2
      hgateWindow hgraded2 hcar2 hceil2 hwindow2 hpred
  · -- height `M`: leaf (c)
    have hcutFrame2 : ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q2 + 1))).h_max = M ∧
          (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (q2 + 1))).h_j + 2 ≤ M := by
      intro w hw
      have h := hwindow (q2 + 1) hq2end1 (S.hc.Γ_neg1 S.E.Δ (q2 + 1))
        ((Assembly.a_mono S n12).trans
          (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
            (action_add_delta_le_next_Γ_neg1 S q2)))
        (le_of_lt (next_Γ_neg1_lt_action S q2)) w hw
      exact ⟨h.2, h.1⟩
    have hprevFrontier2 : ∀ u ∈ rho.honest,
        (rho.storeBeforeTime S u (S.a (q2 - 1))).h_max = M := by
      intro u hu
      exact (hwindow (q2 - 1) (seedPrevRoundEnd_nat hq2end1) (S.a (q2 - 1))
        (Assembly.a_mono S (seedPrevRound_nat n11)) le_rfl u hu).2
    have hadopt2 := seedOpeningLifecycle_of_inputs S adm hcom hfb hcar2 hceil2
      hwindow2 hprevFrontier2
      hcutFrame2
    exact seedExactOpening_outcome S adm hcom hfb h2 n12 n14 hq3end
      hpostBase hhorEnd hcap hgateWindow hcar2 hcar3 hceil3 hP2 hP3
      (hadopt2.gradeNext P2 hP2) hexact
  · -- the public frontier rose at the opening proposal read
    refine Or.inl (lt_of_lt_of_le hriseProposal ?_)
    refine honestHMaxAt_mono S adm.toNamedScheduleWellFormed ?_
    refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact Assembly.a_mono S (le_trans (Nat.le_succ q2) hq2end1)











end HealingSurface
end Proofs
end DecoupledConsensusModel

end
