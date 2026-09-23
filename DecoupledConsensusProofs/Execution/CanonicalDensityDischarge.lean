module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalDensity
public import DecoupledConsensusProofs.Protocol.Grades.PostRecoveryCarrierHeightRead
public import DecoupledConsensusProofs.Protocol.ChainState.RowFreshness
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryExit
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. Arithmetic helpers

`Height` and `Round` are reducible abbreviations of `Nat`, but `omega` matches
the type syntactically, so every numeric step is stated on bare `Nat`. -/

private theorem nat_lt_succ (a : Nat) : a < a + 1 := by omega

private theorem nat_add_zero_le (a : Nat) : a + 0 ≤ a := by omega

private theorem nat_step_of_lt {a b c d : Nat}
    (h1 : a + d ≤ b) (h2 : b < c) : a + (d + 1) ≤ c := by omega


/-! ## 1. Honest height rows -/

/-- Some honest validator's round-`k` action emits a height row at `h`. -/
def HonestHeightRowAt (S : Setup V) (rho : Run V) (h : Height) (k : Round) :
    Prop :=
  ∃ v ∈ rho.honest,
    (actionAttestationAt S rho v k).height_pair.erase.height? = some h

/-- Any honest attestation emitted in the run is the exact action attestation
for its recorded round. -/
private theorem emittedAttestation_eq_actionAttestationAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hemit : rho.emits S v (.attest a) t) :
    a = actionAttestationAt S rho v a.round := by
  have htime : t = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  subst t
  exact ((NamedActionSources.action_run_emission S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v a.round a).mp hemit).2.2

/-- Consecutive action instants are strictly ordered. -/
private theorem action_lt_action_succ (S : Setup V) (r : Round) :
    S.a r < S.a (r + 1) :=
  lt_of_le_of_lt
    ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (action_add_delta_le_next_Γ_neg1 S r))
    (next_Γ_neg1_lt_action S r)

/-- Round order is recovered from action-instant order. -/
private theorem round_le_of_action_le (S : Setup V) {k r : Round}
    (h : S.a k ≤ S.a r) : k ≤ r := by
  by_contra hnot
  have hrk : r + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  exact absurd ((action_lt_action_succ S r).trans_le
    ((Assembly.a_mono S hrk).trans h)) (lt_irrefl _)

/-- Strict round order is recovered from strict action-instant order. -/
private theorem round_lt_of_action_lt (S : Setup V) {k r : Round}
    (h : S.a k < S.a r) : k < r := by
  by_contra hnot
  exact absurd ((Assembly.a_mono S (Nat.le_of_not_gt hnot)).trans_lt h)
    (lt_irrefl _)

/-- A processed block whose chain has crossed height `h` exposes an honest
height row at `h`, emitted strictly before the read. -/
theorem exists_honestHeightRowAt_of_crossing
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} {t : Time} {W : NamedBlock V}
    (hW : W ∈ (rho.storeBeforeTime S v t).bodies)
    {h : Height} (hpos : 1 ≤ h)
    (hcross : h < (Protocol.derive_named S.E S.cfg W).h) :
    ∃ k : Round, S.a k < t ∧ HonestHeightRowAt S rho h k := by
  obtain ⟨X, hXW, hXheight, Q, hQ, hwitness⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg W h hpos hcross
  obtain ⟨i, hiQ, hiHonest⟩ :=
    HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, a, hcarrier, ha, hai, hpair⟩ := hwitness i hiQ
  have haHonest : a.val_index ∈ rho.honest := by
    rw [hai]
    exact hiHonest
  obtain ⟨i, hi, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted t
  have hWni : W ∈ (rho.stateBefore S i v).st.bodies := by
    have hbodyEq :
        (rho.stateBeforeTime S t v).st.bodies =
          (rho.stateBefore S i v).st.bodies := by
      exact congrArg (fun x => x.st.bodies) (congrFun hi v)
    rw [← hbodyEq]
    exact hW
  obtain ⟨j, hj, ta, hacc, hta, hemit⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_emission S rho
      adm.toNamedAdmissibleCore.toNamedUnforgeable i v hWni hcarrier ha haHonest
  obtain ⟨e, he, -, het⟩ := hacc.1.2
  have htaLt : S.a a.round < t := by
    exact hta.trans_lt (by simpa only [het] using hbefore j e hj he)
  have hrowHeight : a.height_pair.erase.height? = some h := by
    simp only [NamedHeightPair.matchesEntry] at hpair
    cases hp : a.height_pair with
    | empty => rw [hp] at hpair; exact absurd hpair (by simp)
    | vote height entry timeout =>
        rw [hp] at hpair
        simp only [decide_eq_true_eq] at hpair
        cases timeout <;>
          simp [NamedHeightPair.erase, HeightPair.height?, hpair.1]
  have haction : a = actionAttestationAt S rho a.val_index a.round :=
    emittedAttestation_eq_actionAttestationAt S adm hemit
  refine ⟨a.round, htaLt, a.val_index, haHonest, ?_⟩
  rw [← haction]
  exact hrowHeight

/-! ## 2. One canonical height per round -/

/-- A row at `h + 1` forces a row at `h` at a strictly earlier round.

The row reads its own processed FG source, whose chain has already crossed
`h`; that crossing quorum contains an honest row at `h`, and a carried row was
emitted strictly before the source was read. -/
theorem exists_honestHeightRowAt_pred
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {h : Height} {k : Round} (hpos : 1 ≤ h)
    (hrow : HonestHeightRowAt S rho (h + 1) k) :
    ∃ k' : Round, k' < k ∧ HonestHeightRowAt S rho h k' := by
  obtain ⟨v, hv, hrowv⟩ := hrow
  obtain ⟨Q, -, hQmem, hQheight⟩ := honestRow_height_le_source S adm hv hrowv
  have hQmem' : Q ∈ (rho.storeBeforeTime S v (S.a k)).bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Run.storeBeforeTime] using hQmem
  have hcross : h < (Protocol.derive_named S.E S.cfg Q).h := by
    rw [hQheight]
    exact nat_lt_succ h
  obtain ⟨k', hk', hrow'⟩ :=
    exists_honestHeightRowAt_of_crossing S adm hmajority hQmem' hpos hcross
  exact ⟨k', round_lt_of_action_lt S hk', hrow'⟩

/-- Descending `d` heights costs at least `d` rounds. -/
theorem exists_honestHeightRowAt_descend
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {h : Height} (hpos : 1 ≤ h) :
    ∀ (d : Nat) (k : Round), HonestHeightRowAt S rho (h + d) k →
      ∃ k' : Round, k' + d ≤ k ∧ HonestHeightRowAt S rho h k' := by
  intro d
  induction d with
  | zero =>
      intro k hrow
      exact ⟨k, nat_add_zero_le k, by simpa using hrow⟩
  | succ d ih =>
      intro k hrow
      have hrow' : HonestHeightRowAt S rho (h + d + 1) k := by
        simpa only [Nat.add_assoc] using hrow
      obtain ⟨k1, hk1, hrow1⟩ :=
        exists_honestHeightRowAt_pred S adm hmajority
          (le_trans hpos (Nat.le_add_right h d)) hrow'
      obtain ⟨k', hk', hrowFinal⟩ := ih k1 hrow1
      exact ⟨k', nat_step_of_lt hk' hk1, hrowFinal⟩

/-! ## 3. The carrier round anchors the count -/

private theorem honest_nonempty_of_majority
    (S : Setup V) {H : Finset V}
    (hmajority : HonestWeightMajority S H) : H.Nonempty := by
  by_contra hnone
  have hzero : S.E.electorate.weightOf H = 0 := by
    rw [Finset.not_nonempty_iff_eq_empty.mp hnone]
    simp [Electorate.weightOf]
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold HonestWeightMajority at hmajority
  omega

/-- A post-boundary row before the carrier round has its canonical source
below the carrier's opening proposal. -/
theorem honestHeightRowAt_le_of_heightHistory
    (S : Setup V) {rho : Run V}
    {q0 c : Round} (hregime : CanonicalCarrierHeightReadAt S rho q0 c)
    {h : Height} {k : Round} (hq0 : q0 ≤ k) (hkc : k < c)
    (hrow : HonestHeightRowAt S rho h k) :
    h ≤ carrierOpeningHeight S rho c := by
  obtain ⟨v, hv, hrowv⟩ := hrow
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho
    (S.hc.opening_slot c)
  obtain ⟨Q, -, -, hQpre, hQheight⟩ :=
    hregime.heightHistory P hP k hq0 hkc v hv h hrowv
  have hPcanon : P = canonicalProposal S rho (S.hc.opening_slot c) :=
    Option.some.inj (hP.symm.trans
      (canonicalProposal_spec S rho (S.hc.opening_slot c)))
  rw [carrierOpeningHeight, ← hPcanon, ← hQheight]
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hQpre





/-
/-- A height strictly below a carrier's opening height has an honest row at a
strictly earlier round.

The carrier's opening proposal is the live confirmation of every honest action
at that round, so it is processed there; its chain crossed the height. -/
theorem exists_honestHeightRowAt_below_carrierOpening
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 c: Round} (hregime: CanonicalCarrierHeightReadAt S rho q0 c)
    {h: Height} (hpos: 1 ≤ h) (hlt: h < carrierOpeningHeight S rho c):
    ∃ k: Round, k < c ∧ HonestHeightRowAt S rho h k:= by
  obtain ⟨v, hv⟩:= honest_nonempty_of_majority S hmajority
  have hmem: proposedBlock S rho (S.hc.opening_slot c) ∈
      (rho.storeBeforeTime S v (S.a c)).T:= by
    have hlive:= liveConfirmed_mem_storeBeforeTime_action S adm v c
    rwa [hregime.openingLive v hv] at hlive
  obtain ⟨k, hk, hrow⟩:=
    exists_honestHeightRowAt_of_crossing S adm hmajority hmem hpos hlt
  exact ⟨k, round_lt_of_action_lt S hk, hrow⟩
 -/

/-! ## 4. The carrier density bound -/









/-
/-- **The carrier density bound.** Between two carrier rounds the opening
proposal gains at most one height per round.

Counting argument. If the later opening were higher than that, its chain would
have crossed every height in between, so there would be an honest row at each
of those heights, at strictly decreasing rounds. The lowest of them is above
the earlier carrier's opening height, so by the carrier anchor its round is
strictly after `c1`; the highest is carried under the later opening proposal,
so its round is strictly before `c2`. That leaves fewer rounds than heights. -/
theorem carrierOpeningHeight_le_add_sub_of_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 c1 c2: Round} (hc12: c1 < c2)
    (hregime1: CanonicalCarrierHeightReadAt S rho q0 c1)
    (hregime2: CanonicalCarrierHeightReadAt S rho q0 c2)
    (hold: honestHMaxAt S rho (S.a q0) ≤ carrierOpeningHeight S rho c1):
    carrierOpeningHeight S rho c2 ≤
      carrierOpeningHeight S rho c1 + (c2 - c1):= by
  by_contra hnot
  have hgt: carrierOpeningHeight S rho c1 + (c2 - c1) <
      carrierOpeningHeight S rho c2:= Nat.lt_of_not_ge hnot
  have hge2: carrierOpeningHeight S rho c1 + 2 ≤
      carrierOpeningHeight S rho c2:= nat_two_le_of_band_gt hgt hc12
  obtain ⟨k, hk, hrow⟩:=
    exists_honestHeightRowAt_below_carrierOpening S adm hmajority hregime2
      (nat_one_le_pred_of_two_le hge2) (nat_pred_lt_of_two_le hge2)
  rw [nat_height_split hge2] at hrow
  obtain ⟨k', hk', hrow'⟩:=
    exists_honestHeightRowAt_descend S adm hmajority
      (nat_one_le_succ (carrierOpeningHeight S rho c1)) _ k hrow
  have hanchor: c1 < k':= by
    by_contra hle
    exact nat_not_succ_le_self
      (honestHeightRowAt_le_carrierOpeningHeight S adm hregime1 hold
        (Nat.le_of_not_gt hle) hrow')
  exact nat_band_contradiction hgt rfl hc12 hk hk' hanchor
 -/

/-! ## 5. The frontier floor at a carrier -/

private theorem nat_le_succ_of_pred_le {m X : Nat} (h : m - 1 ≤ X) :
    m ≤ X + 1 := by omega

private theorem nat_pred_le_of_le_succ {m X : Nat} (h : m ≤ X + 1) :
    m - 1 ≤ X := by omega

private theorem nat_le_one_le_succ {m X : Nat} (h : m ≤ 1) : m ≤ X + 1 := by
  omega

private theorem nat_absurd_frozen {m A M : Nat}
    (hfrozen : m ≤ A + 1) (hgain : A + 2 ≤ M) (hmM : M = m) : False := by
  omega

/-- The strict pre-action read at `a_r` is the inclusive read at the action
instant. -/
private theorem storeBeforeTime_succ_eq_storeAt
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (r : Round) :
    rho.storeBeforeTime S v (S.a r + 1) = rho.storeAt S v (S.a r) := by
  unfold Run.storeBeforeTime Run.storeAt
  rw [stateBeforeTime_eq_stateAt_pred S sch (S.a r + 1)]
  simp

/-- One honest local frontier at round `r` is either below the carrier's
opening height, or it is no higher than the debris frontier at `q0`.

The local frontier is backed by a crossing quorum, so an honest row sits one
below it. A post-boundary row is on the carrier's canonical chain; a row from
the debris prefix is below the honest frontier at `q0`. -/
theorem localHMax_le_carrierOpening_succ_or_old
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {q0 r c : Round} (_hq0 : q0 ≤ r) (hrc : r < c)
    (hregime : CanonicalCarrierHeightReadAt S rho q0 c)
    {v : V} (_hv : v ∈ rho.honest) :
    (rho.storeAt S v (S.a r)).h_max ≤ carrierOpeningHeight S rho c + 1 ∨
      (rho.storeAt S v (S.a r)).h_max ≤ honestHMaxAt S rho (S.a q0) + 1 := by
  have hstore : rho.storeBeforeTime S v (S.a r + 1) =
      rho.storeAt S v (S.a r) :=
    storeBeforeTime_succ_eq_storeAt S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v r
  by_cases hsmall : (rho.storeAt S v (S.a r)).h_max ≤ 1
  · exact Or.inl (nat_le_one_le_succ hsmall)
  · have hlarge : 1 < (rho.storeBeforeTime S v (S.a r + 1)).h_max := by
      rw [hstore]
      exact Nat.lt_of_not_ge hsmall
    obtain ⟨W, -, Q, X, a, ta, -, -, -, -, haHonest, hemit, hta, hheight⟩ :=
      frontierQuorumWitness_stateBeforeTime S adm hmajority
        (t := S.a r + 1) (v := v) hlarge
    rw [hstore] at hheight
    have hround : ta = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
    have haction : a = actionAttestationAt S rho a.val_index a.round :=
      emittedAttestation_eq_actionAttestationAt S adm hemit
    have hrow : HonestHeightRowAt S rho
        ((rho.storeAt S v (S.a r)).h_max - 1) a.round := by
      refine ⟨a.val_index, haHonest, ?_⟩
      rw [← haction]
      exact hheight
    have hleR : a.round ≤ r := by
      apply round_le_of_action_le S
      rw [← hround]
      exact Int.lt_add_one_iff.mp hta
    rcases Nat.lt_or_ge a.round q0 with hprefix | hpost
    · refine Or.inr (nat_le_succ_of_pred_le ?_)
      exact honestEmittedHeight_le_honestHMaxAt S adm haHonest hemit hheight
        (by rw [hround]; exact Assembly.a_mono S (Nat.le_of_lt hprefix))
    · exact Or.inl (nat_le_succ_of_pred_le
        (honestHeightRowAt_le_of_heightHistory S hregime hpost
          (Nat.lt_of_le_of_lt hleR hrc) hrow))

/-- **The relayed frontier floor at a carrier.** Once the honest frontier at
`r` has risen two heights above the debris frontier at `q0`, it is at most one
above the carrier's opening height.

The debris branch of the local dichotomy freezes the frontier one above `q0`,
which the two-height gain excludes. -/
theorem honestHMaxAt_sub_one_le_carrierOpeningHeight_of_gain
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {q0 r c : Round} (hq0 : q0 ≤ r) (hrc : r < c)
    (hregime : CanonicalCarrierHeightReadAt S rho q0 c)
    (hgain : honestHMaxAt S rho (S.a q0) + 2 ≤ honestHMaxAt S rho (S.a r)) :
    honestHMaxAt S rho (S.a r) - 1 ≤ carrierOpeningHeight S rho c := by
  obtain ⟨v, hv, hsup⟩ :=
    Finset.exists_mem_eq_sup rho.honest
      (honest_nonempty_of_majority S hmajority)
      (fun w => (rho.storeAt S w (S.a r)).h_max)
  have hM : honestHMaxAt S rho (S.a r) =
      (rho.storeAt S v (S.a r)).h_max := hsup
  rcases localHMax_le_carrierOpening_succ_or_old S adm hmajority hq0 hrc
      hregime hv with hgood | hfrozen
  · exact nat_pred_le_of_le_succ (hM.trans_le hgood)
  · exact absurd hgain (fun hg => nat_absurd_frozen hfrozen hg hM)

/-! ## 6. The carrier density interface -/








/-
/-- Interface form: the regime at every post-boundary carrier discharges the
density interface. This is the exact hand-off the recurring-finality
assembler already has in context. -/
theorem canonicalCarrierDensityFrom_of_regimeFrom
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0: Round}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hafterAll: ∀ r: Round, q0 + 1 < r →
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hregime: CanonicalRegimeRoundFrom S rho q0):
    CanonicalCarrierDensityFrom S rho q0:=
  canonicalCarrierDensityFrom_of_regime S adm hmajority hexec
    (fun r hr hcarrier hhor => (hregime r (hafterAll r hr) hcarrier hhor).toHeightRead)
 -/


/-
/-- The suffix execution and the moving-chain fold discharge the density
interface. -/
theorem canonicalCarrierDensityFrom_of_movingChain
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0: Round}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hafterAll: ∀ r: Round, q0 + 1 < r →
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q0):
    CanonicalCarrierDensityFrom S rho q0:= by
  apply canonicalCarrierDensityFrom_of_regime S adm hmajority hexec
  intro r hr hcarrier hhor
  exact canonicalCarrierHeightReadAt_of_core_and_chain S hmajority
    (canonicalRegimeRoundExecutionCoreAt_of_execution S adm hcom hexec
      (hafterAll r hr) hcarrier hhor)
    (hchain r (hafterAll r hr) hcarrier hhor)
 -/




/-! ## 7. The finality consumers, re-derived -/



































/-
/-- The carrier pair of one recurring-finality phase, straight from the suffix
execution and the moving-chain fold. No density residual is used. -/
theorem exists_justifiableCarrierPair_afterTwoProgress_of_movingChain
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 rawLag gap start: Round}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hafterAll: ∀ r: Round, q0 + 1 < r →
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q0)
    (hprogress: EventualHeightProgressFrom S rho q0 rawLag)
    (hrawPos: 0 < rawLag)
    (hrec: MultiProposerRecurrence S rho gap)
    (hgap: gap + 2 ≤ S.cfg.K)
    (hstart: q0 ≤ start)
    (hhor: S.a (start + 4 * rawLag + 3 * gap + 5) ≤ rho.horizon):
    ∃ c1 c2: Round,
      start + 2 * rawLag < c1 ∧ c1 < c2 ∧ c2 ≤ c1 + gap + 1 ∧
        c2 ≤ start + 4 * rawLag + 3 * gap + 4 ∧
        ProposerCarrierAt S rho c1 ∧ ProposerCarrierAt S rho c2 ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho c1 ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho c2 ∧
        ((derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot c1))).nj = false ∨
          (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot c2))).nj = false):=
  exists_justifiableCarrierPair_afterTwoProgress_carrier S adm
    (canonicalCarrierDensityFrom_of_movingChain S adm hcom hmajority
      hexec hafterAll hchain)
    hprogress hrawPos hrec hgap hstart
      (hafterAll (start + 2 * rawLag + 1)
        (nat_q0_succ_lt_window hstart hrawPos)) hhor
 -/








/-
/-- The carrier pair WITH PREDECESSORS, straight from the suffix execution and
the moving-chain fold. No density residual is used.

This is the form the finality phase needs once every carrier it uses must have
a carrier predecessor; `exists_justifiableCarrierPair_afterTwoProgress_of_movingChain`
is unchanged beside it. -/
theorem exists_justifiableCarrierPairWithPredecessor_afterTwoProgress_of_movingChain_of_window
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 rawLag gap start: Round}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hafterAll: ∀ r: Round, q0 + 1 < r →
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q0)
    (hprogress: EventualHeightProgressFrom S rho q0 rawLag)
    (hrawPos: 0 < rawLag)
    (hpair: ∀ k: Round, start ≤ k →
      k ≤ start + 4 * rawLag + 3 * gap + 5 →
      ∃ p: Round, k ≤ p ∧ p + 1 ≤ k + gap ∧
        ProposerCarrierAt S rho p ∧ ProposerCarrierAt S rho (p + 1))
    (hgap: gap + 2 ≤ S.cfg.K)
    (hstart: q0 ≤ start)
    (hhor: S.a (start + 4 * rawLag + 3 * gap + 5) ≤ rho.horizon):
    ∃ c1 c2: Round,
      start + 2 * rawLag < c1 ∧ c1 < c2 ∧ c2 ≤ c1 + gap + 1 ∧
        c2 ≤ start + 4 * rawLag + 3 * gap + 4 ∧
        ProposerCarrierAt S rho c1 ∧ ProposerCarrierAt S rho c2 ∧
        ProposerCarrierAt S rho (c1 - 1) ∧ ProposerCarrierAt S rho (c2 - 1) ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho c1 ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho c2 ∧
        ((derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot c1))).nj = false ∨
          (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot c2))).nj = false):=
  exists_justifiableCarrierPairWithPredecessor_afterTwoProgress_carrier_of_window S adm
    (canonicalCarrierDensityWithPredecessorFrom_of_movingChain S adm hcom
      hmajority hexec hafterAll hchain)
    hprogress hrawPos hpair hgap hstart
      (hafterAll (start + 2 * rawLag + 1)
        (nat_q0_succ_lt_window hstart hrawPos)) hhor
 -/


/-
/-- The existing global recurrence interface is unchanged. -/
theorem exists_justifiableCarrierPairWithPredecessor_afterTwoProgress_of_movingChain
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 rawLag gap start: Round}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hafterAll: ∀ r: Round, q0 + 1 < r →
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q0)
    (hprogress: EventualHeightProgressFrom S rho q0 rawLag)
    (hrawPos: 0 < rawLag)
    (hpair: ProposerPairRecurrence S rho gap)
    (hgap: gap + 2 ≤ S.cfg.K)
    (hstart: q0 ≤ start)
    (hhor: S.a (start + 4 * rawLag + 3 * gap + 5) ≤ rho.horizon):
    ∃ c1 c2: Round,
      start + 2 * rawLag < c1 ∧ c1 < c2 ∧ c2 ≤ c1 + gap + 1 ∧
        c2 ≤ start + 4 * rawLag + 3 * gap + 4 ∧
        ProposerCarrierAt S rho c1 ∧ ProposerCarrierAt S rho c2 ∧
        ProposerCarrierAt S rho (c1 - 1) ∧ ProposerCarrierAt S rho (c2 - 1) ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho c1 ∧
        honestHMaxAt S rho (S.a start) < carrierOpeningHeight S rho c2 ∧
        ((derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot c1))).nj = false ∨
          (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot c2))).nj = false):=
  exists_justifiableCarrierPairWithPredecessor_afterTwoProgress_of_movingChain_of_window
    S adm hcom hmajority hexec hafterAll hchain hprogress hrawPos
      (fun k _ _ => hpair k) hgap hstart hhor
 -/

#print axioms exists_honestHeightRowAt_of_crossing
#print axioms exists_honestHeightRowAt_pred
#print axioms exists_honestHeightRowAt_descend
#print axioms honestHeightRowAt_le_of_heightHistory
#print axioms localHMax_le_carrierOpening_succ_or_old
#print axioms honestHMaxAt_sub_one_le_carrierOpeningHeight_of_gain

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
