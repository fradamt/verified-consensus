module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.SeedGradeExistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.VoteDutyGradeTransport
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedSlotInterval

@[expose] public section

/-!
# The band grade, and what it buys

**Exploratory.** `SeedRoundGradedAt` asks each honest action store for SOME
selected grade-2 block. The strengthening asks for one IN THE FRONTIER BAND,
at height at least `M - 1`.

A band grade is worth stating because it makes the seed's other standing
premise vacuous. `SeedClearCarrierCompatiblePreviousAt` fires only at a vote
duty that holds NO fresh anchor for the round. A gate-off read's fork-choice
root is below every run block of the band, so a band grade is active at every
duty of the round; grade 2 implies grade 1 over the same filtered tree, so the
fresh anchor exists there and the premise never fires.

What is NOT here is the production: nothing yet builds a band grade from the
gate-off regime. The trace is in `log.md`.

## Named-runtime proof (design note)

`RunBlock` lives only over `NamedBlock V`, so `SeedRoundBandGradeAt` and
`SeedBandCarrierCoverAt` carry a named witness `Qn` and read the band height
through `Protocol.derive_named Qn`; every store read of the witness is
`Qn.erase`. Each earlier text is kept byte-exact at its declaration.

The grade currency of the production arm changes with the runtime, not with
this file's claims. The selection action never re-evaluates `Protocol.G2`: it
reads the frame frozen at the round's G2-domain cutoff, so a common grade is
`NamedGradeFormsAt` (the relative grade at that read), and the cover's own
delivery facts supply it through
`namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active`. The gate-off
frame at the domain read is derived from the two frame premises this file
already carries, by monotonicity of `h_max` and `h_j` in the reading time; no
premise is added anywhere.

One per-reader step does not survive: `seedGradedBlock_preceq_actionCarrier
_at_store` is blocked (class d) with its declaration byte-exact, because it
goes from one reader's ABSOLUTE action grade to that reader's frame-computed
carrier, and no absolute-to-relative bridge exists in the live tree. Its only
consumer here, `seedBandCarrierCover_succ`, is re-derived through the run-level
bridge instead, so no downstream step is lost.
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


/-- **The band grade of a round.** Each honest reader holds a run block of the
frontier band that is grade 2 at its own round-`q` action read and processed at
its own vote duties of the round.

The per-reader shape is deliberate: like `SeedRoundGradedAt`, and unlike
`GradeFormsAt`, the block may differ from reader to reader.

design note (statement change, ledger row): `RunBlock` lives only over
`NamedBlock V`, so the witness is a named body `Qn` and every erased read of it
goes through `Qn.erase`; the band height reads `Protocol.derive_named Qn`
in place of the retired `derived_state Qn.erase`. earlier text, byte-exact:

    def SeedRoundBandGradeAt
        (S: Setup V) (rho: Run V) (M: Height) (q: Round): Prop:=
      ∀ w ∈ rho.honest, ∃ Q: Block V,
        RunBlock S rho Q ∧
          M - 1 ≤ (derived_state S.E S.cfg Q).h ∧
            Protocol.G2 S.E (gradeViewAt S rho w q) S.hc q Q = true ∧
              ∀ d: Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
                Q ∈ (Proofs.Optimistic.voteDutyStore S rho w d).T -/
def SeedRoundBandGradeAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round) : Prop :=
  (∀ v ∈ rho.honest, ∃ Q : Block V,
      Internal.PhaseGrades.nodeQ2 S (actionReadAt S rho v q) q = some Q) ∧
  ∀ w ∈ rho.honest, ∃ Qn : NamedBlock V,
    RunBlock S rho Qn ∧
      M - 1 ≤ (Protocol.derive_named S.E S.cfg Qn).h ∧
        Protocol.G2 S.E (gradeViewAt S rho w q) S.hc q Qn.erase = true ∧
          ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
            Qn.erase ∈ (Proofs.Optimistic.voteDutyStore S rho w d).T

/-- The last-slot bound, with bare `Nat` binders. -/
private theorem seedLastSlot_nat {a b : Nat} (hb : 0 < b) (h : a ≤ b - 1) :
    a < b := by
  omega

/-- Every slot of a round reports that round. -/
private theorem seedRoundSlot_round_of
    (S : Setup V) {q d : Round}
    (hlo : S.hc.opening_slot q ≤ d) (hhi : d ≤ seedRoundLastSlot S q) :
    S.hc.round_of d = q := by
  have hlast : d < S.hc.opening_slot (q + 1) := by
    have hopen : 0 < S.hc.opening_slot (q + 1) := by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos (Nat.succ_pos q)
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have hd : d ≤ S.hc.opening_slot (q + 1) - 1 := by
      simpa only [seedRoundLastSlot] using hhi
    exact seedLastSlot_nat hopen hd
  rcases Nat.eq_or_lt_of_le hlo with heq | hlt
  · rw [← heq]
    exact round_of_opening_slot_eq_schedule S.hc q
  · exact round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hlt hlast

/-- **Grade one at a vote duty from the reader's own action grade.** This is
`g1_at_voteDuty_of_gradeFormsAt` with the run-level grade replaced by the
reader's own grade-2 witness; the transport was already pointwise. -/
theorem seedG1_at_voteDuty_of_ownG2
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {B : Block V} {v : V} (hv : v ∈ rho.honest)
    (hG2 : Protocol.G2 S.E (gradeViewAt S rho v r) S.hc r B = true)
    {s : Slot} (hround : S.hc.round_of s = r) :
    Protocol.G1 S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.gradeView S.hc r B
        = true := by
  let read := Protocol.vote_time S.E s
  have hG1Action : Protocol.G1 S.E (gradeViewAt S rho v r) S.hc r B = true :=
    G2_imp_G1 S.E (gradeViewAt S rho v r) S.hc r B hG2
  have hcut : S.hc.Γ_0 S.E.Δ r ≤ read := by
    simpa only [read] using Γ_0_le_vote_time_of_round_eq S hround
  have hG1Read : Protocol.G1 S.E
      (rho.storeBeforeTime S v read).toHealing.gradeView S.hc r B = true := by
    rcases le_total read (S.a r) with hbefore | hafter
    · have hG1AtAction : Protocol.G1 S.E
          (rho.storeBeforeTime S v (S.a r)).toHealing.gradeView
          S.hc r B = true := by
        simpa only [gradeViewAt, healStoreAt] using hG1Action
      exact G1_reflects_after_cutoff S adm hv hcut hbefore hG1AtAction
    · exact G1_persists_from_opening S adm hv hafter hG1Action
  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore, read] using hG1Read


/-- **The fresh anchor exists wherever a grade-1 block does.**

Local copy of `VoteBelowSource.fresh_anchor_isSome_of_G1`, which that file put
behind an  comment as prior grade scaffold. The retirement
is about the selection runtime no longer recomputing an anchor inside a duty; the
store-level fact is unchanged, and `SeedClearCarrierCompatiblePreviousAt` still
reads exactly this `Protocol.fresh_anchor`. Proof text is the retired one,
verbatim: two grade-1 blocks of one store are compatible, so their set is a
chain and "deepest" is total on it. -/
private theorem seedFreshAnchor_isSome_of_G1 (E : Env V)
    {hc : Protocol.HealConfig} {st : Protocol.HealingStore V} {r : Round} {B : Block V}
    (hmem : B ∈ Protocol.get_filtered_block_tree st.toFG)
    (hG1 : Protocol.G1 E st.gradeView hc r B = true) :
    (Protocol.fresh_anchor E hc st r).isSome = true := by
  refine deepest?_isSome_of_compatible ?_ ⟨B, Finset.mem_filter.mpr ⟨hmem, hG1⟩⟩
  intro X hX Y hY
  exact G1_compatible E (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hY).2

/-- **A band grade gives a fresh anchor at every vote duty of its round.** -/
theorem seedFreshAnchor_isSome_of_bandGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hframe : ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        Protocol.vote_time S.E d ≤ rho.horizon ∧
          (Proofs.Optimistic.voteDutyStore S rho w d).h_max = M ∧
            (Proofs.Optimistic.voteDutyStore S rho w d).h_j + 2 ≤ M)
    (hband : SeedRoundBandGradeAt S rho M q) :
    ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        (Protocol.fresh_anchor S.E S.hc
          (Proofs.Optimistic.voteDutyStore S rho w d).toHealing q).isSome = true := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  intro d hlo hhi w hw
  obtain ⟨Qn, hQrun, hQband, hQG2, hQmem⟩ := hband.2 w hw
  obtain ⟨hhor, hmax, hgate⟩ := hframe d hlo hhi w hw
  have hM : 1 ≤ M :=
    (by decide : (1 : Nat) ≤ 2).trans
      ((Nat.le_add_left 2 (Proofs.Optimistic.voteDutyStore S rho w d).h_j).trans hgate)
  have hactive : Qn.erase ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho w d).toHealing.toFG := by
    have hmemRead : Qn.erase ∈ (rho.storeBeforeTime S w
        (Protocol.vote_time S.E d)).T := by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hQmem d hlo hhi
    have hfilt := frontierBlock_filtered_of_gateOff S adm hsb hw hhor
      hmemRead rfl hQrun hQband hM
      (by simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hmax)
      (by simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hgate)
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hfilt
  exact seedFreshAnchor_isSome_of_G1 S.E hactive
    (seedG1_at_voteDuty_of_ownG2 S adm hw hQG2
      (seedRoundSlot_round_of S hlo hhi))

/-- **The band grade makes the seed's standing premise vacuous.**
`SeedClearCarrierCompatiblePreviousAt` fires only at a duty with no fresh
anchor for the round, and a band grade always supplies one. -/
theorem seedClearCarrierCompatiblePrevious_of_bandGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hframe : ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        Protocol.vote_time S.E d ≤ rho.horizon ∧
          (Proofs.Optimistic.voteDutyStore S rho w d).h_max = M ∧
            (Proofs.Optimistic.voteDutyStore S rho w d).h_j + 2 ≤ M)
    (hband : SeedRoundBandGradeAt S rho M q) :
    SeedClearCarrierCompatiblePreviousAt S rho q := by
  intro d hlo hhi w hw hfresh _ v _
  exact absurd (seedFreshAnchor_isSome_of_bandGrade S adm hfb hframe hband
    d hlo hhi w hw) (by rw [hfresh]; exact Bool.noConfusion)

/-! ## The band grade subsumes the seed's grade obligation -/





/-- The justified height of one validator only grows in the reading time.
Same shape as `seedBandStore_T_subset`; `RecoveryCrossingHealingRun` keeps the
same fact but sits outside this file's import cone. -/
private theorem seedBandStore_h_j_mono
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) {t u : Time} (htu : t ≤ u) :
    (rho.storeBeforeTime S v t).h_j ≤ (rho.storeBeforeTime S v u).h_j := by
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch,
    storeBeforeTime_eq_stateBefore_strictEventIndex S sch]
  exact stateBefore_h_j_mono S rho v (strictEventIndex_mono rho htu)

/-- Two run-block witnesses erasing to one public block are the same named
body. Mechanical copy of the `private` helper in
`HeightProgressSeedRegimeRun.lean`. -/
private theorem seedBandRunBlock_unique_of_erase_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- **A band grade is a selected grade at the round's action store.** The
band block is processed by the vote duty just after the opening, hence by the
action read, and a gate-off action read keeps every band run block in the
filtered tree. -/
theorem seedSelectedGrade_of_bandGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hframe : ∀ w ∈ rho.honest,
      S.a q ≤ rho.horizon ∧
        (healStoreAt S rho w q).h_max = M ∧
          (healStoreAt S rho w q).h_j + 2 ≤ M)
    (hband : SeedRoundBandGradeAt S rho M q) :
    ∀ w ∈ rho.honest, ∃ Q : Block V,
      Internal.PhaseGrades.nodeQ2 S (actionReadAt S rho w q) q = some Q :=
  hband.1




/-- **The band grade subsumes `SeedRoundGradedAt`.** Together with
`seedClearCarrierCompatiblePrevious_of_bandGrade`, one strengthened producer
obligation replaces the seed's producer obligation AND its standing premise. -/
theorem seedRoundGraded_of_bandGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hframePrev : ∀ w ∈ rho.honest,
      S.a (q - 1) ≤ rho.horizon ∧
        (healStoreAt S rho w (q - 1)).h_max = M ∧
          (healStoreAt S rho w (q - 1)).h_j + 2 ≤ M)
    (hframe : ∀ w ∈ rho.honest,
      S.a q ≤ rho.horizon ∧
        (healStoreAt S rho w q).h_max = M ∧
          (healStoreAt S rho w q).h_j + 2 ≤ M)
    (hbandPrev : SeedRoundBandGradeAt S rho M (q - 1))
    (hband : SeedRoundBandGradeAt S rho M q) :
    SeedRoundGradedAt S rho q :=
  ⟨seedSelectedGrade_of_bandGrade S adm hfb hframePrev hbandPrev,
    seedSelectedGrade_of_bandGrade S adm hfb hframe hband⟩

/-! ## Producing the band grade -/


/-- **What the band grade needs from the round below.** The honest round-`q`
action carriers have a common ancestor that is itself in the frontier band.

This is the seed's convergence claim in its sharpest form. It fails exactly
when two honest carriers are conflicting band blocks, since their common
ancestor is then below the band and no band block covers both.

design note (statement change, ledger row), as for `SeedRoundBandGradeAt`.
earlier text, byte-exact:

    def SeedBandCarrierCoverAt
        (S: Setup V) (rho: Run V) (M: Height) (q: Round): Prop:=
      ∃ Q: Block V, RunBlock S rho Q ∧
        M - 1 ≤ (derived_state S.E S.cfg Q).h ∧ ActionCarriersCover S rho q Q -/
def SeedBandCarrierCoverAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round) : Prop :=
  ∃ Qn : NamedBlock V, RunBlock S rho Qn ∧
    M - 1 ≤ (Protocol.derive_named S.E S.cfg Qn).h ∧
      ActionCarriersCover S rho q Qn.erase

/-- A band block below an honest carrier reaches every honest store one relay
after the round action. The delivery guard is the gate-off thin-block guard,
so no prior activity of the block at the receiver is needed. -/
private theorem seedBandCover_mem_at
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {Qn : NamedBlock V}
    (hQrun : RunBlock S rho Qn)
    (hQband : M - 1 ≤ (Protocol.derive_named S.E S.cfg Qn).h)
    (hQcover : ActionCarriersCover S rho q Qn.erase)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhorRelay : S.a q + S.E.Δ ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a q + S.E.Δ)).h_max = M ∧
        (rho.storeBeforeTime S w (S.a q + S.E.Δ)).h_j + 2 ≤ M) :
    ∀ w ∈ rho.honest, ∀ read : Time, S.a q + S.E.Δ ≤ read →
      Qn.erase ∈ (rho.storeBeforeTime S w read).T := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  intro w hw read hread
  obtain ⟨p, hp⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hQp : Qn.erase ∈ (rho.storeBeforeTime S p (S.a q)).T :=
    Proofs.NamedSlotFreshness.ancestor_mem_storeBeforeTime S adm.toNamedAdmissibleCore
      (actionSGBlockAt_mem_storeBeforeTime S rho p q) (hQcover p hp)
  obtain ⟨D, hDbodies, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a q) p hQp
  have hDrun : RunBlock S rho D := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedScheduleWellFormed (S.a q)
    refine Proofs.Bridges.runBlock_of_stateBefore_mem S hp (i := n) ?_
    simpa only [Run.storeBeforeTime, hn] using hDbodies
  have hDQ : D = Qn := seedBandRunBlock_unique_of_erase_eq adm hDrun hQrun hDerase
  have hsource : Qn ∈ (rho.storeBeforeTime S p (S.a q)).bodies := by
    rw [← hDQ]; exact hDbodies
  exact (thinBlock_visible_and_stamped_after_oneDelay S adm hsb hp hw hsource
    hQrun hQband hpost rfl hread hhorRelay (hframeRelay w hw).1
    (hframeRelay w hw).2).1


/-- **The cover's witness is the round's common relative grade.** The cover is
delivered to every honest reader one relay after the round action, so it is
active both at the round-`(q+1)` G2-domain read that freezes the relative grade
and at the round-`(q+1)` action read, and the run-level bridge turns the cover
into `NamedGradeFormsAt`.

design note: the selection action never re-evaluates `Protocol.G2`; the
carrier is computed from the frame frozen at the G2-domain cutoff. So the
grade currency of this file's production arm is the RELATIVE grade at that
domain read, and the gate-off frame it needs there is read off the two frame
premises this file already carries: `h_max` is monotone in the reading time and
equals `M` at both ends of `[a_q + Δ, a_{q+1}]`, and `h_j` is monotone and
gate-off at the right end. No premise is added. -/
private theorem seedBandCover_namedGradeForms
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {Qn : NamedBlock V}
    (hQrun : RunBlock S rho Qn)
    (hQband : M - 1 ≤ (Protocol.derive_named S.E S.cfg Qn).h)
    (hQcover : ActionCarriersCover S rho q Qn.erase)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhorAction : S.a (q + 1) ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a q + S.E.Δ)).h_max = M ∧
        (rho.storeBeforeTime S w (S.a q + S.E.Δ)).h_j + 2 ≤ M)
    (hframeAction : ∀ w ∈ rho.honest,
      (healStoreAt S rho w (q + 1)).h_max = M ∧
        (healStoreAt S rho w (q + 1)).h_j + 2 ≤ M) :
    NamedGradeFormsAt S rho (q + 1) Qn.erase := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hrelayAction : S.a q + S.E.Δ ≤ S.a (q + 1) :=
    le_trans (action_add_delta_le_next_Γ_neg1 S q)
      (le_of_lt (next_Γ_neg1_lt_action S q))
  have hhorRelay : S.a q + S.E.Δ ≤ rho.horizon := hrelayAction.trans hhorAction
  have hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (next_Γ_neg1_lt_action S q)).trans hhorAction
  have hmemAt := seedBandCover_mem_at S adm hcom hfb hQrun hQband hQcover
    hpost hhorRelay hframeRelay
  have hM1 : ∀ w ∈ rho.honest, 1 ≤ M := by
    intro w hw
    exact (by decide : (1 : Nat) ≤ 2).trans
      ((Nat.le_add_left 2 (healStoreAt S rho w (q + 1)).h_j).trans
        (hframeAction w hw).2)
  have hactive : ∀ w ∈ rho.honest, Qn.erase ∈
      Protocol.get_filtered_block_tree (healStoreAt S rho w (q + 1)).toFG := by
    intro w hw
    have hmem : Qn.erase ∈ (healStoreAt S rho w (q + 1)).T := by
      simpa only [healStoreAt] using hmemAt w hw (S.a (q + 1)) hrelayAction
    exact frontierBlock_filtered_at_healStoreAt_of_gateOff S adm hsb hw
      hhorAction hmem rfl hQrun hQband (hM1 w hw) (hframeAction w hw).1
      (hframeAction w hw).2
  have hdlo : S.a q + S.E.Δ ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2 := by
    rw [← gammaNeg1_eq_domain_g2_succ S q]
    exact action_add_delta_le_next_Γ_neg1 S q
  have hdhi : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2 ≤ S.a (q + 1) := by
    rw [← gammaNeg1_eq_domain_g2_succ S q]
    exact le_of_lt (next_Γ_neg1_lt_action S q)
  have hretained : ∀ w ∈ rho.honest, Qn.erase ∈
      Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S w (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2)).toHealing.toFG := by
    intro w hw
    have hmaxD : (rho.storeBeforeTime S w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2)).h_max = M := by
      refine le_antisymm ?_ ?_
      · exact le_trans (storeBeforeTime_hMax_mono S
          adm.toNamedScheduleWellFormed w hdhi) (le_of_eq (hframeAction w hw).1)
      · exact le_trans (le_of_eq (hframeRelay w hw).1.symm)
          (storeBeforeTime_hMax_mono S adm.toNamedScheduleWellFormed w hdlo)
    have hgateD : (rho.storeBeforeTime S w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2)).h_j + 2 ≤ M :=
      le_trans (Nat.add_le_add_right
        (seedBandStore_h_j_mono S adm.toNamedScheduleWellFormed w hdhi) 2)
        (hframeAction w hw).2
    exact frontierBlock_filtered_of_gateOff S adm hsb hw
      (hdhi.trans hhorAction) (hmemAt w hw _ hdlo) rfl hQrun hQband
      (hM1 w hw) hmaxD hgateD
  exact namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active S adm
    hmajority hQcover hpost hcut hactive
    (activeDomain_of_retainedAtDomainRead S hretained)

/-- **The band grade, produced.** A band ancestor of the round-`q` carriers is
grade 2 at every honest round-`(q+1)` action read and processed at every honest
vote duty of round `q + 1`. -/
theorem seedBandGrade_of_bandCarrierCover
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hpost : S.E.t_GST ≤ S.a q)
    (hhorAction : S.a (q + 1) ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a q + S.E.Δ)).h_max = M ∧
        (rho.storeBeforeTime S w (S.a q + S.E.Δ)).h_j + 2 ≤ M)
    (hframeAction : ∀ w ∈ rho.honest,
      (healStoreAt S rho w (q + 1)).h_max = M ∧
        (healStoreAt S rho w (q + 1)).h_j + 2 ≤ M)
    (hcover : SeedBandCarrierCoverAt S rho M q) :
    SeedRoundBandGradeAt S rho M (q + 1) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  obtain ⟨Qn, hQrun, hQband, hQcover⟩ := hcover
  have hrelayAction : S.a q + S.E.Δ ≤ S.a (q + 1) :=
    le_trans (action_add_delta_le_next_Γ_neg1 S q)
      (le_of_lt (next_Γ_neg1_lt_action S q))
  have hhorRelay : S.a q + S.E.Δ ≤ rho.horizon := hrelayAction.trans hhorAction
  have hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (next_Γ_neg1_lt_action S q)).trans hhorAction
  have hmemAt := seedBandCover_mem_at S adm hcom hfb hQrun hQband hQcover
    hpost hhorRelay hframeRelay
  have hactiveAt : ∀ w ∈ rho.honest, Qn.erase ∈
      Protocol.get_filtered_block_tree (healStoreAt S rho w (q + 1)).toFG := by
    intro w hw
    have hM1 : 1 ≤ M :=
      (by decide : (1 : Nat) ≤ 2).trans
        ((Nat.le_add_left 2 (healStoreAt S rho w (q + 1)).h_j).trans
          (hframeAction w hw).2)
    have hmem : Qn.erase ∈ (healStoreAt S rho w (q + 1)).T := by
      simpa only [healStoreAt] using hmemAt w hw (S.a (q + 1)) hrelayAction
    exact frontierBlock_filtered_at_healStoreAt_of_gateOff S adm hsb hw
      hhorAction hmem rfl hQrun hQband hM1 (hframeAction w hw).1
      (hframeAction w hw).2
  refine ⟨?_, ?_⟩
  · -- the prepared selection, from the common named grade at the action read
    have hforms : NamedGradeFormsAt S rho (q + 1) Qn.erase :=
      seedBandCover_namedGradeForms S adm hcom hfb hQrun hQband hQcover hpost
        hhorAction hframeRelay hframeAction
    intro v hv
    have hactiveRead : Qn.erase ∈
        Internal.PhaseGrades.filteredTree (actionReadAt S rho v (q + 1)) := by
      show Qn.erase ∈ Protocol.get_filtered_block_tree
        (actionStoreAt S rho v (q + 1)).toHealing.toFG
      rw [actionStoreAt_filteredTree S rho v (q + 1)]
      exact hactiveAt v hv
    obtain ⟨Q, hQ, -⟩ := namedGradeFormsAt_preceq_actionQ2 S
      adm.toNamedAdmissibleCore (Nat.succ_pos q) hhorAction hforms hv
      hactiveRead
    exact ⟨Q, hQ⟩
  intro w hw
  have hM1 : 1 ≤ M :=
    (by decide : (1 : Nat) ≤ 2).trans
      ((Nat.le_add_left 2 (healStoreAt S rho w (q + 1)).h_j).trans
        (hframeAction w hw).2)
  refine ⟨Qn, hQrun, hQband, ?_, ?_⟩
  · have hactiveW : Qn.erase ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w (q + 1)).toFG := by
      have hmem : Qn.erase ∈ (healStoreAt S rho w (q + 1)).T := by
        simpa only [healStoreAt] using
          hmemAt w hw (S.a (q + 1)) hrelayAction
      exact frontierBlock_filtered_at_healStoreAt_of_gateOff S adm hsb hw
        hhorAction hmem rfl hQrun hQband hM1 (hframeAction w hw).1
        (hframeAction w hw).2
    exact seedG2_of_actionCarriersCover_at_store S adm hmajority hw hQcover
      hpost hcut hactiveW
  · intro d hlo hhi
    have hvote : S.a q + S.E.Δ ≤ Protocol.vote_time S.E d := by
      refine (action_add_delta_le_next_Γ_neg1 S q).trans ?_
      refine (le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (q + 1))).trans ?_
      refine (le_of_lt (Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (q + 1))).trans ?_
      rw [Protocol.Γ_1_eq_vote_time S.hc S.E (q + 1)]
      exact Protocol.vote_time_mono_slots S.E hlo
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hmemAt w hw (Protocol.vote_time S.E d) hvote

/-! ## The cover propagates -/




/-- **The band-carrier cover propagates one round, with the SAME witness.**

The cover at round `q` grades its own witness at every honest round-`(q+1)`
action store, and a graded block is at or below the reader's own carrier, so the
same block covers the round-`(q+1)` carriers. Convergence at band height is
therefore an INITIALISATION claim, not a recurring one: once it holds at one
round of the gate-off window it holds at every later round of the window.

design note (proof change only; the statement is the earlier one with the named
witness of `SeedBandCarrierCoverAt`): the selection action reads the grade frozen
at the round's G2-domain cutoff, so the second step is the run-level
`preceq_actionSGBlockAt_of_namedGradeFormsAt` on the relative grade that
`seedBandCover_namedGradeForms` produces from the very same premises, in place
of the per-reader absolute-grade step `seedGradedBlock_preceq_actionCarrier
_at_store` (blocked above). No hypothesis is added. -/
theorem seedBandCarrierCover_succ
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round}
    (hpost : S.E.t_GST ≤ S.a q)
    (hhorAction : S.a (q + 1) ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a q + S.E.Δ)).h_max = M ∧
        (rho.storeBeforeTime S w (S.a q + S.E.Δ)).h_j + 2 ≤ M)
    (hframeAction : ∀ w ∈ rho.honest,
      (healStoreAt S rho w (q + 1)).h_max = M ∧
        (healStoreAt S rho w (q + 1)).h_j + 2 ≤ M)
    (hcover : SeedBandCarrierCoverAt S rho M q) :
    SeedBandCarrierCoverAt S rho M (q + 1) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨Qn, hQrun, hQband, hQcover⟩ := hcover
  have hrelayAction : S.a q + S.E.Δ ≤ S.a (q + 1) :=
    le_trans (action_add_delta_le_next_Γ_neg1 S q)
      (le_of_lt (next_Γ_neg1_lt_action S q))
  have hmemAt := seedBandCover_mem_at S adm hcom hfb hQrun hQband hQcover
    hpost (hrelayAction.trans hhorAction) hframeRelay
  have hforms := seedBandCover_namedGradeForms S adm hcom hfb hQrun hQband
    hQcover hpost hhorAction hframeRelay hframeAction
  refine ⟨Qn, hQrun, hQband, ?_⟩
  intro w hw
  have hM1 : 1 ≤ M :=
    (by decide : (1 : Nat) ≤ 2).trans
      ((Nat.le_add_left 2 (healStoreAt S rho w (q + 1)).h_j).trans
        (hframeAction w hw).2)
  have hactiveW : Qn.erase ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w (q + 1)).toFG := by
    have hmem : Qn.erase ∈ (healStoreAt S rho w (q + 1)).T := by
      simpa only [healStoreAt] using hmemAt w hw (S.a (q + 1)) hrelayAction
    exact frontierBlock_filtered_at_healStoreAt_of_gateOff S adm hsb hw
      hhorAction hmem rfl hQrun hQband hM1 (hframeAction w hw).1
      (hframeAction w hw).2
  have hactiveRead : Qn.erase ∈ PhaseGrades.filteredTree
      (actionReadAt S rho w (q + 1)) := by
    show Qn.erase ∈ Protocol.get_filtered_block_tree
      (actionStoreAt S rho w (q + 1)).toHealing.toFG
    rw [actionStoreAt_filteredTree S rho w (q + 1)]
    exact hactiveW
  exact preceq_actionSGBlockAt_of_namedGradeFormsAt S adm.toNamedAdmissibleCore
    (Nat.succ_pos q) hhorAction hforms hw hactiveRead

/-- **The cover carried across a stretch of the gate-off window.** One cover
at `lo` gives a cover at every round of `[lo, hi]`, with the same witness. -/
theorem seedBandCarrierCover_through
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {lo hi : Round}
    (hpost : S.E.t_GST ≤ S.a lo)
    (hhor : S.a hi ≤ rho.horizon)
    (hframe : ∀ read : Time, S.a lo ≤ read → read ≤ S.a hi →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M)
    (hcover : SeedBandCarrierCoverAt S rho M lo) :
    ∀ k : Round, lo ≤ k → k ≤ hi → SeedBandCarrierCoverAt S rho M k := by
  intro k hlo
  induction k, hlo using Nat.le_induction with
  | base => intro _; exact hcover
  | succ n hn ih =>
    intro hhi
    have hnhi : n ≤ hi := le_trans (Nat.le_succ n) hhi
    have hrelayAction : S.a n + S.E.Δ ≤ S.a (n + 1) :=
      le_trans (action_add_delta_le_next_Γ_neg1 S n)
        (le_of_lt (next_Γ_neg1_lt_action S n))
    refine seedBandCarrierCover_succ S adm hcom hfb
      (hpost.trans (Assembly.a_mono S hn))
      ((Assembly.a_mono S hhi).trans hhor) ?_ ?_ (ih hnhi)
    · intro w hw
      have h := hframe (S.a n + S.E.Δ)
        (le_trans (Assembly.a_mono S hn)
          (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)))
        (hrelayAction.trans (Assembly.a_mono S hhi)) w hw
      exact ⟨h.2, h.1⟩
    · intro w hw
      have h := hframe (S.a (n + 1))
        (Assembly.a_mono S (hn.trans (Nat.le_succ n)))
        (Assembly.a_mono S hhi) w hw
      exact ⟨by simpa only [healStoreAt] using h.2,
        by simpa only [healStoreAt] using h.1⟩


/-! ## The cover as a common grade -/



end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms seedG1_at_voteDuty_of_ownG2
#print axioms seedFreshAnchor_isSome_of_bandGrade
#print axioms seedClearCarrierCompatiblePrevious_of_bandGrade
#print axioms seedSelectedGrade_of_bandGrade
#print axioms seedRoundGraded_of_bandGrade
#print axioms seedBandGrade_of_bandCarrierCover
#print axioms seedBandCarrierCover_succ
#print axioms seedBandCarrierCover_through
end DecoupledConsensusModel.Proofs.HealingSurface

end
