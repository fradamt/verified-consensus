module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Store.HonestPoolActionBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol (positive opposing gradeBool localCovers
  readyView rawView freezeRoot)
open DecoupledConsensusModel.Protocol (rawInputs interpretedInputs bodyReady)
open DecoupledConsensusModel.Protocol (early late domain)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The relative grade is monotone under `Preceq`

Copied from the private block of `FixedHeightRootOpeningParentRun`
(`fixedRoot_confirmation_*_mono`), which owns the same four facts but keeps
them private and behind the `SeedCeilingStepRun` import chain. -/

omit [Fintype V] in
private theorem seedQ2_localCovers_mono
    {A B : Block V} {gv : Protocol.GradeView V} {key : Option BlockId}
    (hAB : Block.Preceq A B)
    (hB : DecoupledConsensusModel.Protocol.localCovers gv key B = true) :
    DecoupledConsensusModel.Protocol.localCovers gv key A = true := by
  unfold DecoupledConsensusModel.Protocol.localCovers at hB ⊢
  unfold Protocol.head_covers at hB ⊢
  cases key with
  | none => exact hB
  | some root =>
      dsimp only at hB ⊢
      cases hfind : Block.find? gv.T root with
      | none => rw [hfind] at hB; exact absurd hB (by simp)
      | some head =>
          rw [hfind] at hB
          exact Block.preceq_trans hAB hB

omit [Fintype V] in
private theorem seedQ2_positive_mono
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hB : DecoupledConsensusModel.Protocol.positive gv F eta r early late v B = true) :
    DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hB ⊢
  rcases hB with ⟨u, hu, hmax, hcov, hclean, hlate⟩
  refine ⟨u, hu, hmax, seedQ2_localCovers_mono hAB hcov, hclean, ?_⟩
  intro x hx hlt
  exact seedQ2_localCovers_mono hAB (hlate x hx hlt)

omit [Fintype V] in
private theorem seedQ2_opposing_mono
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hA : DecoupledConsensusModel.Protocol.opposing gv F eta r early late v A = true) :
    DecoupledConsensusModel.Protocol.opposing gv F eta r early late v B = true := by
  simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hA ⊢
  rcases hA with ⟨x, hx, hmax, hnot⟩ | ⟨x, hx, y, hy, hmax, heq, hkey⟩
  · left
    refine ⟨x, hx, hmax, ?_⟩
    intro hcov
    exact hnot (seedQ2_localCovers_mono hAB hcov)
  · exact Or.inr ⟨x, hx, y, hy, hmax, heq, hkey⟩

/-- An ancestor of a graded block is graded in the same window and view. -/
private theorem seedQ2_gradeBool_mono
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) {A B : Block V}
    (hAB : Block.Preceq A B)
    (hB : DecoupledConsensusModel.Protocol.gradeBool E gv F eta r early late B = true) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta r early late A = true := by
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at hB ⊢
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F eta r early late v A = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F eta r early late v B = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      seedQ2_opposing_mono hAB gv F eta r early late v
        (Finset.mem_filter.mp hv).2⟩
  have hPos : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F eta r early late v B = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      seedQ2_positive_mono hAB gv F eta r early late v
        (Finset.mem_filter.mp hv).2⟩
  have e1 := E.electorate.weightOf_mono hOpp
  have e2 := E.electorate.weightOf_mono hPos
  omega

/-! ## The G1 grade of the action's selected candidate -/

/-- **The selected action candidate carries the round's G1 grade.** The named
twin of earlier's `G2_imp_G1` step in the seed's lifecycle-source chain.

The candidate is the round's G2 phase root of this validator, frozen at its own
G2 domain tick, clipped against the action read's finalized block and projected
on the action read's filtered tree. So it is at or below the unclipped freeze
root, which is graded in the G2 window at the G2 domain read; that grade crosses
to the G1 window at the G1 domain read by `q10_grade_cross` (the projected value
is above the G1 tick's finalized block, which is what that crossing needs), and
descends to the candidate because the relative grade is monotone under
`Preceq`. -/
theorem namedG1At_of_nodeQ2
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) {q : Round}
    (hq : 0 < q) (hhor : S.a q ≤ rho.horizon) :
    ∀ v ∈ rho.honest, ∀ Q : Block V,
      nodeQ2 S (actionReadAt S rho v q) q = some Q → namedG1At S rho v q Q := by
  intro v hv Q hQ
  have core : NamedAdmissibleCore S rho := adm.toNamedAdmissibleCore
  have sch := core.toNamedScheduleWellFormed
  -- the read's selector, unfolded on its completed frame
  have hQ' : DecoupledConsensusModel.Protocol.grade2Block
      (actionReadAt S rho v q).st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v q).cache
        (actionReadAt S rho v q).st.core.toHealing q) = some Q := hQ
  unfold DecoupledConsensusModel.Protocol.grade2Block at hQ'
  rw [if_pos (actionFrame_allClosed S core hv hq hhor),
    actionFrame_g2 S core hv hq hhor, Option.bind_some, id_eq] at hQ'
  obtain ⟨g2c, hg2c, hact⟩ := Option.bind_eq_some_iff.mp hQ'
  obtain ⟨raw, hfz, hclip⟩ := Option.map_eq_some_iff.mp hg2c
  -- the selected value is in the filtered tree and below the clipped freeze
  have hQmem : Q ∈ Protocol.get_filtered_block_tree
      (actionReadAt S rho v q).st.core.toHealing.toFG :=
    NamedProposalParent.activePrefix_mem _ g2c Q hact
  have hQle : Block.Preceq Q g2c := by
    unfold DecoupledConsensusModel.Protocol.activePrefix at hact
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hact)).2
  have hFQ : Block.Preceq (actionReadAt S rho v q).st.core.F Q :=
    NamedOutageClosure.q10_filtered_F hQmem
  have hcompat : Block.compatible Q (actionReadAt S rho v q).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFQ
  have hQraw : Block.Preceq Q raw :=
    (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho v q).st.core.F Q hcompat).mp (by rw [hclip]; exact hQle)
  -- the unclipped freeze root is graded in the G2 window at the G2 domain read
  have hgraderaw : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) v).st.core.F
      S.hc.η_SG q (DecoupledConsensusModel.Protocol.early S.E S.hc q .g2)
      (DecoupledConsensusModel.Protocol.late S.E S.hc q .g2) raw = true :=
    (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hfz)).2
  -- the G1 tick's finalized block is below the freeze root
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g1) v).st.core.F
      (actionReadAt S rho v q).st.core.F := by
    show Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g1) v).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a q) v).st.core.F
    rw [NamedOutageClosure.strict_read_eq_index S rho sch.sorted
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g1),
      NamedOutageClosure.strict_read_eq_index S rho sch.sorted (S.a q)]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho v
      (NamedOutageClosure.strict_lengths_mono rho
        (NamedOutageClosure.q10_domain_lt_a S q .g1).le)
  have hFB : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g1) v).st.core.F raw :=
    Block.preceq_trans hFmono (Block.preceq_trans hFQ hQraw)
  -- the grade crosses the two ticks, then descends to the selected value
  have hg1raw := NamedOutageClosure.q10_grade_cross S rho core v hv q hq raw
    hFB hgraderaw
  exact seedQ2_gradeBool_mono S.E _ _ _ _ _ _ hQraw hg1raw


/-! ## Genesis is relatively graded at every honest round read

earlier's `g2_exists_at_action` (`SeedCanonicalAnchorRun`, earlier tree) grades
`Block.genesis` in every honest action store: every honest head covers genesis,
so the absolute direct support of genesis is the whole honest weight, which is
at least `m`. The relative twin below is the same argument in the relative
vocabulary, and it is *cheaper*, not dearer: `covers _ Block.genesis` is free
for every body-ready token, so an honest sender can neither oppose genesis on
the covering arm nor on the equivocation arm, and the trichotomy
`q10_supports_of_not_opposes` turns a non-empty early view straight into
positive support. `GradeFormingMajority` then outweighs the opponents, who are
all faulty.

Both inputs come from the seed's own gate-off frame:
`gradeFormingMajority_of_admissible_belowOneThird` and
`relativeCarrierWindowAt_of_gateOff` (`RelativeCarrierWindowGateOffRun`). -/

/-- Every raw phase input of an honest sender at a strict read is that sender's
own action SG projection of the input's round. -/
private theorem seedQ2_rawInput_eq_action
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w u : V} (hu : u ∈ rho.honest) {t : Time} {r : Round} {cutoff : Time}
    {z : Protocol.SGVote V}
    (hz : z ∈ rawInputs
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      S.hc.η_SG r cutoff u) :
    ∃ k, z = actionSGVoteAt S rho u k := by
  have hzdata := Finset.mem_filter.mp hz
  obtain ⟨k, _, hzk⟩ := Finset.mem_biUnion.mp hzdata.1
  have hzStore : z ∈ (rho.storeBeforeTime S w t).toHealing.sg_votes k := by
    simpa only [Run.storeBeforeTime, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hzk
  exact ⟨k, honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
    S adm hu hzStore hzdata.2.1⟩

/-- A body-ready input of an honest sender covers `Block.genesis`: its key is
the sender's own action carrier root, and body open is exactly the tree
lookup that `head_covers` performs. -/
private theorem seedQ2_readyInput_covers_genesis
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w u : V} (hu : u ∈ rho.honest) {t : Time} {r : Round}
    {cutoff : Time} {z : Protocol.SGVote V}
    (hz : z ∈ interpretedInputs
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F S.hc.η_SG r cutoff u) :
    localCovers (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      z.confirmed Block.genesis = true := by
  have hzdata := Finset.mem_filter.mp hz
  obtain ⟨k, hzk⟩ := seedQ2_rawInput_eq_action S adm hu hzdata.1
  have hconf : z.confirmed = some (actionSGBlockAt S rho u k).root := by
    rw [hzk]
    exact (actionSGVoteAt_shape S rho u k).2.2
  have hready := hzdata.2
  rw [show bodyReady
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F cutoff z =
    bodyReady
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F cutoff z from rfl] at hready
  unfold bodyReady at hready
  rw [hconf] at hready ⊢
  unfold localCovers Protocol.head_covers
  dsimp only at hready ⊢
  cases hfind : Block.find?
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView.T
      (actionSGBlockAt S rho u k).root with
  | none => rw [hfind] at hready; exact absurd hready (by simp)
  | some H => exact Protocol.preceq_genesis H

/-- An honest sender never opposes `Block.genesis` at an honest strict read. -/
private theorem seedQ2_honest_not_opposing_genesis
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w u : V} (hu : u ∈ rho.honest) {t : Time} {r : Round} {ea la : Time}
    (hopp : opposing
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F S.hc.η_SG r ea la u
      Block.genesis = true) : False := by
  simp only [opposing, decide_eq_true_eq] at hopp
  rcases hopp with ⟨x, hx, _hmax, hnot⟩ | ⟨x, hx, y, hy, _hmax, hround, hkey⟩
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact hnot (seedQ2_readyInput_covers_genesis S adm hu hz)
  · obtain ⟨zx, hzx, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨zy, hzy, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨kx, hkx⟩ := seedQ2_rawInput_eq_action S adm hu hzx
    obtain ⟨ky, hky⟩ := seedQ2_rawInput_eq_action S adm hu hzy
    have hxr : zx.round = kx := by
      rw [hkx]; exact (actionSGVoteAt_shape S rho u kx).2.1
    have hyr : zy.round = ky := by
      rw [hky]; exact (actionSGVoteAt_shape S rho u ky).2.1
    have hkk : kx = ky := by
      change zx.round = zy.round at hround
      rw [hxr, hyr] at hround
      exact hround
    apply hkey
    change zx.confirmed = zy.confirmed
    rw [hkx, hky, hkk]

/-- An honest sender with a non-empty early view supports `Block.genesis`. -/
private theorem seedQ2_honest_positive_genesis
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w u : V} (hu : u ∈ rho.honest) {t : Time} {r : Round} {ea la : Time}
    (hcut : ea ≤ la)
    (hne : (readyView
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F S.hc.η_SG r ea u).Nonempty) :
    positive (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F S.hc.η_SG r ea la u
      Block.genesis = true := by
  simp only [positive, decide_eq_true_eq]
  refine NamedOutageClosure.q10_supports_of_not_opposes _
    (NamedOutageClosure.q10_readyView_cut _ _ _ _ hcut u) hne ?_
  intro hopp
  exact seedQ2_honest_not_opposing_genesis S adm hu (r := r) (ea := ea) (la := la)
    (by simp only [opposing, decide_eq_true_eq]; exact hopp)

/-- **The relative grade of `Block.genesis` at every honest phase-domain read.**
At `p =.g2` this is the grade half of `NamedGradeFormsAt S rho c Block.genesis`,
and it is earlier's `g2_exists_at_action` argument (`SeedGradeExistenceRun`, earlier
tree) carried into the relative vocabulary.

Genesis has no ancestors, so `Protocol.head_covers _ Block.genesis` succeeds on
every body-ready token: an honest sender can oppose genesis neither on the
covering arm nor on the equivocation arm, and the trichotomy
`q10_supports_of_not_opposes` turns its non-empty early view straight into
positive support. `GradeFormingMajority` then outweighs the opponents, who are
all faulty. Both inputs are the seed's gate-off window, through
`gradeFormingMajority_of_admissible_belowOneThird` and
`relativeCarrierWindowAt_of_gateOff`.

The phase is a parameter because nothing in the argument is phase-specific: the
window producer is already phase-generic, and genesis is unopposed in every
window. `.g2` feeds K2 (`nodeRawG2_of_gateOffFrame`) and `.g0` feeds K3's
frame root (`actionFrame_g0Root_of_gateOffFrame`).

The three frame facts are the unfolded `GateOffFrameAt S rho M (c - 1) c`
clauses those producers consume; they are taken unfolded so that this module
stays out of the seed import cone. -/
theorem relativeGrade_genesis_of_gateOffWindow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 0 < c) (p : DecoupledConsensusModel.Protocol.Phase)
    (hhor : S.a c ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M)
    (hfrontier : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_max = M)
    (hgateOff : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_j + 2 ≤ M) :
    ∀ v ∈ rho.honest,
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho (domain S.E S.hc c p) v).st c p
        Block.genesis = true := by
  have hdomHorG2 : domain S.E S.hc c .g2 ≤ rho.horizon :=
    (NamedOutageClosure.q10_domain_lt_a S c .g2).le.trans hhor
  have hdomHorP : domain S.E S.hc c p ≤ rho.horizon :=
    (NamedOutageClosure.q10_domain_lt_a S c p).le.trans hhor
  have hmaj : Internal.NamedOutageEntry.GradeFormingMajority S rho c :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hfb hc hdomHorG2 (by assumption)
  have hwindow : RelativeCarrierWindowAt S rho (c - 1) p :=
    relativeCarrierWindowAt_of_gateOff S adm hfb hc hpost hprev hfrontier
      hgateOff hdomHorP
  have hpred : c - 1 + 1 = c := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hc)
  intro v hv
  -- the reader's own phase-domain read
  set n := NamedRun.stateBeforeTime S rho (domain S.E S.hc c p) v with hn
  -- every honest round-(c-1) voter supports genesis at that read
  have hpositive : Internal.NamedOutageEntry.honestRoundVoters S rho (c - 1) ⊆
      Finset.univ.filter fun u =>
        positive n.st.core.toHealing.gradeView n.st.core.F S.hc.η_SG c
          (early S.E S.hc c p) (late S.E S.hc c p) u Block.genesis = true := by
    intro u hu
    have huHon : u ∈ rho.honest :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (c - 1)).mp hu).1
    obtain ⟨y, hy, -, -, -⟩ := hwindow v hv u hu
    have hyv : y ∈ interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (c - 1 + 1) p) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (c - 1 + 1) p) v).st.core.F
        S.hc.η_SG (c - 1 + 1) (early S.E S.hc (c - 1 + 1) p) u := hy
    rw [hpred] at hyv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ u,
      seedQ2_honest_positive_genesis S adm huHon
        (NamedOutageClosure.q10_early_le_late S c p)
        ⟨DecoupledConsensusModel.Protocol.token y, Finset.mem_image_of_mem _ hyv⟩⟩
  have hopposing : (Finset.univ.filter fun u =>
      opposing n.st.core.toHealing.gradeView n.st.core.F S.hc.η_SG c
        (early S.E S.hc c p) (late S.E S.hc c p) u Block.genesis = true) ⊆
      (Finset.univ \ rho.honest) ∪
        Internal.NamedOutageEntry.staleHistoricalVoters S rho c := by
    intro u hu
    refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, ?_⟩)
    intro huHon
    exact seedQ2_honest_not_opposing_genesis S adm huHon
      (Finset.mem_filter.mp hu).2
  exact phaseGrade_of_gradeFormingMajority S rho c _ _ Block.genesis _ _
    hmaj hpositive hopposing


/-- The reader's own phase-`p` freeze root exists at every honest read of the
gate-off window: genesis is graded there and `q10_freeze_of_graded` turns a
graded processed block into the freeze. -/
theorem storeRoot_isSome_of_gateOffWindow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 0 < c) (p : DecoupledConsensusModel.Protocol.Phase)
    (hhor : S.a c ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M)
    (hfrontier : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_max = M)
    (hgateOff : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_j + 2 ≤ M) :
    ∀ v ∈ rho.honest, ∃ raw : Block V,
      PhaseGrades.storeRoot S.E S.hc
        (PhaseGrades.readAt S rho (domain S.E S.hc c p) v).st c p = some raw := by
  have sch := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hgrades := relativeGrade_genesis_of_gateOffWindow S adm hfb hc p hhor
    hpost hprev hfrontier hgateOff
  intro v hv
  set n := NamedRun.stateBeforeTime S rho (domain S.E S.hc c p) v with hn
  have hgrade : gradeBool S.E n.st.core.toHealing.gradeView n.st.core.F
      S.hc.η_SG c (early S.E S.hc c p) (late S.E S.hc c p)
      Block.genesis = true := hgrades v hv
  have hmem : Block.genesis ∈ n.st.core.toHealing.gradeView.T := by
    simpa only [hn, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using
      (Protocol.genesis_mem_and_stamp_storeBeforeTime S sch v
        (domain S.E S.hc c p) (domain S.E S.hc c p)).1
  obtain ⟨raw, hfz, -⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    n.st.core.toHealing.gradeView n.st.core.F S.hc.η_SG c
    (NamedOutageClosure.q10_early_le_late S c p) hmem hgrade
  exact ⟨raw, hfz⟩



/-- **K2 in the relative vocabulary.** Under the seed's gate-off window every
honest action read of round `c` carries a raw grade-2 root.

`nodeRawG2` is the frame's RAW flag: `actionFrame_g2` identifies the action
frame's G2 slot with the reader's own G2-domain freeze, and `freezeRoot` ranges
over the reader's processed tree `gv.T`, NOT over its filtered tree. So the
graded witness only has to be processed, which genesis always is
(`genesis_mem_and_stamp_storeBeforeTime`), and the projection step that
`namedGradeFormsAt_preceq_actionQ2` performs is not on this path at all. See
the Open below for why that route cannot be taken with `C:= Block.genesis`. -/
theorem nodeRawG2_of_gateOffFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 0 < c)
    (hhor : S.a c ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M)
    (hfrontier : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_max = M)
    (hgateOff : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_j + 2 ≤ M) :
    ∀ v ∈ rho.honest, nodeRawG2 S (actionReadAt S rho v c) c := by
  have core : NamedAdmissibleCore S rho := adm.toNamedAdmissibleCore
  have hroots := storeRoot_isSome_of_gateOffWindow S adm hfb hc .g2 hhor
    hpost hprev hfrontier hgateOff
  intro v hv
  obtain ⟨raw, hfz⟩ := hroots v hv
  show ((DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v c).cache
    (actionReadAt S rho v c).st.core.toHealing c).g2.bind id).isSome = true
  rw [actionFrame_g2 S core hv hc hhor, Option.bind_some, id_eq,
    show PhaseGrades.storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc c .g2) v).st c .g2 = some raw from hfz]
  rfl








end HealingSurface
end Proofs
end DecoupledConsensusModel

end
