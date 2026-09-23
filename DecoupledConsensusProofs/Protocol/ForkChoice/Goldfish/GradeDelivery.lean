module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Handlers.AdoptionConstructor
public import DecoupledConsensusProofs.Protocol.Grades.CarrierAdmission
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroHeadResolution
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RoundZero
public import DecoupledConsensusProofs.Protocol.Grades.Ladder
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame

@[expose] public section

/-!
# Fixed-cutoff grade delivery from an admissible run

This file produces `Internal.HealingSurface.HonestGradeDelivery` from the final
Section 7 execution contract. The proof has two independent parts:

* pure batch algebra says that delivery of one resolved support vote either
  preserves the selected support head or exposes a received equivocation; and
* the run layer forwards both the SG attestation and, when non-genesis, the
  block that resolves its confirmed root.

The second transport is necessary because SG attestations are admitted at
receipt and can remain unresolved until their confirmed block arrives.
-/

/-! ## 1. The batch order is a finite strict total order on one validator-round fibre -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace GradeDeliveryRun

open Internal
open Execution
open Internal.PhaseGrades
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]




/-- `none` is the `+∞` timestamp used by the batch order. -/
private def occurrenceKey : Occurrence → WithTop Stamp
  | none => ⊤
  | some t => t

/-- `none` is the least confirmed-root tie-break. -/
private def headKey : Option BlockId → WithBot BlockId
  | none => ⊥
  | some r => r

/-- The lexicographic key implemented by `Protocol.batch_before`. -/
private def batchKey (ts : TimestampMap (Protocol.SGVote V))
    (u : Protocol.SGVote V) : Lex (WithTop Stamp × WithBot BlockId) :=
  toLex (occurrenceKey (ts u), headKey u.confirmed)

omit [DecidableEq V] [Fintype V] in
private theorem batch_before_eq_key_lt
    (ts : TimestampMap (Protocol.SGVote V))
    (u w : Protocol.SGVote V) :
    Protocol.batch_before ts u w = decide (batchKey ts u < batchKey ts w) := by
  cases hu : ts u <;> cases hw : ts w <;>
    cases hur : u.confirmed <;> cases hwr : w.confirmed <;>
    simp [Protocol.batch_before, batchKey, occurrenceKey, headKey,
      Protocol.head_lt, hu, hw, hur, hwr, Prod.Lex.toLex_lt_toLex]

omit [DecidableEq V] [Fintype V] in
private theorem batchKey_injective_on_fibre
    (ts : TimestampMap (Protocol.SGVote V))
    {v : V} {r : Round} {u w : Protocol.SGVote V}
    (huv : u.val_index = v) (hur : u.round = r)
    (hwv : w.val_index = v) (hwr : w.round = r)
    (hkey : batchKey ts u = batchKey ts w) : u = w := by
  have hp : (occurrenceKey (ts u), headKey u.confirmed) =
      (occurrenceKey (ts w), headKey w.confirmed) :=
    toLex.injective hkey
  have hh : u.confirmed = w.confirmed := by
    have := congrArg Prod.snd hp
    cases hu : u.confirmed <;> cases hw : w.confirmed <;>
      simp [headKey, hu, hw] at this ⊢
    exact this
  cases u with
  | mk uv ur uh =>
      cases w with
      | mk wv wr wh =>
          simp only at huv hur hwv hwr hh
          subst uv
          subst ur
          subst wv
          subst wr
          simpa using hh

omit [Fintype V] in
private theorem batch_first_exists_on_fibre
    (ts : TimestampMap (Protocol.SGVote V))
    {batch : Finset (Protocol.SGVote V)} {v : V} {r : Round}
    (hne : batch.Nonempty)
    (hfibre : ∀ u ∈ batch, u.val_index = v ∧ u.round = r) :
    ∃ first : Protocol.SGVote V,
      Protocol.batch_first? ts batch = some first := by
  let key : Protocol.SGVote V → Lex (WithTop Stamp × WithBot BlockId) :=
    batchKey ts
  obtain ⟨first, hfirst, hmin⟩ := Finset.exists_mem_eq_inf' hne key
  have hpasses : Protocol.is_first_in ts batch first = true := by
    simp only [Protocol.is_first_in, decide_eq_true_eq]
    intro u hu
    rw [batch_before_eq_key_lt]
    simp only [decide_eq_false_iff_not]
    have hle : key first ≤ key u := by
      rw [← hmin]
      exact Finset.inf'_le key hu
    exact not_lt_of_ge hle
  have hunique : ∀ u ∈ batch, Protocol.is_first_in ts batch u = true → u = first := by
    intro u hu hpass
    have hleUF : key u ≤ key first := by
      simp only [Protocol.is_first_in, decide_eq_true_eq] at hpass
      have hnot := hpass first hfirst
      rw [batch_before_eq_key_lt] at hnot
      exact le_of_not_gt (by simpa only [decide_eq_false_iff_not] using hnot)
    have hleFU : key first ≤ key u := by
      rw [← hmin]
      exact Finset.inf'_le key hu
    have hkey : key u = key first := le_antisymm hleUF hleFU
    exact batchKey_injective_on_fibre ts
      (hfibre u hu).1 (hfibre u hu).2
      (hfibre first hfirst).1 (hfibre first hfirst).2 hkey
  refine ⟨first, ?_⟩
  unfold Protocol.batch_first?
  exact Protocol.pickUnique?_eq_some hfirst hpasses hunique

omit [Fintype V] in
private theorem batch_first_mem_and_min
    (ts : TimestampMap (Protocol.SGVote V))
    {batch : Finset (Protocol.SGVote V)} {first : Protocol.SGVote V}
    (hfirst : Protocol.batch_first? ts batch = some first) :
    first ∈ batch ∧ ∀ u ∈ batch, ¬ batchKey ts u < batchKey ts first := by
  have hmem : first ∈ batch := by
    unfold Protocol.batch_first? at hfirst
    exact Proofs.Engine.pickUnique?_mem hfirst
  refine ⟨hmem, ?_⟩
  intro u hu
  have hpass : Protocol.is_first_in ts batch first = true := by
    unfold Protocol.batch_first? pickUnique? at hfirst
    split at hfirst
    · rename_i hex
      have hs := Finset.choose_spec
        (fun x : Protocol.SGVote V => Protocol.is_first_in ts batch x = true)
        batch hex
      rw [← Option.some.inj hfirst]
      exact hs.2
    · exact absurd hfirst (by simp)
  simp only [Protocol.is_first_in, decide_eq_true_eq] at hpass
  have hfalse := hpass u hu
  rw [batch_before_eq_key_lt] at hfalse
  simpa only [decide_eq_false_iff_not] using hfalse

omit [DecidableEq V] [Fintype V] in
private theorem occurrenceBefore_of_batchKey_le
    (ts : TimestampMap (Protocol.SGVote V))
    {u w : Protocol.SGVote V} {Γ : Time}
    (hle : batchKey ts u ≤ batchKey ts w)
    (hw : occurrenceBefore (ts w) Γ = true) :
    occurrenceBefore (ts u) Γ = true := by
  cases hu : ts u with
  | none =>
      cases hwv : ts w with
      | none => simp [hwv, occurrenceBefore] at hw
      | some cw =>
          simp only [batchKey, occurrenceKey, hu, hwv,
            Prod.Lex.toLex_le_toLex] at hle
          rcases hle with h | ⟨h, -⟩ <;> simp at h
  | some cu =>
      cases hwv : ts w with
      | none => simp [hwv, occurrenceBefore] at hw
      | some cw =>
          simp only [occurrenceBefore, hwv, decide_eq_true_eq] at hw
          simp only [occurrenceBefore, decide_eq_true_eq]
          simp only [batchKey, occurrenceKey, hu, hwv,
            Prod.Lex.toLex_le_toLex] at hle
          rcases hle with h | ⟨h, -⟩
          · exact lt_trans (by simpa using h) hw
          · have h' : cu = cw := by simpa using h
            rw [h']
            exact hw

omit [Fintype V] in
private theorem batch_first_stamp_before
    (ts : TimestampMap (Protocol.SGVote V))
    {batch : Finset (Protocol.SGVote V)} {first u : Protocol.SGVote V}
    {Γ : Time} (hfirst : Protocol.batch_first? ts batch = some first)
    (hu : u ∈ batch) (huΓ : occurrenceBefore (ts u) Γ = true) :
    occurrenceBefore (ts first) Γ = true := by
  obtain ⟨-, hmin⟩ := batch_first_mem_and_min ts hfirst
  exact occurrenceBefore_of_batchKey_le ts
    (le_of_not_gt (hmin u hu)) huΓ

omit [Fintype V] in
/-- Two differently headed votes received before one cutoff force the summary's
equivocation instant below that cutoff. -/
theorem equivocation_before_of_two
    (ts : TimestampMap (Protocol.SGVote V))
    {batch : Finset (Protocol.SGVote V)} {v : V} {r : Round}
    (hfibre : ∀ x ∈ batch, x.val_index = v ∧ x.round = r)
    {u w : Protocol.SGVote V} (hu : u ∈ batch) (hw : w ∈ batch)
    (hne : u.confirmed ≠ w.confirmed) {Γ : Time}
    (huΓ : occurrenceBefore (ts u) Γ = true)
    (hwΓ : occurrenceBefore (ts w) Γ = true) :
    occurrenceBefore (Protocol.equivocation_instant ts batch) Γ = true := by
  obtain ⟨first, hfirst⟩ := batch_first_exists_on_fibre ts ⟨u, hu⟩ hfibre
  rw [Protocol.equivocation_instant, hfirst]
  have hfirstMem := (batch_first_mem_and_min ts hfirst).1
  let other := if first.confirmed = u.confirmed then w else u
  have hotherMem : other ∈ batch := by
    dsimp only [other]
    split <;> assumption
  have hotherNe : other.confirmed ≠ first.confirmed := by
    dsimp only [other]
    split
    · rename_i hfu
      intro hwf
      exact hne (hfu.symm.trans hwf.symm)
    · rename_i hfu
      exact fun h => hfu h.symm
  have hotherΓ : occurrenceBefore (ts other) Γ = true := by
    dsimp only [other]
    split <;> assumption
  let different := batch.filter (fun x => x.confirmed ≠ first.confirmed)
  have hotherDifferent : other ∈ different :=
    Finset.mem_filter.mpr ⟨hotherMem, hotherNe⟩
  have hdFibre : ∀ x ∈ different, x.val_index = v ∧ x.round = r := by
    intro x hx
    exact hfibre x (Finset.mem_of_mem_filter x hx)
  obtain ⟨second, hsecond⟩ :=
    batch_first_exists_on_fibre ts ⟨other, hotherDifferent⟩ hdFibre
  change occurrenceBefore
    (match Protocol.batch_first? ts different with
      | none => none
      | some second => ts second) Γ = true
  rw [hsecond]
  exact batch_first_stamp_before ts hsecond hotherDifferent hotherΓ

omit [Fintype V] in
/- A finite equivocation instant exposes the two projected votes that define
it, and both receipt stamps precede the same cutoff. -/
theorem witnesses_of_equivocation_before
    (ts : TimestampMap (Protocol.SGVote V))
    {batch : Finset (Protocol.SGVote V)} {Gamma : Time}
    (hbefore : occurrenceBefore
      (Protocol.equivocation_instant ts batch) Gamma = true) :
    ∃ first ∈ batch, ∃ second ∈ batch,
      first.confirmed ≠ second.confirmed ∧
      occurrenceBefore (ts first) Gamma = true ∧
      occurrenceBefore (ts second) Gamma = true := by
  unfold Protocol.equivocation_instant at hbefore
  cases hfirst : Protocol.batch_first? ts batch with
  | none =>
      have : False := by
        simp [hfirst, occurrenceBefore] at hbefore
      exact this.elim
  | some first =>
      let different := batch.filter
        (fun u => u.confirmed ≠ first.confirmed)
      have hbefore' : occurrenceBefore
          (match Protocol.batch_first? ts different with
          | none => none
          | some second => ts second) Gamma = true := by
        simpa only [hfirst, different] using hbefore
      cases hsecond : Protocol.batch_first? ts different with
      | none =>
          have : False := by
            simp [hsecond, occurrenceBefore] at hbefore'
          exact this.elim
      | some second =>
          have hsecondTime : occurrenceBefore (ts second) Gamma = true := by
            simpa only [hsecond] using hbefore'
          have hfirstMem := (batch_first_mem_and_min ts hfirst).1
          have hsecondDifferent : second ∈ different :=
            (batch_first_mem_and_min ts hsecond).1
          have hsecondData := Finset.mem_filter.mp hsecondDifferent
          have hfirstTime := batch_first_stamp_before ts hfirst
            hsecondData.1 hsecondTime
          exact ⟨first, hfirstMem, second, hsecondData.1,
            Ne.symm hsecondData.2, hfirstTime, hsecondTime⟩

omit [Fintype V] in
theorem receipt_before_of_resolution_before
    {T : Finset (Block V)} {tb : TimestampMap (Block V)}
    {ts : TimestampMap (Protocol.SGVote V)}
    {u : Protocol.SGVote V} {Γ : Time}
    (h : occurrenceBefore (Protocol.sg_resolution_time T tb ts u) Γ = true) :
    occurrenceBefore (ts u) Γ = true := by
  cases hc : u.confirmed with
  | none => simpa [Protocol.sg_resolution_time, hc] using h
  | some root =>
      cases hf : Block.find? T root with
      | none => simp [Protocol.sg_resolution_time, hc, hf, occurrenceBefore] at h
      | some H =>
          exact occurrenceBefore_of_max_left (by
            simpa [Protocol.sg_resolution_time, hc, hf] using h)

omit [Fintype V] in
/-- One timely resolved vote that covers `B` either remains the target summary's
support vote or exposes a timely equivocation at the target. -/
theorem summary_support_or_equivocation_of_vote
    (gv : Protocol.GradeView V) (r : Round) (v : V) (B : Block V) (Γ : Time)
    (hrounds : ∀ k : Round, ∀ x ∈ gv.sg_votes k, x.round = k)
    {u : Protocol.SGVote V}
    (hu : u ∈ Protocol.sg_votes_by (Protocol.round_batch gv r) v)
    (hut : occurrenceBefore
      (Protocol.sg_resolution_time gv.T gv.timestamp_block
        gv.timestamp_sg_vote u) Γ = true)
    (hucov : Protocol.head_covers gv.T B u.confirmed = true) :
    (occurrenceBefore (Protocol.summary gv r v).t_v Γ = true ∧
      Protocol.head_covers gv.T B (Protocol.summary gv r v).C_v = true) ∨
      occurrenceBefore (Protocol.summary gv r v).e_v Γ = true := by
  let batch := Protocol.sg_votes_by (Protocol.round_batch gv r) v
  let τ := Protocol.sg_resolution_time gv.T gv.timestamp_block
    gv.timestamp_sg_vote
  let headed := batch.filter (fun x =>
    x.confirmed.isSome ∧ Protocol.sg_resolved gv.T x = true)
  have huBatch : u ∈ batch := hu
  have huHeaded : u ∈ headed := by
    refine Finset.mem_filter.mpr ⟨huBatch, ?_⟩
    cases hc : u.confirmed with
    | none => simp [Protocol.head_covers, hc] at hucov
    | some root =>
        cases hf : Block.find? gv.T root with
        | none => simp [Protocol.head_covers, hc, hf] at hucov
        | some H => simp [Protocol.sg_resolved, hc, hf]
  have hbatchFibre : ∀ x ∈ batch, x.val_index = v ∧ x.round = r - 1 := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    refine ⟨hx'.2, ?_⟩
    by_cases hr : r = 0
    · subst r
      simp [batch, Protocol.round_batch, Protocol.sg_votes_by] at hx
    · exact hrounds (r - 1) x (by
        simpa [batch, Protocol.round_batch, hr, Protocol.sg_votes_by] using hx'.1)
  have hheadedFibre : ∀ x ∈ headed, x.val_index = v ∧ x.round = r - 1 := by
    intro x hx
    exact hbatchFibre x (Finset.mem_of_mem_filter x hx)
  obtain ⟨first, hfirst⟩ :=
    batch_first_exists_on_fibre τ ⟨u, huHeaded⟩ hheadedFibre
  have hfirstHeaded := (batch_first_mem_and_min τ hfirst).1
  have hfirstBatch : first ∈ batch := Finset.mem_of_mem_filter first hfirstHeaded
  have hfirstTime : occurrenceBefore (τ first) Γ = true :=
    batch_first_stamp_before τ hfirst huHeaded hut
  have hsummaryC : (Protocol.summary gv r v).C_v = first.confirmed := by
    change (Protocol.batch_first? τ headed).bind Protocol.SGVote.confirmed =
      first.confirmed
    rw [hfirst]
    rfl
  have hsummaryT : (Protocol.summary gv r v).t_v = τ first := by
    change (Protocol.batch_first? τ headed).elim none τ = τ first
    rw [hfirst]
    simp
  by_cases hcover : Protocol.head_covers gv.T B first.confirmed = true
  · exact Or.inl ⟨by rwa [hsummaryT], by rwa [hsummaryC]⟩
  · apply Or.inr
    have hheadsNe : first.confirmed ≠ u.confirmed := by
      intro heq
      rw [heq, hucov] at hcover
      exact hcover rfl
    have huReceipt : occurrenceBefore (gv.timestamp_sg_vote u) Γ = true :=
      receipt_before_of_resolution_before hut
    have hfirstReceipt : occurrenceBefore (gv.timestamp_sg_vote first) Γ = true :=
      receipt_before_of_resolution_before hfirstTime
    have heqv := equivocation_before_of_two gv.timestamp_sg_vote
      hbatchFibre hfirstBatch hu hheadsNe hfirstReceipt huReceipt
    simpa only [Proofs.Optimistic.summary_e_v_eq, batch] using heqv

omit [Fintype V] in
/-- A timely supporting summary exposes the exact resolved projected vote that
the summary selected. -/
theorem vote_of_summary_support
    (gv : Protocol.GradeView V) (r : Round) (v : V) (B : Block V) (Γ : Time)
    (ht : occurrenceBefore (Protocol.summary gv r v).t_v Γ = true)
    (_hcov : Protocol.head_covers gv.T B (Protocol.summary gv r v).C_v = true) :
    ∃ u ∈ Protocol.sg_votes_by (Protocol.round_batch gv r) v,
      (Protocol.summary gv r v).C_v = u.confirmed ∧
      (Protocol.summary gv r v).t_v =
        Protocol.sg_resolution_time gv.T gv.timestamp_block
          gv.timestamp_sg_vote u := by
  let batch := Protocol.sg_votes_by (Protocol.round_batch gv r) v
  let τ := Protocol.sg_resolution_time gv.T gv.timestamp_block
    gv.timestamp_sg_vote
  let headed := batch.filter (fun x =>
    x.confirmed.isSome ∧ Protocol.sg_resolved gv.T x = true)
  cases hfirst : Protocol.batch_first? τ headed with
  | none =>
      have : (Protocol.summary gv r v).t_v = none := by
        change (Protocol.batch_first? τ headed).elim none τ = none
        rw [hfirst]
        simp
      rw [this] at ht
      simp [occurrenceBefore] at ht
  | some u =>
      have huHeaded : u ∈ headed := by
        unfold Protocol.batch_first? at hfirst
        exact Proofs.Engine.pickUnique?_mem hfirst
      refine ⟨u, Finset.mem_of_mem_filter u huHeaded, ?_, ?_⟩
      · change (Protocol.batch_first? τ headed).bind
          Protocol.SGVote.confirmed = u.confirmed
        rw [hfirst]
        rfl
      · change (Protocol.batch_first? τ headed).elim none τ = τ u
        rw [hfirst]
        simp


/-! ## 4. Fixed-cutoff SG delivery guards -/
















/-! ## 5. Projected vote transport -/

theorem projected_rounds_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (w : V) (read : Time) :
    ∀ k : Round, ∀ u ∈
      (rho.storeBeforeTime S w read).toHealing.sg_votes k, u.round = k := by
  obtain ⟨N, hN, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch read
  have hread : rho.storeBeforeTime S w read = (rho.stateBefore S N w).st :=
    congrArg NodeState.st (congrFun hN w)
  intro k u hu
  rw [hread] at hu
  change u ∈ ((rho.stateBefore S N w).st.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  have haround := Proofs.NamedStoreBridge.sgRounds_stateBefore S rho N w k a
    (List.mem_toFinset.mp ha)
  simpa only [← hau, Protocol.sgVote] using haround

/- Public pure-to-run bridge for later concentration proofs. A projected
round-`(r-1)` vote at the reader that resolves and covers `B` either supplies
the selected summary support or makes the summary's equivocation timely. -/

/- Inverse form of the summary equivocation timestamp at a grade read. -/













/-! ## 6. The resolved support head follows the same fixed-cutoff hop -/


omit [Fintype V] in
theorem occurrenceBefore_of_max_right
    {x y : Occurrence} {Gamma : Time}
    (h : occurrenceBefore (occurrenceMax x y) Gamma = true) :
    occurrenceBefore y Gamma = true := by
  cases hx : x with
  | none => rw [hx] at h; exact absurd h (by simp [occurrenceMax, occurrenceBefore])
  | some a =>
      cases hy : y with
      | none => rw [hx, hy] at h
                exact absurd h (by simp [occurrenceMax, occurrenceBefore])
      | some b =>
          rw [hx, hy] at h
          simp only [occurrenceMax, occurrenceBefore, decide_eq_true_eq] at h ⊢
          exact lt_of_le_of_lt (le_max_right a b) h


theorem publicTime_Gamma_0 (S : Setup V) (r : Round) :
    PublicTime S (S.hc.Γ_0 S.E.Δ r) := by
  refine ⟨4 * S.hc.opening_slot r, ?_⟩
  unfold Protocol.HealConfig.Γ_0 slotStart
  push_cast
  ring



/-- A block in one read store whose insertion stamp is below a public cutoff is
either genesis or has an exact acceptance event below that cutoff.
`Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before` supplies
the acceptance time bound.
The erased `B: Block V` conclusion of the prior statement cannot survive as
`NamedRun.acceptsAt S rho i p (.block B) t`: `Object.block`/`NamedObject.block`
takes a `NamedBlock V`, never an erased one (`NamedObjects.lean:8`). This is
the same class of restatement design note already apply elsewhere in this cone
(erased endpoint → an explicit `NamedBlock` witness whose erasure is the prior
endpoint): the conclusion binds the accepted named body `D` with `D.erase = B`,
found (not guessed) via `Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime`
mirroring `find_target_of_source_find_and_mem`'s own
`exists_named_of_mem_stateBefore` step above. Consumers take the named witness
and its `.erase` equation; a call site that only used the prior bare
`Run.acceptsAt S i p (.block B) t` recovers it by rewriting along `D.erase = B`
after the fact. -/
theorem accepted_block_of_mem_stamp_before
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p : V} (hp : p ∈ rho.honest) {read Gamma : Time} {B : Block V}
    (hpub : PublicTime S Gamma)
    (hB : B ∈ (rho.storeBeforeTime S p read).T)
    (hstamp : stampedBefore
      (rho.storeBeforeTime S p read).timestamp_block Gamma B = true) :
    B = Block.genesis ∨
      ∃ (D : NamedBlock V) (i : Nat) (t : Time), D.erase = B ∧
        NamedRun.acceptsAt S rho i p (.block D) t ∧ t < Gamma := by
  obtain ⟨N, hN, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read
  have hread : rho.storeBeforeTime S p read = (rho.stateBefore S N p).st := by
    unfold Run.storeBeforeTime
    exact congrArg NodeState.st (congrFun hN p)
  rw [hread] at hB hstamp
  obtain ⟨D, hDbodies, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho N p hB
  have hprocessed : Object.processed (rho.stateBefore S N p).st (.block D) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    exact hDbodies
  rcases Protocol.acceptsAt_block_of_processed S rho p N D hprocessed with
    hgen | ⟨i, hiN, t, hacc⟩
  · exact Or.inl (by rw [← hDerase, hgen]; rfl)
  · have hstampD : stampedBefore
        (rho.stateBefore S N p).st.core.timestamp_block Gamma D.erase = true := by
      rw [hDerase]
      exact hstamp
    exact Or.inr ⟨D, i, t, hDerase, hacc,
      Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
        S adm hp hacc (Nat.succ_le_of_lt hiN) hpub hstampD⟩



/- Membership in the filtered tree at a read puts the reader's finalized block
below the member. -/
theorem finalized_preceq_of_mem_filtered_at_read
    (S : Setup V) (rho : Run V) {w : V} {read : Time} {B : Block V}
    (hactive : B ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG) :
    Block.Preceq (rho.storeBeforeTime S w read).F B := by
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq] at hactive
  exact hactive.1.1.2


theorem finalizedBelowAtDeliveries_of_finalizedPreceqAtRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {B : Block V} {H : NamedBlock V} {GammaOut read : Time}
    (houtRead : GammaOut ≤ read)
    (hFpre : Block.Preceq (rho.storeBeforeTime S w read).F B)
    (hBH : Block.Preceq B H.erase) :
    Protocol.BlockFinalizedBelowAtDeliveriesBefore
      S rho w H GammaOut := by
  let N := (rho.events.filter (fun e => decide (e.time < read))).length
  have hread : rho.storeBeforeTime S w read =
      (rho.stateBefore S N w).st :=
    congrArg NodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read) w)
  have hFread : Block.Preceq (rho.stateBefore S N w).st.F B := by
    simpa only [hread] using hFpre
  intro i hi
  have hFiGamma := stateBefore_F_preceq_stateBeforeTime_of_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
    (w := w) (d := GammaOut) hi
  have hFGread := stateBeforeTime_F_mono_of_le S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (w := w) houtRead
  exact Block.preceq_trans hFiGamma
    (Block.preceq_trans hFGread (Block.preceq_trans hFpre hBH))

/- Activity of `B` at an arbitrary guard read makes every earlier delivery of
a descendant head `H` pass the receiver's finalized-ancestor guard. -/
theorem finalizedBelowAtDeliveries_of_activeAtRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {B : Block V} {H : NamedBlock V} {GammaOut read : Time}
    (houtRead : GammaOut ≤ read)
    (hactive : B ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG)
    (hBH : Block.Preceq B H.erase) :
    Protocol.BlockFinalizedBelowAtDeliveriesBefore
      S rho w H GammaOut :=
  finalizedBelowAtDeliveries_of_finalizedPreceqAtRead S adm houtRead
    (finalized_preceq_of_mem_filtered_at_read S rho hactive) hBH

/- Action-view specialization retained for the existing delivery API. -/
theorem finalizedBelowAtDeliveries_of_active
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {r : Round} {B : Block V} {H : NamedBlock V} {GammaOut : Time}
    (houtRead : GammaOut ≤ S.a r)
    (hactive : B ∈ (gradeViewAt S rho w r).tree)
    (hBH : Block.Preceq B H.erase) :
    Protocol.BlockFinalizedBelowAtDeliveriesBefore
      S rho w H GammaOut := by
  apply finalizedBelowAtDeliveries_of_activeAtRead S adm houtRead ?_ hBH
  simpa only [gradeViewAt, healStoreAt] using hactive

/- Run-wide root collision freedom makes a source-resolved block resolve to
the same block in an arbitrary target pre-time store once target membership is
known. -/
theorem find_target_of_source_find_and_mem
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {sourceT : Finset (Block V)}
    {read : Time} {root : BlockId} {H : Block V}
    (hfind : Block.find? sourceT root = some H)
    (hHmem : H ∈ (rho.storeBeforeTime S w read).T) :
    Block.find? (rho.storeBeforeTime S w read).T root = some H := by
  obtain ⟨N, hN, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read
  have htarget : rho.storeBeforeTime S w read = (rho.stateBefore S N w).st := by
    unfold Run.storeBeforeTime
    exact congrArg NodeState.st (congrFun hN w)
  have hHroot : H.root = root := Proofs.HealingLemmas.find?_root hfind
  rw [← hHroot]
  apply Proofs.Optimistic.find?_eq_some_of_unique hHmem
  intro Y hY hrootY
  have hYmem : Y ∈ (rho.stateBefore S N w).st.core.T := by rw [← htarget]; exact hY
  have hHmem' : H ∈ (rho.stateBefore S N w).st.core.T := by rw [← htarget]; exact hHmem
  obtain ⟨DY, hDYbodies, hDYerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho N w hYmem
  obtain ⟨DH, hDHbodies, hDHerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho N w hHmem'
  have hDYrun : NamedRun.blockInRun S rho DY :=
    ⟨DY, Or.inr ⟨w, hw, N, hDYbodies⟩, Proofs.NamedAncestry.named_self DY⟩
  have hDHrun : NamedRun.blockInRun S rho DH :=
    ⟨DH, Or.inr ⟨w, hw, N, hDHbodies⟩, Proofs.NamedAncestry.named_self DH⟩
  have hDroot : DY.root = DH.root := by
    rw [← Proofs.NamedWire.erase_root DY, ← Proofs.NamedWire.erase_root DH, hDYerase, hDHerase, hrootY]
  have hDeq : DY = DH :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective DY DH hDYrun hDHrun DY DH
      (Or.inl (Proofs.NamedAncestry.named_self DY))
      (Or.inr (Proofs.NamedAncestry.named_self DH)) hDroot
  rw [← hDYerase, ← hDHerase, hDeq]



/- One source summary supporter crosses one fixed cutoff hop, over named
rows (earlier's `forward_summary_support`). Both of its blockers are now
available: `supporting_vote_resolves_at_target` above, and
`relay_projected_vote_or_equivocation` above. -/









/-! A non-empty inclusive G1 result has a non-empty strict action result. -/

/-! The active-prefix branch of the frame anchor is definitionally exact. -/
theorem nodeAnchor_eq_of_activePrefix_some
    (S : Setup V) (n : NamedNodeState V) {r : Round} {root A : Block V}
    (hframe : DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r) .g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree n) root = some A) :
    nodeAnchor S n r = A := by
  change DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 = A
  unfold DecoupledConsensusModel.Protocol.anchor
  have hframe' :
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 =
        some (some root) := by
    simpa only [DecoupledConsensusModel.Protocol.phaseResult] using hframe
  rw [hframe']
  change (DecoupledConsensusModel.Protocol.activePrefix (filteredTree n) root).getD
      (Protocol.get_fg_root n.st.core.toHealing.toFG) = A
  rw [hactive]
  rfl

#print axioms nodeAnchor_eq_of_activePrefix_some







/-! ## Receipt-only agreement between two grade readers -/



end GradeDeliveryRun
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
