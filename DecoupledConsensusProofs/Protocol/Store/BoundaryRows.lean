module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RetainedRows

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Schedule arithmetic -/

/-- Copied from the private helper of the same name in `NamedSGArrival`. -/
theorem source_deadline_le_next_early (S : Setup V) (q : Round) (hR : 3 ≤ S.hc.R) :
    S.a q + S.E.Δ ≤ early S.E S.hc (q + 1) .g2 := by
  have hRcast : (3 : Time) ≤ (S.hc.R : Time) := by exact_mod_cast hR
  have hmul : 12 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Time) := by
    have h := Int.mul_le_mul_of_nonneg_left hRcast
      (Int.mul_nonneg (show (0 : Time) ≤ 4 by norm_num) S.E.Δ_pos.le)
    calc
      12 * S.E.Δ = (4 * S.E.Δ) * 3 := by ring
      _ ≤ 4 * S.E.Δ * (S.hc.R : Time) := h
  have hrest : S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ := by
    calc
      S.E.Δ = 12 * S.E.Δ + -(11 * S.E.Δ) := by ring
      _ ≤ 4 * S.E.Δ * (S.hc.R : Time) + -(11 * S.E.Δ) := Int.add_le_add_right hmul _
      _ = _ := by ring
  have heq : early S.E S.hc (q + 1) .g2 =
      S.a q + 4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ := by
    unfold early opening Phase.earlyOffset Protocol.proposal_time Env.t Setup.a
      Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  calc
    S.a q + S.E.Δ ≤ S.a q + (4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ) :=
      Int.add_le_add_left hrest _
    _ = early S.E S.hc (q + 1) .g2 := by rw [heq]; ring

/-- Copied from the private helper of the same name in `NamedSGArrival`. -/
theorem early_le_domain (S : Setup V) (q : Round) :
    early S.E S.hc q .g2 ≤ domain S.E S.hc q .g2 := by
  change opening S.E S.hc q + (-5) * S.E.Δ ≤ opening S.E S.hc q + (-1) * S.E.Δ
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (show (-5 : Time) ≤ -1 by decide) S.E.Δ_pos.le) _

theorem opening_mono (S : Setup V) {q r : Round} (h : q ≤ r) :
    opening S.E S.hc q ≤ opening S.E S.hc r :=
  Protocol.proposal_time_mono S.E (Nat.mul_le_mul_right _ h)

theorem early_le_opening (S : Setup V) (q : Round) :
    early S.E S.hc q .g2 ≤ opening S.E S.hc q := by
  change opening S.E S.hc q + (-5) * S.E.Δ ≤ opening S.E S.hc q
  have : (-5) * S.E.Δ ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg (by decide) S.E.Δ_pos.le
  simpa only [add_zero] using Int.add_le_add_left this (opening S.E S.hc q)

theorem domain_le_opening (S : Setup V) (q : Round) :
    domain S.E S.hc q .g2 ≤ opening S.E S.hc q := by
  change opening S.E S.hc q + (-1) * S.E.Δ ≤ opening S.E S.hc q
  have : (-1) * S.E.Δ ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg (by decide) S.E.Δ_pos.le
  simpa only [add_zero] using Int.add_le_add_left this (opening S.E S.hc q)

/-- An action time one delay before a strictly later round's G2 early cutoff. -/
theorem action_delta_le_early (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R) (hqr : q < r) :
    S.a q + S.E.Δ ≤ early S.E S.hc r .g2 := by
  refine (source_deadline_le_next_early S q hR).trans ?_
  change opening S.E S.hc (q + 1) + (-5) * S.E.Δ ≤ opening S.E S.hc r + (-5) * S.E.Δ
  exact Int.add_le_add_right (opening_mono S hqr) _

theorem action_le_domain (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R) (hqr : q < r) :
    S.a q ≤ domain S.E S.hc r .g2 := by
  refine le_trans ?_ ((action_delta_le_early S hR hqr).trans (early_le_domain S r))
  simpa only [add_zero] using Int.add_le_add_left S.E.Δ_pos.le (S.a q)

/-! ## The retained inventory -/

theorem mem_retainedRounds (S : Setup V) {sr k : Round}
    (hlo : sr - S.hc.η_SG ≤ k) (hhi : k ≤ sr) :
    k ∈ Internal.OutageEntryRevision.retainedRounds S sr := by
  simp only [Internal.OutageEntryRevision.retainedRounds, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hhi, hlo⟩

theorem retainedRounds_bounds (S : Setup V) {sr k : Round}
    (h : k ∈ Internal.OutageEntryRevision.retainedRounds S sr) :
    sr - S.hc.η_SG ≤ k ∧ k ≤ sr := by
  simp only [Internal.OutageEntryRevision.retainedRounds, Finset.mem_filter, Finset.mem_range] at h
  exact ⟨h.2, Nat.le_of_lt_succ h.1⟩

omit [DecidableEq V] [Fintype V] in
private theorem occurrenceBefore_mono {x : Occurrence} {c d : Time}
    (h : occurrenceBefore x c = true) (hcd : c ≤ d) : occurrenceBefore x d = true := by
  cases x with
  | none => exact absurd h (by simp [occurrenceBefore])
  | some w =>
    simp only [occurrenceBefore, decide_eq_true_eq] at h ⊢
    exact lt_of_lt_of_le h (WithBot.coe_le_coe.mpr hcd)

/-- An honest round-`q` voter's row is in every honest reader's bucketed pool
at any read past round `q + 1`'s G2 domain, with a projection stamp before any
cutoff at or after round `q + 1`'s G2 early cutoff. This is `HealthySGArrival`
carried forward by `strict_sg_row_carry`. -/
theorem vote_row_at_cut (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {b0 : Time} (harr : HealthySGArrival S rho b0)
    (hR : 3 ≤ S.hc.R) (q : Round) (u : V) (hu : u ∈ honestRoundVoters S rho q)
    (hopen : opening S.E S.hc (q + 1) ≤ b0)
    (cut cutoff : Time) (hcut : domain S.E S.hc (q + 1) .g2 ≤ cut)
    (hcutoff : early S.E S.hc (q + 1) .g2 ≤ cutoff)
    (reader : V) (hreader : reader ∈ rho.honest) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = q ∧
      NamedRun.emits S rho u (.attest a) (S.a a.round) ∧
      S.a a.round + S.E.Δ ≤ b0 ∧
      Protocol.sgVote a.erase ∈
        (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView.sg_votes a.round ∧
      occurrenceBefore ((NamedRun.stateBeforeTime S rho cut reader).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) cutoff = true := by
  obtain ⟨huh, a, hval, haround, hem⟩ :=
    (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u q).mp hu
  subst haround
  subst hval
  have hdeadline : S.a a.round + S.E.Δ ≤ b0 :=
    ((source_deadline_le_next_early S a.round hR).trans (early_le_opening S (a.round + 1))).trans
      hopen
  obtain ⟨hrow, hstamp⟩ := harr a huh hem hdeadline reader hreader
  obtain ⟨hrowcut, hstampeq⟩ := strict_sg_row_carry S rho sch reader hcut hrow
  have hstampcut : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho cut reader).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) cutoff = true := by
    rw [hstampeq]
    exact occurrenceBefore_mono hstamp hcutoff
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho cut reader).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1
  have hpool := NamedAdmission.pool_view_mem
    (NamedRun.stateBeforeTime S rho cut reader).st hcoh.2.2.2.1 a hrowcut
  exact ⟨a, rfl, rfl, hem, hdeadline,
    Finset.mem_image_of_mem Protocol.sgVote hpool, hstampcut⟩

/-- The inventory instance: the row lands in `retainedRaw` at any inventory time
`tau ≤ b0` that round `q + 1`'s opening has already passed. Healthy delivery
holds up to `tau` a fortiori, so the `b0`-stated `HealthySGArrival` still
applies; only the read and the retention stamp move to `tau`. -/
theorem retained_mem_of_vote_at (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {b0 : Time} (harr : HealthySGArrival S rho b0)
    (hR : 3 ≤ S.hc.R) (sr q : Round) (u : V) (hu : u ∈ honestRoundVoters S rho q)
    (hq : q ∈ Internal.OutageEntryRevision.retainedRounds S sr)
    (tau : Time) (htau : tau ≤ b0) (hopen : opening S.E S.hc (q + 1) ≤ tau)
    (reader : V) (hreader : reader ∈ rho.honest) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = q ∧
      NamedRun.emits S rho u (.attest a) (S.a a.round) ∧
      S.a a.round + S.E.Δ ≤ tau ∧
      Protocol.sgVote a.erase ∈ Internal.OutageEntryRevision.retainedRaw S
        (NamedRun.stateBeforeTime S rho tau reader).st.core sr tau u := by
  have hdeadtau : S.a q + S.E.Δ ≤ tau :=
    ((source_deadline_le_next_early S q hR).trans (early_le_opening S (q + 1))).trans hopen
  obtain ⟨a, hval, haround, hem, _, hsg, hstamp⟩ :=
    vote_row_at_cut S rho sch harr hR q u hu (hopen.trans htau) tau tau
      ((domain_le_opening S (q + 1)).trans hopen)
      (((early_le_domain S (q + 1)).trans (domain_le_opening S (q + 1))).trans hopen)
      reader hreader
  refine ⟨a, hval, haround, hem, by rw [haround]; exact hdeadtau, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨a.round, haround ▸ hq, hsg⟩, hval ▸ rfl, hstamp⟩

/-- The boundary instance: the row lands in `retainedRaw` at `b0`. -/
theorem retained_mem_of_vote (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {b0 : Time} (harr : HealthySGArrival S rho b0)
    (hR : 3 ≤ S.hc.R) (sr q : Round) (u : V) (hu : u ∈ honestRoundVoters S rho q)
    (hq : q ∈ Internal.OutageEntryRevision.retainedRounds S sr)
    (hopen : opening S.E S.hc (q + 1) ≤ b0)
    (reader : V) (hreader : reader ∈ rho.honest) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = q ∧
      NamedRun.emits S rho u (.attest a) (S.a a.round) ∧
      S.a a.round + S.E.Δ ≤ b0 ∧
      Protocol.sgVote a.erase ∈ Internal.OutageEntryRevision.retainedRaw S
        (NamedRun.stateBeforeTime S rho b0 reader).st.core sr b0 u :=
  retained_mem_of_vote_at S rho sch harr hR sr q u hu hq b0 le_rfl hopen reader hreader

/-- The phase instance: the row lands in `rawInputs` at a later round's G2 read. -/
theorem rawInputs_mem_of_vote (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {b0 : Time} (harr : HealthySGArrival S rho b0)
    (hR : 3 ≤ S.hc.R) (q r : Round) (u : V) (hu : u ∈ honestRoundVoters S rho q)
    (hwin : q ∈ Protocol.latest_window S.hc.η_SG r) (hqr : q < r)
    (hopen : opening S.E S.hc (q + 1) ≤ b0)
    (reader : V) (hreader : reader ∈ rho.honest) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = q ∧
      NamedRun.emits S rho u (.attest a) (S.a a.round) ∧
      S.a a.round + S.E.Δ ≤ b0 ∧
      Protocol.sgVote a.erase ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) reader).st.core.toHealing.gradeView
        S.hc.η_SG r (early S.E S.hc r .g2) u := by
  have hdom : domain S.E S.hc (q + 1) .g2 ≤ domain S.E S.hc r .g2 := by
    change opening S.E S.hc (q + 1) + (-1) * S.E.Δ ≤ opening S.E S.hc r + (-1) * S.E.Δ
    exact Int.add_le_add_right (opening_mono S hqr) _
  have hearly : early S.E S.hc (q + 1) .g2 ≤ early S.E S.hc r .g2 := by
    change opening S.E S.hc (q + 1) + (-5) * S.E.Δ ≤ opening S.E S.hc r + (-5) * S.E.Δ
    exact Int.add_le_add_right (opening_mono S hqr) _
  obtain ⟨a, hval, haround, hem, hdeadline, hsg, hstamp⟩ :=
    vote_row_at_cut S rho sch harr hR q u hu hopen _ _ hdom hearly reader hreader
  refine ⟨a, hval, haround, hem, hdeadline, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨a.round, List.mem_toFinset.mpr (haround ▸ hwin), hsg⟩,
      hval ▸ rfl, hstamp⟩

/-- Traceback from a raw phase input of an honest sender, the `rawInputs` twin
of `retained_trace`. -/
theorem rawInputs_trace (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (cut cutoff : Time) (reader : V) (eta r : Round) (u : V) (hu : u ∈ rho.honest)
    {y : Protocol.SGVote V}
    (hy : y ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView eta r cutoff u) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = y.round ∧
      Protocol.sgVote a.erase = y ∧ y.round ∈ Protocol.latest_window eta r ∧
      S.a a.round < cut ∧ NamedRun.emits S rho u (.attest a) (S.a a.round) := by
  obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hy
  obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.mp hpool
  obtain ⟨a, hround, hproj, hmem⟩ := pool_token_row S rho sch cut reader hyk
  have hyround : y.round = a.round := by rw [← hproj]; rfl
  have hval : a.val_index = u := by
    have hvy : y.val_index = u := hfields.1
    rw [← hproj] at hvy
    exact hvy
  subst hval
  obtain ⟨hlt, hem⟩ := honest_held_row_before_cut S rho sch auth cut reader hmem hu
  exact ⟨a, rfl, hyround.symm, hproj,
    by rw [hyround, hround]; exact List.mem_toFinset.mp hk, hlt, hem⟩

/-! ## `staleAt` at the boundary -/

/-- If every maximal retained raw row of an honest sender comes from a round at
or above the stable round, that sender is not a stale risk at this reader.
Coverage is `retained_covers`; the equivocation clause is honest
non-equivocation in a single round. -/
theorem staleAt_false_of_rounds_ge_at (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (b0 tau : Time) (htau : tau ≤ b0)
    (hgrid : OnDeltaGrid S tau)
    (s : Round) (P : Block V)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s P) (hhead : HonestHeadHeldAbove S rho b0 s P)
    (reader : V) (hreader : reader ∈ rho.honest) (u : V) (hu : u ∈ rho.honest)
    (hFP : Block.Preceq (NamedRun.stateBeforeTime S rho tau reader).st.core.F P) (sr : Round)
    (hge : ∀ x ∈ Internal.OutageEntryRevision.latest (Internal.OutageEntryRevision.retainedRaw S
        (NamedRun.stateBeforeTime S rho tau reader).st.core sr tau u), s ≤ x.round) :
    Internal.OutageEntryRevision.staleAt S (NamedRun.stateBeforeTime S rho tau reader).st.core
      sr tau P u = false := by
  simp only [Internal.OutageEntryRevision.staleAt, decide_eq_false_iff_not, not_or, not_exists]
  constructor
  · intro x
    simp only [not_and]
    intro hx
    rw [retained_covers_at S rho sch auth roots b0 tau htau hgrid s P hconf hhead reader hreader
      u hu hFP sr (latest_mem hx).1 (hge x hx)]
    exact Bool.noConfusion
  · intro x
    simp only [not_and, not_exists]
    intro hx y
    simp only [not_not]
    intro hy
    obtain ⟨a, hva, hra, hpa, _, hla, hema⟩ :=
      retained_trace S rho sch auth tau reader sr u hu (latest_mem hx).1
    obtain ⟨b, hvb, hrb, hpb, _, hlb, hemb⟩ :=
      retained_trace S rho sch auth tau reader sr u hu (latest_mem hy).1
    have hround : a.round = b.round := by
      rw [hra, hrb]; exact latest_round_eq hx hy
    have hab : a = b :=
      NamedOutageProvenance.emitted_same_round_unique S rho sch hema hemb hround
    rw [← hpa, ← hpb, hab]

theorem staleAt_false_of_rounds_ge (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (b0 : Time) (hgrid : OnDeltaGrid S b0)
    (s : Round) (P : Block V)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s P) (hhead : HonestHeadHeldAbove S rho b0 s P)
    (reader : V) (hreader : reader ∈ rho.honest) (u : V) (hu : u ∈ rho.honest)
    (hFP : Block.Preceq (NamedRun.stateBeforeTime S rho b0 reader).st.core.F P) (sr : Round)
    (hge : ∀ x ∈ Internal.OutageEntryRevision.latest (Internal.OutageEntryRevision.retainedRaw S
        (NamedRun.stateBeforeTime S rho b0 reader).st.core sr b0 u), s ≤ x.round) :
    Internal.OutageEntryRevision.staleAt S (NamedRun.stateBeforeTime S rho b0 reader).st.core
      sr b0 P u = false :=
  staleAt_false_of_rounds_ge_at S rho sch auth roots b0 b0 le_rfl hgrid s P hconf hhead reader
    hreader u hu hFP sr hge

/-- The contrapositive form used by the stale inclusion, at a general inventory
time `tau ≤ b0`. -/
theorem exists_low_round_of_staleAt_at (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (b0 tau : Time) (htau : tau ≤ b0)
    (hgrid : OnDeltaGrid S tau)
    (s : Round) (P : Block V)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s P) (hhead : HonestHeadHeldAbove S rho b0 s P)
    (reader : V) (hreader : reader ∈ rho.honest) (u : V) (hu : u ∈ rho.honest)
    (hFP : Block.Preceq (NamedRun.stateBeforeTime S rho tau reader).st.core.F P) (sr : Round)
    (hstale : Internal.OutageEntryRevision.staleAt S
      (NamedRun.stateBeforeTime S rho tau reader).st.core sr tau P u = true) :
    ∃ x ∈ Internal.OutageEntryRevision.latest (Internal.OutageEntryRevision.retainedRaw S
      (NamedRun.stateBeforeTime S rho tau reader).st.core sr tau u), x.round < s := by
  by_contra hcon
  push_neg at hcon
  have := staleAt_false_of_rounds_ge_at S rho sch auth roots b0 tau htau hgrid s P hconf hhead
    reader hreader u hu hFP sr hcon
  rw [this] at hstale
  exact Bool.noConfusion hstale


#print axioms action_delta_le_early
#print axioms retained_mem_of_vote
#print axioms staleAt_false_of_rounds_ge



end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
