module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusStatements
public import DecoupledConsensusInternal.Legacy.Claims
public import DecoupledConsensusInternal.Legacy.Instance
public import DecoupledConsensusProofs.Generic.W4FinalityClosed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.W4StableRecordGrowthFrom
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts
public import DecoupledConsensusProofs.Objects.AdmissibleCore
public import DecoupledConsensusProofs.Bridge.RoundTimes

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Bridge from the historical proof vocabulary to the standard bundle

The bridge keeps the existing proofs as the source of every public field. The
lemmas in this file only unfold the interface and weaken or reorder the prior
contracts where the records permits it.
-/



namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

abbrev legacyInterface (S : Setup V) : Interface V := Statements.«instance» S
noncomputable abbrev legacyConstants (S : Setup V) : Constants := Statements.ourConstants S

/- This local adapter maps the compatibility
   `ProposerOpeningCarrierRecurrence` predicate to the current generic
   `legacyStrongMultiProposerRecurrence` name. -/
abbrev legacyStrongMultiProposerRecurrence (S : Setup V) (rho : Run V) (gap : Nat) : Prop :=
  ProposerOpeningCarrierRecurrence S rho gap

private theorem oldSlashableBound_of_standard
    (S : Setup V) {rho : Run V} (h : Statements.SlashableBound (legacyInterface S) rho) :
    Execution.SlashableBound S rho := by
  intro B₁ B₂ hB₁ hB₂
  exact h B₁ B₂ hB₁ hB₂

theorem unconditional_finalizedBelowStable (S : Setup V) :
    ∀ rho, Prefix S rho (legacyInterface S).finalized (legacyInterface S).stable := by
  intro rho v t
  have h := (legacy_consensus_closed S).nestedOutputs rho v t
  exact h.1

theorem unconditional_stableBelowConfirmed (S : Setup V) :
    ∀ rho, Prefix S rho (legacyInterface S).stable (legacyInterface S).confirmed := by
  intro rho v t
  have h := (legacy_consensus_closed S).nestedOutputs rho v t
  exact h.2

theorem unconditional_pureFinality (S : Setup V) :
    ∀ c c' T T', (legacyInterface S).collisionFree c c' → (legacyInterface S).finalizes c T →
      (legacyInterface S).finalizes c' T' →
      Block.compatible T T' = true ∨ (legacyInterface S).evidence c c' := by
  intro c c' T T' hinj hc hc'
  rcases hc with ⟨h₁, hc⟩
  rcases hc' with ⟨h₂, hc'⟩
  rcases (legacy_consensus_closed S).finality.accountable c c' T T' h₁ h₂ hinj hc hc' with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem unconditional_finalizedAccountable (S : Setup V) :
    ∀ rho, RunWellFormed S rho →
      AccountablyConsistentFrom S (legacyInterface S) rho (legacyInterface S).finalized (legacyInterface S).finalized 0 := by
  intro rho hwell u hu v hv t t' ht hth ht' hth'
  rcases (legacy_consensus_closed S).finality.runAccountable rho hwell with h
  rcases h.reads u hu v hv t t' with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem unconditional_voteSafetyOfClients (S : Setup V) :
    ValidatorVoteSafety S :=
  (legacy_consensus_closed S).voteSafetyOfClients

theorem accountable_finalizedAgree (S : Setup V) :
    ∀ rho, RunWellFormed S rho → Statements.SlashableBound (legacyInterface S) rho →
      AgreeFrom S rho (legacyInterface S).finalized 0 := by
  intro rho hwell hsb u hu v hv t t' ht hth ht' hth'
  have hold := oldSlashableBound_of_standard S hsb
  have h := (legacy_consensus_closed S).finality.runAgreement rho hwell hold
  exact h.2 u hu v hv t t'

theorem accountable_leakFairness (S : Setup V) :
    LeakFairness.LeakFairnessL1CurrentProduction S :=
  (legacy_consensus_closed S).leakFairness

private theorem committees_bridge (S : Setup V) {H : Finset V} :
    Statements.HonestCommittees (legacyInterface S) H → Execution.HonestCommittees S H := by
  intro h s
  exact h s

private theorem confirmed_agree_bridge (S : Setup V) {rho : Run V} {t₀ : Time}
    (h : ConfirmedOutputCompatibleFrom S rho t₀) :
    AgreeFrom S rho (legacyInterface S).confirmed t₀ := by
  intro u hu v hv t t' ht ht' hth hth'
  change Block.compatible (confirmedOutputAt S rho u t)
      (confirmedOutputAt S rho v t') = true
  exact h u hu v hv t t' ht hth ht' hth'

private theorem confirmed_monotone_bridge (S : Setup V) {rho : Run V} {t₀ : Time}
    (h : ConfirmedOutputMonotoneFrom S rho t₀) :
    MonotoneFrom S rho (legacyInterface S).confirmed t₀ := by
  intro v hv t t' ht htt hth'
  change Block.Preceq (confirmedOutputAt S rho v t)
      (confirmedOutputAt S rho v t')
  exact h v hv t t' ht htt hth'

private theorem sleepy_genesis_to_weakGenesis (S : Setup V) {rho : Run V}
    (h : SleepyRegime S (legacyInterface S) (legacyConstants S) rho 0) : WeakGenesis S rho := by
  refine ⟨h.execution, h.synchrony, committees_bridge S h.committees,
    le_antisymm h.gst S.E.t_GST_nonneg, ?_⟩
  intro r hr hhor
  exact h.windows r hr (Proofs.HealingLemmas.a_nonneg S r) hhor

private theorem healingBoundary_le_next_action (S : Setup V) (q : Round) :
    healingBoundaryTime S q ≤ S.a (q + 1) := by
  unfold healingBoundaryTime Setup.a Protocol.HealConfig.a
    Protocol.HealConfig.opening_slot Protocol.vote_time Env.t slotStart
  push_cast
  have hR : (3 : Int) ≤ S.hc.R := by exact_mod_cast S.hc.R_ge_three
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  nlinarith

private theorem finality_boundary_identity (S : Setup V) (r k : Round) :
    healingBoundaryTime S (r + k) =
      S.a r + 4 * S.E.Δ * (S.hc.R * k : Nat) + 3 * S.E.Δ := by
  simp only [healingBoundaryTime, Protocol.vote_time, Env.t, slotStart,
    Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot]
  push_cast
  ring

private theorem finality_startup_identity (S : Setup V) (k : Round) :
    healingBoundaryTime S (k + 1) - S.a 0 =
      4 * S.E.Δ * (S.hc.R * (k + 1) : Nat) + 3 * S.E.Δ := by
  simp only [healingBoundaryTime, Protocol.vote_time, Env.t, slotStart,
    Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot]
  push_cast
  ring

private theorem finality_startup_nonneg (S : Setup V) (k : Round) :
    0 ≤ healingBoundaryTime S (k + 1) - S.a 0 := by
  rw [finality_startup_identity]
  have hΔ : (0 : Int) ≤ S.E.Δ := S.E.Δ_pos.le
  have hR : (0 : Int) ≤ S.hc.R := by exact_mod_cast (Nat.zero_le S.hc.R)
  positivity

private theorem finality_startup_time_bound (S : Setup V) {t₀ : Time}
    (hgst : S.E.t_GST ≤ t₀) {k : Round} :
    healingBoundaryTime S (roundAt S t₀ + k) ≤
      t₀ + (healingBoundaryTime S (k + 1) - S.a 0) := by
  have ht₀ : (0 : Time) ≤ t₀ := S.E.t_GST_nonneg.trans hgst
  let r := roundAt S t₀
  by_cases hr : r = 0
  · subst r
    rw [hr]
    rw [finality_boundary_identity, finality_startup_identity]
    unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
    push_cast
    have hR : (3 : Int) ≤ S.hc.R := by exact_mod_cast S.hc.R_ge_three
    have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
    nlinarith
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hprev : S.a (r - 1) < t₀ := by
      apply lt_of_not_ge
      exact roundAt_min S t₀ (Nat.sub_lt (Nat.zero_lt_of_lt hrpos) (by decide))
    have hidentity : healingBoundaryTime S (r + k) =
        S.a (r - 1) + (healingBoundaryTime S (k + 1) - S.a 0) := by
      rw [finality_boundary_identity, finality_startup_identity]
      rw [← add_assoc]
      rw [← Proofs.HealingLemmas.a_add_rounds S (r - 1) (k + 1)]
      have hrsub : r - 1 + 1 = r :=
        Nat.sub_add_cancel (Nat.succ_le_iff.mpr hrpos)
      rw [show r - 1 + (k + 1) = (r - 1 + 1) + k by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm], hrsub]
      rw [Proofs.HealingLemmas.a_add_rounds]
    rw [hidentity]
    exact add_le_add hprev.le le_rfl

private theorem finality_slot_before_next_opening (S : Setup V) (s : Slot) :
    s < S.hc.opening_slot (S.hc.round_of s + 1) := by
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hmod : s % S.hc.R < S.hc.R := Nat.mod_lt s hRpos
  unfold Protocol.HealConfig.round_of Protocol.HealConfig.opening_slot
  calc
    s = s % S.hc.R + S.hc.R * (s / S.hc.R) :=
      (Nat.mod_add_div s S.hc.R).symm
    _ < S.hc.R + S.hc.R * (s / S.hc.R) :=
      Nat.add_lt_add_right hmod _
    _ = (s / S.hc.R + 1) * S.hc.R := by ring

private theorem finality_deadline_time_bound (S : Setup V) (s : Slot) (k : Round) :
    S.a (S.hc.round_of s + 1 + k) ≤
      Protocol.proposal_time S.E s +
        (healingBoundaryTime S (k + 1) - S.a 0) + 3 * S.E.Δ := by
  have hlow : S.hc.round_of s * S.hc.R ≤ s := by
    have hlow0 : S.hc.R * (s / S.hc.R) ≤ s := by
      calc
        S.hc.R * (s / S.hc.R) ≤ s % S.hc.R + S.hc.R * (s / S.hc.R) :=
          Nat.le_add_left _ _
        _ = s := Nat.mod_add_div s S.hc.R
    simpa [Protocol.HealConfig.round_of, Nat.mul_comm] using hlow0
  have hlow' : ((S.hc.round_of s * S.hc.R : Nat) : Time) ≤ (s : Time) := by
    exact_mod_cast hlow
  simp only [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
    Protocol.proposal_time, Env.t, slotStart, healingBoundaryTime,
    Protocol.vote_time]
  push_cast at hlow' ⊢
  ring_nf at hlow' ⊢
  have hR : (3 : Int) ≤ S.hc.R := by exact_mod_cast S.hc.R_ge_three
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hscaled := Int.mul_le_mul_of_nonneg_left hlow'
    (show (0 : Int) ≤ 4 * S.E.Δ by nlinarith)
  ring_nf at hscaled
  nlinarith

theorem finalized_included (S : Setup V) :
    ∀ rho t₀ gap extra, FinalityRegime S (legacyInterface S) rho t₀ gap extra →
      t₀ + (legacyConstants S).finalityStartup gap extra ≤ rho.horizon →
      Included S (legacyInterface S) rho (legacyInterface S).finalized
        (t₀ + (legacyConstants S).finalityStartup gap extra) ((legacyConstants S).finalityDeadline gap extra) := by
  intro rho t₀ gap extra hregime hhorizon
  let rGST := roundAt S t₀
  have hpost : S.E.t_GST ≤ S.a rGST :=
    hregime.gst.trans (roundAt_spec S t₀)
  have hstartupHorizon :
      healingBoundaryTime S (rGST + finalityStartup S gap extra) ≤ rho.horizon := by
    have hbound := finality_startup_time_bound S hregime.gst
      (k := finalityStartup S gap extra)
    apply hbound.trans
    simpa [legacyConstants, ourConstants] using hhorizon
  have hstrong : StrongFinalityRun S rho gap :=
    ⟨hregime.execution, hregime.synchrony, hregime.allAwake,
      committees_bridge S hregime.committees, hregime.belowThird,
      hregime.recurrence, hregime.gapBound⟩
  obtain ⟨q, hqlo, hqhi, hproposal⟩ :=
    (legacy_consensus_closed S).liveness.honestProposalFinalization.afterGST
      extra hregime.timeout gap rho rGST hstrong hpost hstartupHorizon
  have ht₀ : (0 : Time) ≤ t₀ := S.E.t_GST_nonneg.trans hregime.gst
  have hstartupNonneg : 0 ≤ (legacyConstants S).finalityStartup gap extra := by
    simpa [legacyConstants, ourConstants] using
      (finality_startup_nonneg S (finalityStartup S gap extra))
  intro s hs hhon hdeadline
  have hproposalPos : 0 < (legacyInterface S).proposalTime s :=
    (add_nonneg ht₀ hstartupNonneg).trans_lt hs
  have hspos : 0 < s := by
    cases s with
    | zero => simp [legacyInterface, Statements.«instance», Protocol.proposal_time,
        Env.t, slotStart] at hproposalPos
    | succ k => exact Nat.zero_lt_succ _
  have hqBoundary : healingBoundaryTime S q ≤
      healingBoundaryTime S (rGST + finalityStartup S gap extra) :=
    by
      unfold healingBoundaryTime
      exact Protocol.vote_time_mono_slots S.E
        (Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R hqhi) 2)
  have hqStart : healingBoundaryTime S q < (legacyInterface S).proposalTime s := by
    have hbound := finality_startup_time_bound S hregime.gst
      (k := finalityStartup S gap extra)
    have hle : healingBoundaryTime S q ≤
        t₀ + (healingBoundaryTime S (finalityStartup S gap extra + 1) - S.a 0) :=
      hqBoundary.trans (hbound)
    exact hle.trans_lt (by simpa [legacyConstants, ourConstants] using hs)
  obtain ⟨B, hB, hfinality⟩ := hproposal s hspos hqStart hhon
  dsimp at hfinality
  have hdueTime : S.a (S.hc.round_of s + 1 + finalityDeadline S gap extra) ≤
      (legacyInterface S).proposalTime s + (legacyConstants S).finalityDeadline gap extra := by
    have h := finality_deadline_time_bound S s (finalityDeadline S gap extra)
    simpa [legacyConstants, ourConstants, add_assoc] using h
  have hdueHorizon : S.a (S.hc.round_of s + 1 + finalityDeadline S gap extra) ≤
      rho.horizon := by
    exact hdueTime.trans hdeadline
  obtain ⟨t, _htlo, hthi, hF⟩ := hfinality hdueHorizon
  refine ⟨B, ?_, ?_⟩
  · exact ⟨hhon, hB⟩
  · intro v hv
    have htv : t ≤ (legacyInterface S).proposalTime s + (legacyConstants S).finalityDeadline gap extra :=
      hthi.trans hdueTime
    have hmono := StoreFinality.stateAt_F_mono S
      hregime.execution.toNamedScheduleWellFormed v htv
    exact Block.preceq_trans (hF v hv) hmono

private theorem recovery_to_strong (S : Setup V) {source : Run V} {t₀ : Time}
    {gap extra : Nat} (h : RecoveryRegime S (legacyInterface S) (legacyConstants S) source t₀ gap extra) :
    ∃ rGST n : Round, StrongRecoveryPrefix S source rGST gap extra n ∧
      n + gap = recoveryRound S t₀ gap extra := by
  let rGST : Round := roundAt S t₀
  let n : Round := recoveryRound S t₀ gap extra - gap
  have hgap : gap ≤ recoveryRound S t₀ gap extra := by
    unfold recoveryRound
    exact Nat.le_add_left gap _
  have hsum : n + gap = recoveryRound S t₀ gap extra := by
    exact Nat.sub_add_cancel hgap
  have hstart : BoundedPhaseStart S source rGST gap extra n := by
    simp only [BoundedPhaseStart]
    dsimp [rGST, n, boundedPhaseStartLag]
    apply (Nat.sub_eq_iff_eq_add hgap).2
    rfl
  have hpost : S.E.t_GST ≤ S.a rGST :=
    h.gst.trans (roundAt_spec S t₀)
  have hhor : source.horizon = S.a (n + gap) := by
    simpa [legacyConstants, ourConstants, recoveryRound, boundedPhaseStartLag, hsum] using h.horizon
  refine ⟨rGST, n,
    ⟨h.execution, h.synchrony, h.allAwake, committees_bridge S h.committees,
      h.belowThird, h.recurrence, h.timeout, hpost, hstart, hhor⟩,
    hsum⟩

theorem strongRecovery_of_recovery (S : Setup V) {source : Run V} {t₀ : Time}
    {gap extra : Nat}
    (h : Statements.RecoveryRegime S (Statements.«instance» S)
      (Statements.ourConstants S) source t₀ gap extra) :
    ∃ rGST n : Round, StrongRecoveryPrefix S source rGST gap extra n ∧
      n + gap = Statements.Instantiation.recoveryRound S t₀ gap extra :=
  recovery_to_strong S h

private theorem sleepy_continuation_to_weakContinuation (S : Setup V)
    {source rho : Run V} {t₀ : Time} {gap extra : Nat}
    {rGST n : Round}
    (hrec : RecoveryRegime S (legacyInterface S) (legacyConstants S) source t₀ gap extra)
    (hstrong : StrongRecoveryPrefix S source rGST gap extra n)
    (hsum : n + gap = recoveryRound S t₀ gap extra)
    (hcont : Continues source rho ((legacyConstants S).prefixEnd t₀ gap extra)
      ((legacyConstants S).recoveryEnd t₀ gap extra))
    (hsleep : SleepyRegime S (legacyInterface S) (legacyConstants S) rho ((legacyConstants S).recoveryEnd t₀ gap extra))
    (hslash : Statements.SlashableBound (legacyInterface S) rho) :
    WeakContinuation S source rho (n + gap) := by
  have hprefix : (legacyConstants S).prefixEnd t₀ gap extra = S.a (n + gap) := by
    simpa [legacyConstants, ourConstants, recoveryRound, boundedPhaseStartLag, hsum]
  have hrecover : (legacyConstants S).recoveryEnd t₀ gap extra = healingBoundaryTime S (n + gap) := by
    simpa [legacyConstants, ourConstants, recoveryRound, hsum]
  have hslash' := oldSlashableBound_of_standard S hslash
  refine ⟨hsleep.execution, hsleep.synchrony,
    committees_bridge S hsleep.committees, hslash',
    (by simpa [hprefix] using hcont.agrees),
    (by simpa [hrecover] using hcont.covered), ?_⟩
  intro r hr hhor
  have hrnext : n + gap + 1 ≤ r := Nat.succ_le_iff.mpr hr
  have hboundary : (legacyConstants S).recoveryEnd t₀ gap extra ≤ S.a (n + gap + 1) := by
    rw [hrecover]
    exact healingBoundary_le_next_action S (n + gap)
  have htime : (legacyConstants S).recoveryEnd t₀ gap extra ≤ S.a r :=
    hboundary.trans (Assembly.a_mono S hrnext)
  have hrpos : 0 < r := Nat.zero_lt_of_lt hr
  exact hsleep.windows r hrpos (by simpa [htime] using htime) hhor

private theorem action_le_healingBoundary (S : Setup V) {m q : Round} (hmq : m ≤ q) :
    S.a m ≤ healingBoundaryTime S q := by
  exact (Assembly.a_mono S hmq).trans (a_le_healingBoundaryTime S q)

private theorem healingBoundary_mono (S : Setup V) {m q : Round} (hmq : m ≤ q) :
    healingBoundaryTime S m ≤ healingBoundaryTime S q := by
  unfold healingBoundaryTime
  exact Protocol.vote_time_mono_slots S.E
    (Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R hmq) 2)

private theorem finalized_compatible_of_confirmed_compatible (S : Setup V)
    {rho : Run V} {t₀ : Time}
    (hcompat : ConfirmedOutputCompatibleFrom S rho t₀) :
    ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      t₀ ≤ t → t₀ ≤ t' → t ≤ rho.horizon → t' ≤ rho.horizon →
      Block.compatible (rho.storeAt S u t).F
        (rho.storeAt S v t').F = true := by
  intro u hu v hv t t' ht ht' hhor hhor'
  have hprefixU := (legacy_consensus_closed S).finalizedPrefix rho u t
  have hprefixV := (legacy_consensus_closed S).finalizedPrefix rho v t'
  have hcc := hcompat u hu v hv t t' ht ht' hhor hhor'
  have hUF := Protocol.compatible_of_preceq_of_compatible hprefixU hcc
  have hVF := Protocol.compatible_of_preceq_of_compatible hprefixV
    (Protocol.compatible_comm hUF)
  exact Protocol.compatible_comm hVF

private theorem stableOutput_eq_latest (S : Setup V) (rho : Run V) (v : V) (t : Time)
    (h : Block.Preceq (rho.storeAt S v t).F
      (rho.storeAt S v t).latest_stable) :
    stableOutputAt S rho v t = (rho.storeAt S v t).latest_stable := by
  change Block.preceq (rho.storeAt S v t).F
      (rho.storeAt S v t).latest_stable = true at h
  unfold stableOutputAt Protocol.get_stable
  rw [if_pos h]

private theorem stableOutput_eq_finalized (S : Setup V) (rho : Run V) (v : V) (t : Time)
    (h : ¬ Block.Preceq (rho.storeAt S v t).F
      (rho.storeAt S v t).latest_stable) :
    stableOutputAt S rho v t = (rho.storeAt S v t).F := by
  change ¬ Block.preceq (rho.storeAt S v t).F
      (rho.storeAt S v t).latest_stable = true at h
  unfold stableOutputAt Protocol.get_stable
  rw [if_neg h]

private theorem stable_safe_of_canonical (S : Setup V) {rho : Run V} {t₀ : Time}
    (hcanon : StableRecordCanonicalFrom S rho t₀)
    (hFcompat : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      t₀ ≤ t → t₀ ≤ t' → t ≤ rho.horizon → t' ≤ rho.horizon →
      Block.compatible (rho.storeAt S u t).F
        (rho.storeAt S v t').F = true)
    (hFmono : ∀ v ∈ rho.honest, ∀ t t', t₀ ≤ t → t ≤ t' →
      t' ≤ rho.horizon →
      Block.Preceq (rho.storeAt S v t).F (rho.storeAt S v t').F) :
    SafeFrom S rho (legacyInterface S).stable t₀ := by
  refine ⟨?_, ?_⟩
  · intro u hu v hv t t' ht ht' hhor hhor'
    change Block.compatible (stableOutputAt S rho u t)
      (stableOutputAt S rho v t') = true
    by_cases huF : Block.Preceq (rho.storeAt S u t).F
        (rho.storeAt S u t).latest_stable
    · by_cases hvF : Block.Preceq (rho.storeAt S v t').F
          (rho.storeAt S v t').latest_stable
      · rw [stableOutput_eq_latest S rho u t huF,
          stableOutput_eq_latest S rho v t' hvF]
        exact hcanon.agree u hu v hv t t' ht hhor ht' hhor'
      · rw [stableOutput_eq_latest S rho u t huF,
          stableOutput_eq_finalized S rho v t' hvF]
        exact hcanon.finality u hu v hv t t' ht hhor ht' hhor'
    · by_cases hvF : Block.Preceq (rho.storeAt S v t').F
          (rho.storeAt S v t').latest_stable
      · rw [stableOutput_eq_finalized S rho u t huF,
          stableOutput_eq_latest S rho v t' hvF]
        exact Protocol.compatible_comm
          (hcanon.finality v hv u hu t' t hhor ht hhor' ht')
      · rw [stableOutput_eq_finalized S rho u t huF,
          stableOutput_eq_finalized S rho v t' hvF]
        exact hFcompat u hu v hv t t' ht hhor ht' hhor'
  · intro v hv t t' ht htt hhor
    change Block.Preceq (stableOutputAt S rho v t)
      (stableOutputAt S rho v t')
    by_cases hF : Block.Preceq (rho.storeAt S v t).F
        (rho.storeAt S v t).latest_stable
    · by_cases hF' : Block.Preceq (rho.storeAt S v t').F
          (rho.storeAt S v t').latest_stable
      · rw [stableOutput_eq_latest S rho v t hF,
          stableOutput_eq_latest S rho v t' hF']
        exact hcanon.monotone v hv t t' ht htt hhor
      · rw [stableOutput_eq_latest S rho v t hF,
          stableOutput_eq_finalized S rho v t' hF']
        have hcross := hcanon.finality v hv v hv t t' ht (ht.trans htt)
          (le_trans htt hhor) hhor
        simp only [Block.compatible, Bool.or_eq_true] at hcross
        rcases hcross with hleft | hright
        · exact hleft
        · exact False.elim (hF' (Block.preceq_trans hright
            (hcanon.monotone v hv t t' ht htt hhor)))
    · by_cases hF' : Block.Preceq (rho.storeAt S v t').F
          (rho.storeAt S v t').latest_stable
      · rw [stableOutput_eq_finalized S rho v t hF,
          stableOutput_eq_latest S rho v t' hF']
        exact Block.preceq_trans (hFmono v hv t t' ht htt hhor) hF'
      · rw [stableOutput_eq_finalized S rho v t hF,
          stableOutput_eq_finalized S rho v t' hF']
        exact hFmono v hv t t' ht htt hhor

private theorem safe_confirmed_of_phase (S : Setup V) {rho : Run V}
    {m boundary cut : Round} {P : Block V}
    (hmq : m ≤ boundary)
    (hphase : PhaseShiftSafety S rho cut (S.hc.opening_slot m) P) :
    SafeFrom S rho (legacyInterface S).confirmed (healingBoundaryTime S boundary) := by
  have hstart : S.a m ≤ healingBoundaryTime S boundary :=
    action_le_healingBoundary S hmq
  refine ⟨?_, ?_⟩
  · intro u hu v hv t t' ht hth ht' hth'
    simpa [Internal.readAt, legacyInterface, Statements.«instance», Internal.confirmedOutputAt] using
      hphase.userConfirmation.outputCompatible u hu v hv t t'
        (hstart.trans ht) (hstart.trans ht') hth hth'
  · intro v hv t t' ht htt hth
    simpa [Internal.readAt, legacyInterface, Statements.«instance», Internal.confirmedOutputAt] using
      hphase.userConfirmation.outputMonotone v hv t t'
        (hstart.trans ht) htt hth

theorem available_confirmedSafe (S : Setup V) :
    ∀ rho t₀, SleepyRegime S (legacyInterface S) (legacyConstants S) rho t₀ →
      RecoveredBy S (legacyInterface S) (legacyConstants S) rho t₀ → SafeFrom S rho (legacyInterface S).confirmed t₀ := by
  intro rho t₀ hsleep hrecovered
  cases hrecovered with
  | genesis =>
      have hlegacy : WeakGenesis S rho := sleepy_genesis_to_weakGenesis S hsleep
      have h := (legacy_consensus_closed S).gstZeroGuarantees rho hlegacy
      exact ⟨confirmed_agree_bridge S h.outputCompatible,
        confirmed_monotone_bridge S h.outputMonotone⟩
  | @recovered source tPrefix gap extra hrec hcont hslash =>
      obtain ⟨rGST, n, hstrong, hsum⟩ := recovery_to_strong S hrec
      have hweak := sleepy_continuation_to_weakContinuation S hrec hstrong hsum hcont hsleep hslash
      obtain ⟨m, hmn, hmgap, _hgapm, _P, _hP, hphase⟩ :=
        (legacy_consensus_closed S).boundedSafety source rGST gap extra n hstrong
      have hs := safe_confirmed_of_phase (m := m) (cut := n)
        (boundary := n + gap) S
        hmgap (hphase rho hweak)
      simpa [legacyConstants, ourConstants, recoveryRound, hsum] using hs

private theorem positive_slot_of_positive_proposal_time (S : Setup V) {s : Slot}
    (hs : 0 < (legacyInterface S).proposalTime s) : 0 < s := by
  cases s with
  | zero => simp [legacyInterface, Statements.«instance», Protocol.proposal_time, Env.t, slotStart] at hs
  | succ k => exact Nat.zero_lt_succ _

private theorem opening_before_of_post_boundary_proposal (S : Setup V)
    {m q : Round} {s : Slot} (hmq : m ≤ q)
    (hs : healingBoundaryTime S q < Protocol.proposal_time S.E s) :
    S.hc.opening_slot m < s := by
  have hm0 : Protocol.proposal_time S.E (S.hc.opening_slot m) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q) :=
    Protocol.proposal_time_mono S.E
      (Nat.mul_le_mul_right S.hc.R hmq)
  have hq : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      healingBoundaryTime S q := by
    unfold healingBoundaryTime
    exact (Protocol.proposal_time_lt_vote_time S.E
      (S.hc.opening_slot q)).le.trans
      (Protocol.vote_time_mono_slots S.E
        (Nat.le_add_right (S.hc.opening_slot q) 2))
  have hm := hm0.trans hq
  have hslot : Protocol.proposal_time S.E (S.hc.opening_slot m) <
      Protocol.proposal_time S.E s := hm.trans_lt hs
  apply Nat.lt_of_not_ge
  intro hle
  have hge : Protocol.proposal_time S.E s ≤
      Protocol.proposal_time S.E (S.hc.opening_slot m) := by
    have hmono := Protocol.proposal_time_mono S.E hle
    omega
  exact (not_lt_of_ge hge) hslot

private theorem included_of_userProposals (S : Setup V) {rho : Run V} {t₀ : Time}
    {start : Slot} (hstart : ∀ s : Slot, t₀ < Protocol.proposal_time S.E s →
      S.E.proposer s ∈ rho.honest → start < s)
    (h : UserProposalsConfirmedAfter S rho start) :
    Included S (legacyInterface S) rho (legacyInterface S).confirmed t₀ (legacyConstants S).confirmationDelay := by
  intro s hs hp hhor
  have hslot := hstart s hs hp
  obtain ⟨B, hB, hlatest, houtput⟩ := h s hslot hhor hp
  refine ⟨B, ?_, ?_⟩
  · exact ⟨hp, hB⟩
  · intro v hv
    have htime : Protocol.confirmation_time S.E s =
        (legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay := by
      rfl
    rw [← htime]
    exact houtput v hv (Protocol.confirmation_time S.E s) le_rfl hhor

theorem available_confirmedIncluded (S : Setup V) :
    ∀ rho t₀, SleepyRegime S (legacyInterface S) (legacyConstants S) rho t₀ →
      RecoveredBy S (legacyInterface S) (legacyConstants S) rho t₀ →
      Included S (legacyInterface S) rho (legacyInterface S).confirmed t₀ (legacyConstants S).confirmationDelay := by
  intro rho t₀ hsleep hrecovered
  cases hrecovered with
  | genesis =>
      have hlegacy : WeakGenesis S rho := sleepy_genesis_to_weakGenesis S hsleep
      have h := (legacy_consensus_closed S).gstZeroGuarantees rho hlegacy
      exact included_of_userProposals S
        (fun s hs _ => positive_slot_of_positive_proposal_time S hs) h.userProposals
  | @recovered source tPrefix gap extra hrec hcont hslash =>
      obtain ⟨rGST, n, hstrong, hsum⟩ := recovery_to_strong S hrec
      have hweak := sleepy_continuation_to_weakContinuation S hrec hstrong hsum hcont hsleep hslash
      obtain ⟨m, hmn, hmgap, _hgapm, _P, _hP, hphase⟩ :=
        (legacy_consensus_closed S).boundedSafety source rGST gap extra n hstrong
      have hrecover : (legacyConstants S).recoveryEnd tPrefix gap extra =
          healingBoundaryTime S (n + gap) := by
        simpa [legacyConstants, ourConstants, recoveryRound, hsum]
      exact included_of_userProposals S
        (fun s hs hp => opening_before_of_post_boundary_proposal S
          hmgap (by simpa [hrecover] using hs))
        (hphase rho hweak).userConfirmation.proposals

theorem available_stableSafe (S : Setup V) :
    ∀ rho t₀, SleepyRegime S (legacyInterface S) (legacyConstants S) rho t₀ →
      RecoveredBy S (legacyInterface S) (legacyConstants S) rho t₀ → SafeFrom S rho (legacyInterface S).stable t₀ := by
  intro rho t₀ hsleep hrecovered
  cases hrecovered with
  | genesis =>
      have hlegacy : WeakGenesis S rho := sleepy_genesis_to_weakGenesis S hsleep
      have h := (legacy_consensus_closed S).gstZeroGuarantees rho hlegacy
      have hcanon := (legacy_consensus_closed S).stableSafety.gstZero rho hlegacy
      have hFcompat := finalized_compatible_of_confirmed_compatible S
        h.outputCompatible
      have hFmono : ∀ v ∈ rho.honest, ∀ t t', 0 ≤ t → t ≤ t' →
          t' ≤ rho.horizon →
          Block.Preceq (rho.storeAt S v t).F (rho.storeAt S v t').F := by
        intro v hv t t' ht htt hhor
        exact StoreFinality.stateAt_F_mono S
          hlegacy.core.toNamedScheduleWellFormed v htt
      exact stable_safe_of_canonical S hcanon hFcompat hFmono
  | @recovered source tPrefix gap extra hrec hcont hslash =>
      obtain ⟨rGST, n, hstrong, hsum⟩ := recovery_to_strong S hrec
      have hweak := sleepy_continuation_to_weakContinuation S hrec hstrong hsum hcont hsleep hslash
      obtain ⟨m, hmn, hmgap, hcanonCont⟩ :=
        (legacy_consensus_closed S).stableSafety.afterGST
          source rGST gap extra n hstrong
      have hcanonM := hcanonCont rho hweak
      have hcanon : StableRecordCanonicalFrom S rho
          (healingBoundaryTime S (n + gap)) :=
        Proofs.HealingSurface.Handover.StableRecordCanonicalFrom.mono_start S
          (healingBoundary_mono S hmgap) hcanonM
      have hFcompat : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
          healingBoundaryTime S (n + gap) ≤ t →
          healingBoundaryTime S (n + gap) ≤ t' →
          t ≤ rho.horizon → t' ≤ rho.horizon →
          Block.compatible (rho.storeAt S u t).F
            (rho.storeAt S v t').F = true := by
        intro u hu v hv t t' ht ht' hhor hhor'
        exact (legacy_consensus_closed S).finality.runAgreement rho
          (FinalityExecution.of_executionValid hweak.execution)
          (oldSlashableBound_of_standard S hslash) |>.2 u hu v hv t t'
      have hFmono : ∀ v ∈ rho.honest, ∀ t t',
          healingBoundaryTime S (n + gap) ≤ t → t ≤ t' →
          t' ≤ rho.horizon →
          Block.Preceq (rho.storeAt S v t).F (rho.storeAt S v t').F := by
        intro v hv t t' ht htt hhor
        exact StoreFinality.stateAt_F_mono S
          hweak.core.toNamedScheduleWellFormed v htt
      have hs := stable_safe_of_canonical S hcanon hFcompat hFmono
      simpa [legacyConstants, ourConstants, recoveryRound, hsum] using hs

theorem outage_stablePersists (S : Setup V) :
    ∀ rho b₀ b₁ (T : Time) v P,
      OutageRegime S (legacyInterface S) (legacyConstants S) rho b₀ b₁ →
      Statements.SlashableBound (legacyInterface S) rho → v ∈ rho.honest →
      Block.Preceq P (readAt S rho (legacyInterface S).stable v T) →
      Statements.Instantiation.nextAction S T + (legacyConstants S).formationMargin ≤ b₀ →
      b₁ + S.E.Δ ≤ (legacyConstants S).expiry (Statements.Instantiation.nextAction S T) →
      b₁ + S.E.Δ ≤ rho.horizon →
      ∀ t, b₀ ≤ t → t ≤ rho.horizon → InBy S rho (legacyInterface S).stable P t := by
  intro rho b₀ b₁ T v P hout hslash hv houtput hmargin hret hhor
  have hexec : NamedOutageEntry.OutageExecution S rho b₀ b₁ :=
    { execution := hout.execution
      synchrony := hout.synchrony
      interval := hout.interval
      healthy := hout.healthy
      gst := hout.gst
      boundaryPublic := hout.boundaryPublic }
  have hslash' := oldSlashableBound_of_standard S hslash
  have hcom := committees_bridge S hout.committees
  have hmargin' : Statements.Instantiation.nextAction S T +
      Statements.Instantiation.roundLength S + S.E.Δ ≤ b₀ := by
    simpa [legacyConstants, ourConstants, Statements.Instantiation.roundLength,
      NamedOutageClosure.a_eq_roundLength, add_assoc, add_comm, add_left_comm]
      using hmargin
  have houtput' : Block.Preceq P
      (Protocol.get_stable (Run.storeAt S rho v T).core) := by
    change Block.Preceq P (Protocol.get_stable (Run.storeAt S rho v T).core) at houtput
    exact houtput
  have ha : S.a (Statements.Instantiation.roundAfter S T + S.hc.η_SG + 1) =
      Statements.Instantiation.nextAction S T +
        ((S.hc.η_SG : Time) + 1) * Statements.Instantiation.roundLength S := by
    unfold Statements.Instantiation.nextAction
    rw [NamedOutageClosure.a_eq_roundLength, NamedOutageClosure.a_eq_roundLength]
    push_cast
    ring
  have hret' : b₁ + S.E.Δ ≤ Statements.Instantiation.nextAction S T +
      ((S.hc.η_SG : Time) + 1) * Statements.Instantiation.roundLength S -
        11 * S.E.Δ := by
    have hret'' : b₁ + S.E.Δ ≤
        S.a (Statements.Instantiation.roundAfter S T + S.hc.η_SG + 1) -
          11 * S.E.Δ := by
      simpa [legacyConstants, ourConstants, Statements.Instantiation.nextAction,
        Proofs.HealingLemmas.round_of_slotOf_a, NamedOutageClosure.early_g2_eq]
        using hret
    rw [ha] at hret''
    exact hret''
  have hsleep := NamedOutageClosure.outageSleepyThroughout_of_awake S rho
    hout.participation
  have hforming := NamedOutageClosure.gradeFormingThroughout_of_awake S rho
    hout.execution.toNamedScheduleWellFormed hout.participation
  have h := NamedOutageClosure.stable_chain_outage_resilience_public S
    rho b₀ b₁ T v P hexec hslash' hcom hout.participation hv hmargin'
    houtput' hret' hhor
  intro t ht htime w hw
  exact h w hw t ht htime

private theorem confirmed_output_mem_storeAt (S : Setup V) (rho : Run V)
    (v : V) (t : Time) :
    confirmedOutputAt S rho v t ∈ (rho.storeAt S v t).T := by
  have hinv := Proofs.NamedRuntime.readAt_invariants S rho t v
  have hF : (rho.storeAt S v t).F ∈ (rho.storeAt S v t).T := hinv.1.1.2.1
  have hL : (rho.storeAt S v t).latest_confirmed ∈
      (rho.storeAt S v t).T := hinv.1.2.2.1
  have hS : (rho.storeAt S v t).latest_stable ∈
      (rho.storeAt S v t).T := hinv.1.2.2.2
  unfold confirmedOutputAt Protocol.get_confirmed
  split
  · exact hL
  · unfold Protocol.get_stable
    split
    · exact hS
    · exact hF

private theorem stable_output_mem_storeAt (S : Setup V) (rho : Run V)
    (v : V) (t : Time) :
    stableOutputAt S rho v t ∈ (rho.storeAt S v t).T := by
  have hinv := Proofs.NamedRuntime.readAt_invariants S rho t v
  have hF : (rho.storeAt S v t).F ∈ (rho.storeAt S v t).T := hinv.1.1.2.1
  have hS : (rho.storeAt S v t).latest_stable ∈
      (rho.storeAt S v t).T := hinv.1.2.2.2
  unfold stableOutputAt Protocol.get_stable
  split
  · exact hS
  · exact hF

private theorem action_le_confirmation_after_opening (S : Setup V)
    {r : Round} {s : Slot} (hs : S.hc.opening_slot r < s) :
    S.a r ≤ Protocol.confirmation_time S.E s := by
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot
    Protocol.confirmation_time Env.t slotStart
  push_cast
  have hR : (3 : Int) ≤ S.hc.R := by exact_mod_cast S.hc.R_ge_three
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hs' : (S.hc.opening_slot r : Int) < (s : Int) := by
    exact_mod_cast hs
  simp only [Protocol.HealConfig.opening_slot] at hs'
  have h4Δ : (0 : Int) < 4 * S.E.Δ := by nlinarith
  have hmul := Int.mul_lt_mul_of_pos_left hs' h4Δ
  have hmul' : 4 * S.E.Δ * ((r : Int) * (S.hc.R : Int)) <
      4 * S.E.Δ * (s : Int) := by
    simpa only [Nat.cast_mul] using hmul
  nlinarith

private theorem storeAt_eq_storeBeforeTime_succ (S : Setup V) (rho : Run V)
    (v : V) (t : Time) :
    rho.storeAt S v t = rho.storeBeforeTime S v (t + 1) := by
  have hbool (a b : Int) : decide (a ≤ b) = decide (a < b + 1) := by
    simp only [Int.lt_add_one_iff]
  have hfilter : rho.events.filter (fun e => decide (e.time ≤ t)) =
      rho.events.filter (fun e => decide (e.time < t + 1)) :=
    List.filter_congr (fun e _ => hbool e.time t)
  have hstate : NamedRun.readAt S rho t =
      NamedRun.stateBeforeTime S rho (t + 1) := by
    unfold NamedRun.readAt NamedRun.stateBeforeTime
    rw [hfilter]
  unfold Run.storeAt Run.storeBeforeTime
  rw [hstate]

private theorem stateAt_eq_stateBefore_le (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (t : Time) :
    ∃ n : Nat, Run.stateAt S rho t = rho.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → rho.events[j]? = some e → e.time ≤ t :=
  (Proofs.Bridges.filtered_fold_eq_stateBefore S sch
    (p := fun e => decide (e.time ≤ t))
    (fun e f hk hf => by
      simp only [decide_eq_true_eq] at hf ⊢
      exact le_trans (Proofs.Bridges.time_le_of_key_le hk) hf)).imp fun _ h =>
    ⟨h.1, fun j e hj hget => by simpa using h.2 j e hj hget⟩

private theorem proposal_time_le_of_mem_storeAt
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {t : Time} (ht : 0 ≤ t) {C : Block V}
    (hC : C ∈ (rho.storeAt S v t).T) :
    Protocol.proposal_time S.E C.slot ≤ t := by
  obtain ⟨n, hn, hbefore⟩ := stateAt_eq_stateBefore_le S
    adm.toNamedScheduleWellFormed t
  have hnv : NamedRun.readAt S rho t v = rho.stateBefore S n v :=
    congrFun hn v
  have hCn : C ∈ (rho.stateBefore S n v).st.core.T := by
    have hC' : C ∈ (NamedRun.readAt S rho t v).st.core.T := hC
    rwa [hnv] at hC'
  obtain ⟨D, hD, hDe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hCn
  have hprocessed : Object.processed (rho.stateBefore S n v).st (.block D) = true := by
    simp only [NamedReceipt.processed, decide_eq_true_eq]
    exact hD
  rcases Protocol.acceptsAt_block_of_processed S rho v n D hprocessed with
      hgen | ⟨i, hin, time, hacc⟩
  · subst D
    simp only [NamedBlock.erase] at hDe
    subst C
    simpa [Protocol.proposal_time, Env.t, slotStart] using ht
  · obtain ⟨_, e, he, _, het⟩ := hacc.1
    have htime : time ≤ t := by
      rw [← het]
      exact hbefore i e hin he
    have hCtime : Protocol.proposal_time S.E C.slot ≤ time := by
      simpa [hDe] using
        (Proofs.NamedSlotFreshness.proposal_time_le_of_acceptsAt_block S adm hacc)
    exact hCtime.trans htime

private theorem confirmed_growth_from_round
    (S : Setup V) {rho : Run V} {t₀ D : Time} {start : Slot} {gap : Round}
    (adm : AdmissibleCore S rho)
    (hround : AvailableChainGrowthFrom S rho start gap)
    (hmono : ConfirmedOutputMonotoneFrom S rho t₀)
    (selector : ∀ t, t₀ ≤ t → t + D ≤ rho.horizon →
      ∃ r : Round, start ≤ S.hc.opening_slot r ∧ t ≤ S.a r ∧
        t < Protocol.proposal_time S.E (S.hc.opening_slot r + 1) ∧
        S.a (r + gap) ≤ t + D) :
    Growth S rho (legacyInterface S).confirmed t₀ D (honestAfter (legacyInterface S) rho) := by
  intro t ht hdeadline
  obtain ⟨r, hrstart, htr, hproposal, hrdeadline⟩ := selector t ht hdeadline
  obtain ⟨s, hsopen, hp, hconf, B, hB, _hrecords, houtputs⟩ :=
    hround r hrstart (hrdeadline.trans hdeadline)
  have hspos : 0 < s := Nat.zero_lt_of_lt
    (lt_of_le_of_lt (Nat.zero_le (S.hc.opening_slot r)) hsopen)
  have hsAfter : t < Protocol.proposal_time S.E s := by
    have hslot : S.hc.opening_slot r + 1 ≤ s := Nat.succ_le_of_lt hsopen
    exact hproposal.trans_le (Protocol.proposal_time_mono S.E hslot)
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    hconf.trans (hrdeadline.trans hdeadline)
  have har : S.a r ≤ Protocol.confirmation_time S.E s := by
    exact action_le_confirmation_after_opening S hsopen
  have hstrictAt : ∀ v ∈ rho.honest,
      Block.Prec (confirmedOutputAt S rho v t) B.erase := by
    intro v hv
    have hTConf := Block.preceq_trans
      (hmono v hv t (S.a r) ht htr
        ((Assembly.a_mono S (Nat.le_add_right r gap)).trans
          (hrdeadline.trans hdeadline)))
      (hmono v hv (S.a r) (Protocol.confirmation_time S.E s)
        (ht.trans htr) har hconfHor)
    have hBConf := (houtputs v hv (Protocol.confirmation_time S.E s)
      le_rfl hconfHor).2
    have hcompat := Block.compatible_of_preceq_common hTConf hBConf
    have hneq' : confirmedOutputAt S rho v t ≠ B.erase := by
      intro heq
      have hmem := confirmed_output_mem_storeAt S rho v t
      rw [heq] at hmem
      have hslot := w4_block_slot_lt_of_mem_storeAt S adm
        hspos hsAfter hmem
      have hBslot : B.erase.slot = s := by
        rw [Proofs.NamedWire.erase_slot]
        exact DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hB
      exact (Nat.ne_of_lt (hslot.trans_eq hBslot.symm)) rfl
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    rcases hcompat with hTB | hBT
    · simp only [Block.Prec, Block.prec, hneq', decide_false, Bool.not_false,
        Bool.true_and]
      exact hTB
    · have hmem := confirmed_output_mem_storeAt S rho v t
      rw [storeAt_eq_storeBeforeTime_succ S rho v t] at hmem
      have hslotle := Proofs.NamedSlotFreshness.preceq_slot_le_of_mem_storeBeforeTime
        S adm _ hmem B.erase hBT
      have hslot := w4_block_slot_lt_of_mem_storeAt S adm
        hspos hsAfter (confirmed_output_mem_storeAt S rho v t)
      have hBslot : B.erase.slot = s := by
        rw [Proofs.NamedWire.erase_slot]
        exact DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hB
      have hsle : s ≤ (confirmedOutputAt S rho v t).slot := by
        simpa [hBslot] using hslotle
      exact False.elim ((Nat.not_lt_of_ge hsle) hslot)
  refine ⟨B, ?_, ?_, ?_⟩
  · exact ⟨s, hsAfter, ⟨hp, hB⟩⟩
  · intro v hv
    simpa [Internal.readAt, legacyInterface, Statements.«instance», Internal.confirmedOutputAt]
      using hstrictAt v hv
  · intro v hv
    exact (houtputs v hv (t + D)
      (hconf.trans hrdeadline) hdeadline).2

private theorem roundAt_prev_action_lt (S : Setup V) (t : Time)
    {q : Round} (hq : 0 < q) (heq : q = roundAt S t) :
    S.a (q - 1) < t := by
  subst q
  exact lt_of_not_ge (Statements.roundAt_min S t
    (Nat.sub_lt (Nat.zero_lt_of_lt hq) (by decide)))

private theorem round_le_of_action_le (S : Setup V) {m q : Round}
    (h : S.a m ≤ S.a q) : m ≤ q := by
  exact Nat.le_of_not_gt (fun hmq =>
    (not_lt_of_ge h) (Proofs.HealingSurface.action_strictMono S hmq))

private theorem roundLength_formula (S : Setup V) :
    S.a 1 - S.a 0 = 4 * S.E.Δ * (S.hc.R : Int) := by
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
  push_cast
  ring

private theorem action_le_after_next_slot_proposal (S : Setup V)
    {q : Round} {t : Time}
    (h : Protocol.proposal_time S.E (S.hc.opening_slot q + 1) ≤ t) :
    S.a q ≤ t + 2 * S.E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart at h
  simp only [Protocol.HealConfig.opening_slot] at h
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
    at ⊢
  push_cast at h ⊢
  have hR : (3 : Int) ≤ S.hc.R := by exact_mod_cast S.hc.R_ge_three
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  nlinarith

private theorem action_gap_deadline_zero (S : Setup V) {t D : Time} {gap : Round}
    (ht : 0 ≤ t)
    (hD : D = (gap + 1 : Time) * (S.a 1 - S.a 0) + 2 * S.E.Δ) :
    S.a gap ≤ t + D := by
  rw [hD, ← Nat.zero_add gap, Proofs.HealingLemmas.a_add_rounds, roundLength_formula]
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
  push_cast
  ring_nf
  have hR : (3 : Int) ≤ S.hc.R := by exact_mod_cast S.hc.R_ge_three
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  nlinarith

private theorem action_gap_deadline_prev (S : Setup V) {t D : Time} {q gap : Round}
    (hq : 0 < q) (hprev : S.a (q - 1) < t)
    (hD : D = (gap + 1 : Time) * (S.a 1 - S.a 0) + 2 * S.E.Δ) :
    S.a (q + gap) ≤ t + D := by
  have hqsucc : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  have hqgap : q + gap = (q - 1) + (gap + 1) := by
    calc
      q + gap = (q - 1 + 1) + gap := by rw [hqsucc]
      _ = (q - 1) + (1 + gap) := by simp [Nat.add_assoc]
      _ = (q - 1) + (gap + 1) := by rw [Nat.add_comm 1 gap]
  rw [hqgap, Proofs.HealingLemmas.a_add_rounds, hD, roundLength_formula]
  push_cast
  ring_nf
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  nlinarith

private theorem action_gap_deadline_next (S : Setup V) {t D : Time} {q gap : Round}
    (hnext : Protocol.proposal_time S.E (S.hc.opening_slot q + 1) ≤ t)
    (hD : D = (gap + 1 : Time) * (S.a 1 - S.a 0) + 2 * S.E.Δ) :
    S.a (q + 1 + gap) ≤ t + D := by
  have haq := action_le_after_next_slot_proposal S hnext
  have hqgap : q + 1 + gap = q + (gap + 1) := by
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hqgap, Proofs.HealingLemmas.a_add_rounds, hD, roundLength_formula]
  push_cast
  ring_nf
  have hL : (0 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by
    have hΔ : (0 : Int) ≤ S.E.Δ := S.E.Δ_pos.le
    have hR : (0 : Int) ≤ S.hc.R := by
      exact_mod_cast (Nat.zero_le S.hc.R)
    positivity
  have hg : (0 : Int) ≤ (gap : Int) := by omega
  have hprod : (0 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) * (gap : Int) :=
    mul_nonneg hL hg
  nlinarith

private theorem confirmed_growth_selector
    (S : Setup V) {t₀ D H : Time} {start : Slot} {gap : Round}
    (hstart : ∀ t, t₀ ≤ t → start ≤ S.hc.opening_slot (roundAt S t))
    (ht₀ : 0 ≤ t₀)
    (hD : D = (gap + 1 : Time) * (S.a 1 - S.a 0) + 2 * S.E.Δ) :
    ∀ t, t₀ ≤ t → t + D ≤ H →
      ∃ r : Round, start ≤ S.hc.opening_slot r ∧ t ≤ S.a r ∧
        t < Protocol.proposal_time S.E (S.hc.opening_slot r + 1) ∧
        S.a (r + gap) ≤ t + D := by
  intro t ht _
  let q := roundAt S t
  have hqeq : q = roundAt S t := rfl
  have hq : t ≤ S.a q := roundAt_spec S t
  have hstartq : start ≤ S.hc.opening_slot q := hstart t ht
  have hqnonneg : 0 ≤ t := ht₀.trans ht
  by_cases hnext : t < Protocol.proposal_time S.E (S.hc.opening_slot q + 1)
  · refine ⟨q, hstartq, hq, hnext, ?_⟩
    by_cases hqzero : q = 0
    · subst q
      simp only [hqzero] at hq hstartq hnext ⊢
      simpa only [Nat.zero_add] using (action_gap_deadline_zero S hqnonneg hD)
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
      have hprev := roundAt_prev_action_lt S t hqpos hqeq
      exact action_gap_deadline_prev S hqpos hprev hD
  · have hnext_le : Protocol.proposal_time S.E
        (S.hc.opening_slot q + 1) ≤ t := le_of_not_gt hnext
    have hqnext : t < Protocol.proposal_time S.E
        (S.hc.opening_slot (q + 1) + 1) := by
      have haction : S.a q < Protocol.proposal_time S.E
          (S.hc.opening_slot (q + 1) + 1) := by
        have hbase := Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
          S (Nat.lt_succ_self q)
        have hbase' : S.a q < Protocol.proposal_time S.E
            (S.hc.opening_slot (q + 1)) :=
          lt_of_lt_of_le (lt_add_of_pos_right _ S.E.Δ_pos) hbase
        exact hbase'.trans_le
          (Protocol.proposal_time_mono S.E
            (Nat.le_add_right (S.hc.opening_slot (q + 1)) 1))
      exact hq.trans_lt haction
    refine ⟨q + 1,
      hstartq.trans (Nat.mul_le_mul_right S.hc.R (Nat.le_succ q)),
      hq.trans (Assembly.a_mono S (Nat.le_succ q)), hqnext, ?_⟩
    exact action_gap_deadline_next S hnext_le hD

private theorem stable_growth_from_round
    (S : Setup V) {rho : Run V} {t₀ D : Time} {start : Slot} {gap : Round}
    (adm : AdmissibleCore S rho)
    (hround : StableRecordGrowthFrom S rho start gap)
    (hmono : MonotoneFrom S rho (legacyInterface S).stable t₀)
    (hDnonneg : 0 ≤ D)
    (selector : ∀ t, t₀ ≤ t → t + D ≤ rho.horizon →
      ∃ r : Round, start ≤ S.hc.opening_slot r ∧ t ≤ S.a r ∧
        t < Protocol.proposal_time S.E (S.hc.opening_slot r + 1) ∧
        S.a (r + gap) ≤ t + D) :
    Growth S rho (legacyInterface S).stable t₀ D (honestAfter (legacyInterface S) rho) := by
  intro t ht hdeadline
  obtain ⟨r, hrstart, htr, hproposal, hrdeadline⟩ := selector t ht hdeadline
  obtain ⟨B, ⟨s, hsopen, hp, hB⟩, hgrowth⟩ :=
    hround r hrstart (hrdeadline.trans hdeadline)
  have hspos : 0 < s := Nat.zero_lt_of_lt
    (lt_of_le_of_lt (Nat.zero_le (S.hc.opening_slot r)) hsopen)
  have hsAfter : t < Protocol.proposal_time S.E s := by
    have hslot : S.hc.opening_slot r + 1 ≤ s := Nat.succ_le_of_lt hsopen
    exact hproposal.trans_le (Protocol.proposal_time_mono S.E hslot)
  have hstrictAt : ∀ v ∈ rho.honest,
      Block.Prec (stableOutputAt S rho v t) B.erase := by
    intro v hv
    have hfuture := ((hgrowth v hv).2 (t + D) hrdeadline hdeadline).2
    have hTFuture := hmono v hv t (t + D) ht
      (le_add_of_nonneg_right hDnonneg) hdeadline
    have hcompat := Block.compatible_of_preceq_common hTFuture hfuture
    have hneq : stableOutputAt S rho v t ≠ B.erase := by
      intro heq
      have hmem := stable_output_mem_storeAt S rho v t
      rw [heq] at hmem
      have hslot := w4_block_slot_lt_of_mem_storeAt S adm hspos hsAfter hmem
      have hBslot : B.erase.slot = s := by
        rw [Proofs.NamedWire.erase_slot]
        exact DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hB
      exact (Nat.ne_of_lt (hslot.trans_eq hBslot.symm)) rfl
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    rcases hcompat with hTB | hBT
    · simp only [Block.Prec, Block.prec, hneq, decide_false, Bool.not_false,
        Bool.true_and]
      exact hTB
    · have hmem := stable_output_mem_storeAt S rho v t
      rw [storeAt_eq_storeBeforeTime_succ S rho v t] at hmem
      have hslotle := Proofs.NamedSlotFreshness.preceq_slot_le_of_mem_storeBeforeTime
        S adm _ hmem B.erase hBT
      have hslot := w4_block_slot_lt_of_mem_storeAt S adm hspos hsAfter
        (stable_output_mem_storeAt S rho v t)
      have hBslot : B.erase.slot = s := by
        rw [Proofs.NamedWire.erase_slot]
        exact DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hB
      have hsle : s ≤ (stableOutputAt S rho v t).slot := by
        simpa [hBslot] using hslotle
      exact False.elim ((Nat.not_lt_of_ge hsle) hslot)
  refine ⟨B, ?_, ?_, ?_⟩
  · exact ⟨s, hsAfter, ⟨hp, hB⟩⟩
  · intro v hv
    simpa [Internal.readAt, legacyInterface, Statements.«instance», Internal.stableOutputAt]
      using hstrictAt v hv
  · intro v hv
    simpa [Internal.readAt, legacyInterface, Statements.«instance», Internal.stableOutputAt]
      using ((hgrowth v hv).2 (t + D) hrdeadline hdeadline).2

theorem available_stableGrowth (S : Setup V) :
    ∀ rho t₀, SleepyRegime S (legacyInterface S) (legacyConstants S) rho t₀ →
      RecoveredBy S (legacyInterface S) (legacyConstants S) rho t₀ →
      ∀ gap, ProposerOpeningCarrierRecurrence S rho gap →
        Growth S rho (legacyInterface S).stable t₀ ((legacyConstants S).stableGrowthDelay gap)
          (honestAfter (legacyInterface S) rho) := by
  intro rho t₀ hsleep hrecovered gap hrec
  cases hrecovered with
  | genesis =>
      have hlegacy : WeakGenesis S rho := sleepy_genesis_to_weakGenesis S hsleep
      have hgen := (legacy_consensus_closed S).gstZeroGuarantees rho hlegacy
      have hcanon := (legacy_consensus_closed S).stableSafety.gstZero rho hlegacy
      have hFcompat := finalized_compatible_of_confirmed_compatible S
        hgen.outputCompatible
      have hFmono : ∀ v ∈ rho.honest, ∀ t t', 0 ≤ t → t ≤ t' →
          t' ≤ rho.horizon →
          Block.Preceq (rho.storeAt S v t).F (rho.storeAt S v t').F := by
        intro v hv t t' ht htt hhor
        exact StoreFinality.stateAt_F_mono S
          hlegacy.core.toNamedScheduleWellFormed v htt
      have hsafe := stable_safe_of_canonical S hcanon hFcompat hFmono
      have hround := (legacy_consensus_closed S).liveness.stableRecordGrowth.gstZero
        rho hlegacy gap hrec
      let rgap : Round := gap + S.hc.η_SG - 1
      have hrgap : rgap + 1 = gap + S.hc.η_SG := by
        dsimp [rgap]
        have hle : 1 ≤ gap + S.hc.η_SG :=
          S.hc.η_SG_ge_one.trans (Nat.le_add_left _ _)
        exact Nat.sub_add_cancel hle
      have hrgap' : (rgap : Time) + 1 = (gap + S.hc.η_SG : Time) := by
        exact_mod_cast hrgap
      have hD : (legacyConstants S).stableGrowthDelay gap =
          (rgap + 1 : Time) * (S.a 1 - S.a 0) + 2 * S.E.Δ := by
        dsimp [legacyConstants, ourConstants]
        rw [hrgap']
      have hDnonneg : 0 ≤ (legacyConstants S).stableGrowthDelay gap := by
        rw [hD, roundLength_formula]
        have hR : (0 : Int) ≤ S.hc.R := by positivity
        have hΔ : (0 : Int) ≤ S.E.Δ := S.E.Δ_pos.le
        positivity
      have hselector := confirmed_growth_selector (H := rho.horizon) S
        (start := 0) (gap := rgap) (t₀ := 0)
        (D := (legacyConstants S).stableGrowthDelay gap)
        (fun _ _ => Nat.zero_le _) le_rfl hD
      exact stable_growth_from_round S hlegacy.core hround hsafe.monotone
        hDnonneg (by simpa [legacyConstants, ourConstants] using hselector)
  | @recovered source tPrefix gap0 extra hrec0 hcont hslash =>
      obtain ⟨rGST, n, hstrong, hsum⟩ := recovery_to_strong S hrec0
      have hweak := sleepy_continuation_to_weakContinuation S hrec0 hstrong hsum
        hcont hsleep hslash
      obtain ⟨m, hmn, hmgap, hcanonCont⟩ :=
        (legacy_consensus_closed S).stableSafety.afterGST source rGST gap0 extra n hstrong
      have hcanonM := hcanonCont rho hweak
      have hcanon : StableRecordCanonicalFrom S rho
          (healingBoundaryTime S (n + gap0)) :=
        Proofs.HealingSurface.Handover.StableRecordCanonicalFrom.mono_start S
          (healingBoundary_mono S hmgap) hcanonM
      have hFcompat : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
          healingBoundaryTime S (n + gap0) ≤ t →
          healingBoundaryTime S (n + gap0) ≤ t' →
          t ≤ rho.horizon → t' ≤ rho.horizon →
          Block.compatible (rho.storeAt S u t).F
            (rho.storeAt S v t').F = true := by
        intro u hu v hv t t' ht ht' hhor hhor'
        exact (legacy_consensus_closed S).finality.runAgreement rho
          (FinalityExecution.of_executionValid hweak.execution)
          (oldSlashableBound_of_standard S hslash) |>.2 u hu v hv t t'
      have hFmono : ∀ v ∈ rho.honest, ∀ t t',
          healingBoundaryTime S (n + gap0) ≤ t → t ≤ t' →
          t' ≤ rho.horizon →
          Block.Preceq (rho.storeAt S v t).F (rho.storeAt S v t').F := by
        intro v hv t t' ht htt hhor
        exact StoreFinality.stateAt_F_mono S
          hweak.core.toNamedScheduleWellFormed v htt
      have hsafe := stable_safe_of_canonical S hcanon hFcompat hFmono
      obtain ⟨mGrowth, hmgrowLo, hmgrowHi, hGrowthCont⟩ :=
        (legacy_consensus_closed S).liveness.stableRecordGrowth.afterGST
          source rGST gap0 extra n hstrong
      have hround := hGrowthCont rho hweak gap hrec
      let rgap : Round := gap + S.hc.η_SG - 1
      have hrgap : rgap + 1 = gap + S.hc.η_SG := by
        dsimp [rgap]
        have hle : 1 ≤ gap + S.hc.η_SG :=
          S.hc.η_SG_ge_one.trans (Nat.le_add_left _ _)
        exact Nat.sub_add_cancel hle
      have hrgap' : (rgap : Time) + 1 = (gap + S.hc.η_SG : Time) := by
        exact_mod_cast hrgap
      have hD : (legacyConstants S).stableGrowthDelay gap =
          (rgap + 1 : Time) * (S.a 1 - S.a 0) + 2 * S.E.Δ := by
        dsimp [legacyConstants, ourConstants]
        rw [hrgap']
      have hDnonneg : 0 ≤ (legacyConstants S).stableGrowthDelay gap := by
        rw [hD, roundLength_formula]
        have hR : (0 : Int) ≤ S.hc.R := by positivity
        have hΔ : (0 : Int) ≤ S.E.Δ := S.E.Δ_pos.le
        positivity
      have hbound : S.a mGrowth ≤ (legacyConstants S).recoveryEnd tPrefix gap0 extra := by
        simpa [legacyConstants, ourConstants, recoveryRound, hsum] using
          (action_le_healingBoundary S hmgrowHi)
      have hselector := confirmed_growth_selector (H := rho.horizon) S
        (start := S.hc.opening_slot mGrowth) (gap := rgap)
        (t₀ := (legacyConstants S).recoveryEnd tPrefix gap0 extra)
        (D := (legacyConstants S).stableGrowthDelay gap)
        (fun t ht => by
          have hq := roundAt_spec S t
          have hmq := round_le_of_action_le S (hbound.trans (ht.trans hq))
          exact Nat.mul_le_mul_right S.hc.R hmq)
        (by
          have hnon := (Proofs.HealingLemmas.a_nonneg S
            (recoveryRound S tPrefix gap0 extra)).trans
            (a_le_healingBoundaryTime S (recoveryRound S tPrefix gap0 extra))
          simpa [legacyConstants, ourConstants, recoveryRound, hsum] using hnon) hD
      have hmono : MonotoneFrom S rho (legacyInterface S).stable
          ((legacyConstants S).recoveryEnd tPrefix gap0 extra) := by
        simpa [legacyConstants, ourConstants, recoveryRound, hsum] using hsafe.monotone
      exact stable_growth_from_round S hweak.core hround hmono
        hDnonneg (by simpa [legacyConstants, ourConstants] using hselector)

private theorem honestProposalReadSafety_of_available
    (S : Setup V) {rho : Run V} {t₀ : Time}
    (hsleep : SleepyRegime S (legacyInterface S) (legacyConstants S) rho t₀)
    (hrecovered : RecoveredBy S (legacyInterface S) (legacyConstants S) rho t₀)
    {s : Slot} (hs : 0 < s)
    (hafter : t₀ < Protocol.proposal_time S.E s)
    (hconf : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest) :
    HonestProposalReadSafety S rho s := by
  cases hrecovered with
  | genesis =>
      have hlegacy : WeakGenesis S rho := sleepy_genesis_to_weakGenesis S hsleep
      exact (legacy_consensus_closed S).gstZeroGuarantees rho hlegacy
        |>.proposalReads s hs hconf hprop
  | @recovered source tPrefix gap extra hrec hcont hslash =>
      obtain ⟨rGST, n, hstrong, hsum⟩ := recovery_to_strong S hrec
      have hweak := sleepy_continuation_to_weakContinuation S hrec hstrong hsum
        hcont hsleep hslash
      obtain ⟨m, hmn, hmgap, _hgapm, _P, _hP, hphase⟩ :=
        (legacy_consensus_closed S).boundedSafety source rGST gap extra n hstrong
      have hrecover : (legacyConstants S).recoveryEnd tPrefix gap extra =
          healingBoundaryTime S (n + gap) := by
        simpa [legacyConstants, ourConstants, recoveryRound, hsum]
      have hmopen : S.hc.opening_slot m < s :=
        opening_before_of_post_boundary_proposal S hmgap
          (by simpa [hrecover] using hafter)
      exact (hphase rho hweak).honestProposalReads s hmopen hconf hprop

/-- Inclusion delay of the stable output for recurrence gap `gap` (to become
`Constants.stableInclusionDelay`). -/
noncomputable def stableInclusionDelay (S : Setup V) (gap : Nat) : Time :=
  6 * S.E.Δ + (legacyConstants S).stableGrowthDelay gap

theorem stableInclusionDelay_eq_constant (S : Setup V) (gap : Nat) :
    stableInclusionDelay S gap =
      (Statements.Instantiation.constants S).stableInclusionDelay gap := by
  rfl

theorem available_stableIncluded (S : Setup V) :
    ∀ rho t₀, SleepyRegime S (legacyInterface S) (legacyConstants S) rho t₀ →
      RecoveredBy S (legacyInterface S) (legacyConstants S) rho t₀ →
      ∀ gap, legacyStrongMultiProposerRecurrence S rho gap →
        Included S (legacyInterface S) rho (legacyInterface S).stable t₀ (stableInclusionDelay S gap) := by
  intro rho t₀ hsleep hrecovered gap hrec
  have hstable := available_stableGrowth S rho t₀ hsleep hrecovered gap hrec
  have hstableDnonneg : 0 ≤ (legacyConstants S).stableGrowthDelay gap := by
    dsimp [legacyConstants, ourConstants]
    rw [roundLength_formula]
    have hR : (0 : Int) ≤ S.hc.R := by positivity
    have hΔ : (0 : Int) ≤ S.E.Δ := S.E.Δ_pos.le
    positivity
  have hconfirmationDnonneg : 0 ≤ (legacyConstants S).confirmationDelay := by
    dsimp [legacyConstants, ourConstants]
    exact mul_nonneg (by norm_num) S.E.Δ_pos.le
  intro s hs hprop hdeadline
  have ht₀nonneg : 0 ≤ t₀ := S.E.t_GST_nonneg.trans hsleep.gst
  have hproposalPos : 0 < (legacyInterface S).proposalTime s := ht₀nonneg.trans_lt hs
  have hdeadline' :
      (legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
          (legacyConstants S).stableGrowthDelay gap ≤ rho.horizon := by
    simpa [stableInclusionDelay, legacyConstants, ourConstants, add_assoc] using hdeadline
  have hconfirmedHorizon :
      (legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay ≤ rho.horizon := by
    exact (le_add_of_nonneg_right hstableDnonneg).trans hdeadline'
  obtain ⟨B, hB, _hBin⟩ := available_confirmedIncluded S rho t₀
    hsleep hrecovered s hs hprop hconfirmedHorizon
  have hspos : 0 < s := positive_slot_of_positive_proposal_time S hproposalPos
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    simpa [legacyConstants, ourConstants] using hconfirmedHorizon
  have hread := honestProposalReadSafety_of_available S hsleep hrecovered
    hspos (by simpa [legacyInterface] using hs) hconfHor hprop
  obtain ⟨B', hB'after, _hB'strict, hB'In⟩ :=
    hstable ((legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay)
      (hs.le.trans (le_add_of_nonneg_right hconfirmationDnonneg))
      hdeadline'
  obtain ⟨s', hs't₁, hB'prop⟩ := hB'after
  rcases hB'prop with ⟨hprop', hB'⟩
  have hadm : AdmissibleCore S rho :=
    AdmissibleCore.ofParts hsleep.execution hsleep.synchrony
  have htfNonneg : 0 ≤
      (legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
        (legacyConstants S).stableGrowthDelay gap := by
    exact add_nonneg
      (add_nonneg (by simpa [legacyInterface] using
        (Proofs.Optimistic.proposal_time_nonneg S.E s)) hconfirmationDnonneg)
      hstableDnonneg
  have hB'pre : Block.Preceq B'.erase
      (stableOutputAt S rho (S.E.proposer s)
        ((legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
          (legacyConstants S).stableGrowthDelay gap)) := by
    change Block.Preceq B'.erase
      (readAt S rho (legacyInterface S).stable (S.E.proposer s)
        ((legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
          (legacyConstants S).stableGrowthDelay gap))
    exact hB'In (S.E.proposer s) hprop
  have hstableMem := stable_output_mem_storeAt S rho (S.E.proposer s)
    ((legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
      (legacyConstants S).stableGrowthDelay gap)
  rw [storeAt_eq_storeBeforeTime_succ S rho (S.E.proposer s)
    ((legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
      (legacyConstants S).stableGrowthDelay gap)] at hstableMem
  have hB'MemBefore := Proofs.NamedSlotFreshness.ancestor_mem_storeBeforeTime S hadm
    hstableMem hB'pre
  have hB'Mem : B'.erase ∈
      (rho.storeAt S (S.E.proposer s)
        ((legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
          (legacyConstants S).stableGrowthDelay gap)).T := by
    rw [storeAt_eq_storeBeforeTime_succ S rho (S.E.proposer s)
      ((legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
        (legacyConstants S).stableGrowthDelay gap)]
    exact hB'MemBefore
  have hB'time := proposal_time_le_of_mem_storeAt S hadm htfNonneg hB'Mem
  have hB'slot : B'.erase.slot = s' := by
    rw [Proofs.NamedWire.erase_slot]
    exact DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s' hB'
  have hs'hor : Protocol.proposal_time S.E s' ≤ rho.horizon := by
    have hle : Protocol.proposal_time S.E s' ≤
        (legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
          (legacyConstants S).stableGrowthDelay gap := by
      simpa [hB'slot] using hB'time
    exact hle.trans hdeadline'
  have htime : Protocol.proposal_time S.E s ≤
      Protocol.proposal_time S.E s' := by
    exact (le_add_of_nonneg_right hconfirmationDnonneg).trans_lt hs't₁ |>.le
  have hsle : s ≤ s' := by
    have hslot := Protocol.slot_le_slotOf_of_proposal_time_le S.E htime
    simpa only [Proofs.Optimistic.slotOf_proposal_time] using hslot
  have hslt : s < s' := by
    by_contra hnot
    have hs'le : s' ≤ s := Nat.le_of_not_gt hnot
    exact (not_lt_of_ge (Protocol.proposal_time_mono S.E hs'le))
      (le_add_of_nonneg_right hconfirmationDnonneg |>.trans_lt hs't₁)
  have hparent : Block.Preceq B.erase (Proofs.HealingSurface.proposedParent S rho s') := by
    simpa only [proposerHeadAt] using
      hread.proposal B hB.2 s' hslt hs'hor hprop'
  have hparentB' : Block.Preceq (Proofs.HealingSurface.proposedParent S rho s') B'.erase := by
    calc
      Proofs.HealingSurface.proposedParent S rho s' = B'.erase.parent :=
        (Proofs.HealingSurface.proposedBlockErased_parent S rho s' hB').symm
      _ ⪯ B'.erase := preceq_parent B'.erase
  have hBB' : Block.Preceq B.erase B'.erase :=
    Block.preceq_trans hparent hparentB'
  refine ⟨B, hB, ?_⟩
  intro v hv
  have hB'InAt : Block.Preceq B'.erase
      (readAt S rho (legacyInterface S).stable v
        ((legacyInterface S).proposalTime s + (legacyConstants S).confirmationDelay +
          (legacyConstants S).stableGrowthDelay gap)) := hB'In v hv
  simpa [stableInclusionDelay, legacyConstants, ourConstants, add_assoc] using
    Block.preceq_trans hBB' hB'InAt

end Proofs
end DecoupledConsensusModel

end
