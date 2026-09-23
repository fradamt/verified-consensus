module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.ConfirmedOutput
public import DecoupledConsensusInternal.WholeRunFinalitySafety
public import DecoupledConsensusInternal.Definitions.StableOutput
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone
public import DecoupledConsensusProofs.Execution.StoreFinalityRun

@[expose] public section

/-! # Finality-aware confirmed-output properties -/

namespace DecoupledConsensusModel
namespace Proofs
namespace ConfirmedOutput

open Internal Execution

variable {V : Type} [DecidableEq V]

/-- Prefix inclusion holds even for an arbitrary store. -/
theorem finalized_preceq_get_confirmed (st : Protocol.Store V) :
    Block.Preceq st.F (Protocol.get_confirmed st) := by
  -- The two accessor steps of the nested chains, each by its own branch:
  -- finality reaches the stable output, and the stable output reaches the
  -- confirmed output.
  have hstable : Block.Preceq st.F (Protocol.get_stable st) := by
    unfold Protocol.get_stable
    split
    · assumption
    · exact Block.preceq_self _
  have hconf : Block.Preceq (Protocol.get_stable st) (Protocol.get_confirmed st) := by
    unfold Protocol.get_confirmed
    split
    · assumption
    · exact Block.preceq_self _
  exact Block.preceq_trans hstable hconf

/-- The stable output stays below the confirmation record when the stable record
does and finality does. The `Protocol.StableBelowConfirmed` premise is a regime
fact, not a run invariant of `update_confirmation_with`: an eligible Goldfish
head can replace a conflicting confirmation record while the stable record keeps
an ancestor on the previous branch. A follow-up statement discharges it under the
safety regime, from SG-root canonicity of honest Goldfish heads. -/
theorem get_stable_preceq_latest (st : Protocol.Store V)
    (hs : Protocol.StableBelowConfirmed st) (h : Block.Preceq st.F st.latest_confirmed) :
    Block.Preceq (Protocol.get_stable st) st.latest_confirmed := by
  unfold Protocol.get_stable
  split
  · exact hs
  · exact h

/-- A stable output that does not reach the confirmation record is finality
itself: the stored stable record would reach it, by the regime fact. -/
theorem get_stable_eq_finalized_of_not_preceq (st : Protocol.Store V)
    (hs : Protocol.StableBelowConfirmed st)
    (hnot : Block.preceq (Protocol.get_stable st) st.latest_confirmed ≠ true) :
    Protocol.get_stable st = st.F := by
  by_cases hfs : Block.preceq st.F st.latest_stable = true
  · refine absurd ?_ hnot
    unfold Protocol.get_stable
    rw [if_pos hfs]
    exact hs
  · unfold Protocol.get_stable
    exact if_neg hfs

/-- A current record that already extends finality is returned unchanged. The
stable output must also stay below it, which is the regime fact
`Protocol.StableBelowConfirmed`: it is not a run invariant of
`update_confirmation_with`, because an eligible Goldfish head can replace a
conflicting confirmation record while the stable record keeps an ancestor on the
old branch. A follow-up statement discharges it under the safety regime, from
SG-root canonicity of honest Goldfish heads. -/
theorem get_confirmed_eq_latest (st : Protocol.Store V)
    (hs : Protocol.StableBelowConfirmed st)
    (h : Block.Preceq st.F st.latest_confirmed) :
    Protocol.get_confirmed st = st.latest_confirmed := by
  unfold Protocol.get_confirmed
  exact if_pos (get_stable_preceq_latest st hs h)



/-- Any common upper bound of the stored record and finality also bounds the
output. The stable output is bounded through the confirmation record, by the
regime fact `Protocol.StableBelowConfirmed`. It is not a run invariant of
`update_confirmation_with`, because an eligible Goldfish head can replace a
conflicting confirmation record while the stable record keeps an ancestor on the
old branch. A follow-up statement discharges it under the safety regime, from
SG-root canonicity of honest Goldfish heads. -/
theorem get_confirmed_preceq (st : Protocol.Store V) {B : Block V}
    (hs : Protocol.StableBelowConfirmed st)
    (hF : Block.Preceq st.F B) (hL : Block.Preceq st.latest_confirmed B) :
    Block.Preceq (Protocol.get_confirmed st) B := by
  unfold Protocol.get_confirmed
  split
  · exact hL
  · unfold Protocol.get_stable
    split
    · exact Block.preceq_trans hs hL
    · exact hF

/-- A protected prefix of the raw record remains exposed when compatible with
finality. The stable output can only hide the record when the stable record
leaves it, which the regime fact `Protocol.StableBelowConfirmed` excludes. It is
not a run invariant of `update_confirmation_with`, because an eligible Goldfish
head can replace a conflicting confirmation record while the stable record keeps
an ancestor on the previous branch. A follow-up statement discharges it under the
safety regime, from SG-root canonicity of honest Goldfish heads. -/
theorem preceq_get_confirmed_of_latest (st : Protocol.Store V) {B : Block V}
    (hs : Protocol.StableBelowConfirmed st)
    (hL : Block.Preceq B st.latest_confirmed) (hF : Block.compatible B st.F = true) :
    Block.Preceq B (Protocol.get_confirmed st) := by
  unfold Protocol.get_confirmed
  split
  · exact hL
  · rename_i hnot
    simp only [Block.compatible, Bool.or_eq_true] at hF
    rcases hF with h | h
    · rw [get_stable_eq_finalized_of_not_preceq st hs hnot]
      exact h
    · exact False.elim (hnot (get_stable_preceq_latest st hs (Block.preceq_trans h hL)))

/-- Exposed output is monotone when both fields advance and the previous record
is compatible with the new finality. This compatibility is not unconditional.
Both reads also need the regime fact `Protocol.StableBelowConfirmed`: at the previous
store it puts the previous stable output at finality in the lagging branch, and at
the new store it keeps the new stable output from hiding the new record. It is
not a run invariant of `update_confirmation_with`, because an eligible Goldfish
head can replace a conflicting confirmation record while the stable record keeps
an ancestor on the previous branch. A follow-up statement discharges it under the
safety regime, from SG-root canonicity of honest Goldfish heads. -/
theorem get_confirmed_mono (old new : Protocol.Store V)
    (hsold : Protocol.StableBelowConfirmed old)
    (hsnew : Protocol.StableBelowConfirmed new)
    (hF : Block.Preceq old.F new.F)
    (hL : Block.Preceq old.latest_confirmed new.latest_confirmed)
    (hcross : Block.compatible old.latest_confirmed new.F = true) :
    Block.Preceq (Protocol.get_confirmed old) (Protocol.get_confirmed new) := by
  unfold Protocol.get_confirmed at ⊢
  split
  · exact preceq_get_confirmed_of_latest new hsnew hL hcross
  · rename_i hnot
    rw [get_stable_eq_finalized_of_not_preceq old hsold hnot]
    exact Block.preceq_trans hF (finalized_preceq_get_confirmed new)

/-! ## The stable output

`get_stable` selects the stable record or finality. Its guarantees therefore
rest on the stable record's own canonicity, not on the record nesting. -/







variable [Fintype V]


/-- Transfer agreement to the exposed output once the regime supplies
compatibility between finality and historical confirmation records. -/
theorem confirmedOutputCompatibleFrom_of_fields
    (S : Setup V) {rho : Run V} {t0 : Time}
    (hfinality : WholeRunFinalitySafety S rho)
    (hlatest : ConfirmationCompatibleFrom S rho t0)
    (hstable : ∀ w ∈ rho.honest, ∀ s, t0 ≤ s → s ≤ rho.horizon →
      Protocol.StableBelowConfirmed (rho.storeAt S w s).core)
    (hcross : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t0 ≤ t' →
      t ≤ rho.horizon → t' ≤ rho.horizon →
      Block.compatible (rho.storeAt S u t).F (rho.storeAt S v t').latest_confirmed = true) :
    ConfirmedOutputCompatibleFrom S rho t0 := by
  intro u hu v hv t t' ht ht' hhor hhor'
  unfold confirmedOutputAt Protocol.get_confirmed
  split <;> split
  · exact hlatest u hu v hv t t' ht ht' hhor hhor'
  · rename_i hnb
    rw [get_stable_eq_finalized_of_not_preceq _ (hstable v hv t' ht' hhor') hnb]
    simpa only [Block.compatible, Bool.or_comm] using
      hcross v hv u hu t' t ht' ht hhor' hhor
  · rename_i hna _
    rw [get_stable_eq_finalized_of_not_preceq _ (hstable u hu t ht hhor) hna]
    exact hcross u hu v hv t t' ht ht' hhor hhor'
  · rename_i hna hnb
    rw [get_stable_eq_finalized_of_not_preceq _ (hstable u hu t ht hhor) hna,
      get_stable_eq_finalized_of_not_preceq _ (hstable v hv t' ht' hhor') hnb]
    exact hfinality.2 u hu v hv t t'

/-- Transfer monotonicity when the previous record remains compatible with later
finality. A stale conflicting record can otherwise be replaced in the output. -/
theorem confirmedOutputMonotoneFrom_of_cross
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) {t0 : Time}
    (hlatest : ConfirmationMonotoneFrom S rho t0)
    (hstable : ∀ w ∈ rho.honest, ∀ s, t0 ≤ s → s ≤ rho.horizon →
      Protocol.StableBelowConfirmed (rho.storeAt S w s).core)
    (hcross : ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t ≤ t' → t' ≤ rho.horizon →
      Block.compatible (rho.storeAt S v t).latest_confirmed (rho.storeAt S v t').F = true) :
    ConfirmedOutputMonotoneFrom S rho t0 := by
  intro v hv t t' ht htt' hhor
  exact get_confirmed_mono _ _ (hstable v hv t ht (le_trans htt' hhor))
    (hstable v hv t' (le_trans ht htt') hhor)
    (StoreFinality.stateAt_F_mono S sch v htt')
    (hlatest v hv t t' ht htt' hhor) (hcross v hv t t' ht htt' hhor)




end ConfirmedOutput
end Proofs
end DecoupledConsensusModel

end
