import DecoupledConsensus.Store.Proof.Conditional

namespace DecoupledConsensus

/-! # Store Proofs: certified store layer

This module is proof-side only.  It keeps the executable model and all public
store operations in terms of `Store`, while allowing Section 3 proofs to carry
the certificate/history data that is not part of protocol state.

A certified step does not redefine `Store.onBlock`: it is valid exactly when
the underlying executable store step is valid and the target store is equipped
with the requested certification.
-/

variable {n : ℕ}

open scoped Block

namespace Store

/-- The finalized root has certificate-level evidence, except for genesis,
    which is finalized by convention at height 0. -/
def CertifiedFinalizedRoot (S : Store n) : Prop :=
  S.F = Block.genesis ∨ ∃ h_f : ℕ, Nonempty (FinalizationRecord S.F h_f)

/-- Proof-side certification carried alongside an executable store.

The fields are intentionally stronger than plain `Reachable`: they record the
history/certificate obligations not recoverable from the current executable
store tuple alone. Current-root and processed-justification records are derived
from accepted entries in `History.lean`, so they are not stored here. -/
structure StoreCertification (S : Store n) : Prop where
  reachable : Reachable S
  finalized : CertifiedFinalizedRoot S
  noHigh : NoHighJustifications S

/-- A proof-side wrapper around the executable store. -/
structure CertifiedStore (n : ℕ) where
  store : Store n
  cert : StoreCertification store

lemma genesis_noHigh : NoHighJustifications (Store.genesis n) := by
  intro C h hProc
  rcases hProc with ⟨e, he, _hJ, hhj⟩
  have heq : e = StoreEntry.genesis n := by
    simpa [Store.genesis] using he
  subst e
  simp [StoreEntry.state, StoreEntry.genesis, stateOf, State.genesis] at hhj
  omega

/-- Genesis satisfies the proof-side store certification. -/
lemma genesisCertification : StoreCertification (Store.genesis n) where
  reachable := Reachable.genesis
  finalized := Or.inl rfl
  noHigh := genesis_noHigh

namespace CertifiedStore

/-- The certified genesis store. -/
def genesis (n : ℕ) : CertifiedStore n where
  store := Store.genesis n
  cert := genesisCertification

@[simp] lemma genesis_store : (genesis n).store = Store.genesis n := rfl

/-- Certified steps project exactly to executable `Store.onBlock` steps. -/
def OnBlock (Sigma SigmaPrime : CertifiedStore n) (B : Block n) : Prop :=
  Sigma.store.onBlock B = some SigmaPrime.store

/-- Certified reachability: the target of every step carries its certificate,
    while the step itself remains the executable store transition. -/
inductive Reachable : CertifiedStore n → Prop
  | genesis : Reachable (genesis n)
  | onBlock {Sigma SigmaPrime : CertifiedStore n} {B : Block n}
      (hSigma : Reachable Sigma) (hstep : Sigma.OnBlock SigmaPrime B) :
      Reachable SigmaPrime

/-- Certified reachability projects to executable store reachability. -/
theorem reachable_store {Sigma : CertifiedStore n} (hSigma : Reachable Sigma) :
    Store.Reachable Sigma.store := by
  induction hSigma with
  | genesis =>
      exact Store.Reachable.genesis
  | onBlock hPrev hstep ih =>
      exact Store.Reachable.onBlock ih hstep

/-- Certified steps are exactly executable store steps on the projection. -/
theorem onBlock_store {Sigma SigmaPrime : CertifiedStore n} {B : Block n}
    (hstep : Sigma.OnBlock SigmaPrime B) :
    Sigma.store.onBlock B = some SigmaPrime.store :=
  hstep

end CertifiedStore

/-- No-high-justification, now as a certified-store theorem rather than an
    explicit premise at the call site. -/
theorem certified_no_high_justifications {Sigma : CertifiedStore n}
    {C : Block n} {h : ℕ}
    (hProc : ProcessedJustification Sigma.store C h) :
    h ≤ Sigma.store.hj :=
  Sigma.cert.noHigh hProc

/-- Certified upgrade wrapper: a previously processed descriptor for finalized
    `F` supplies the height bound via no-high, while the target store supplies
    the current-root certificate. -/
theorem certified_upgrade_of_processed {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {Sigma T : CertifiedStore n} (hFuture : Future Sigma.store T.store)
    {F : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F h_f)
    (hProc : ProcessedJustification Sigma.store F h_f)
    (hId : rF.IdInjectiveAgainstStore T.store) :
    F ≼ T.store.J := by
  exact upgrade_of_processed hn hNoSlash
    Sigma.cert.reachable hFuture rF hProc hId Sigma.cert.noHigh

/-- Certified lock-in wrapper matching the Section 3 shape more closely than
    `lockin_of_records`: the caller gives a processed descriptor, not the
    internal current-root/processed-record/no-high plumbing. -/
theorem certified_lockin {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {Sigma T : CertifiedStore n} (hFuture : Future Sigma.store T.store)
    {F B : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F h_f)
    (hProc : ProcessedJustification Sigma.store F h_f)
    (hId : rF.IdInjectiveAgainstStore T.store)
    (hB : B ∈ T.store.getConfirmed) :
    F ≼ T.store.J ∧ T.store.isViableBool F = true ∧ F ≼ B := by
  exact lockin_of_processed hn hNoSlash
    Sigma.cert.reachable hFuture rF hProc hId Sigma.cert.noHigh hB

end Store

end DecoupledConsensus
