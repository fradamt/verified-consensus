module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransportTwoCutoff
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.ChainState.WholeRunFinalitySafety

@[expose] public section

/-!
# Committee-aware healthy-prefix safety

The first helper below packages the delivery already present in an outage
execution as the two-cutoff transport used by the relative-grade proofs. It
is useful only when the last phase domain is before the healthy-prefix cut.

The requested confirmation-chain and outage-clause producers are recorded
after this helper. The earlier GST-zero route was audited first. Its missing
healthy-prefix twin is the confirmation-selection safety fold; the existing
relative-grade lemmas consume that fold but do not produce it.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface (TwoCutoffDelivery)

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem early_g2_add_delta_eq_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 + S.E.Δ = early S.E S.hc r .g1 := by
  unfold early Phase.earlyOffset
  ring

private theorem late_g1_add_delta_eq_g2 (S : Setup V) (r : Round) :
    late S.E S.hc r .g1 + S.E.Δ = late S.E S.hc r .g2 := by
  unfold late Phase.lateOffset
  ring

private theorem early_g1_le_domain_g0 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
  have h1 := q10_early_g1_le_domain_g2 S r
  have h2 := q10_domain_g2_lt_domain_g1 S r
  have h3 : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
    unfold domain Phase.domainOffset
    exact Int.add_le_add_left
      (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _
  exact h1.trans (h2.le.trans h3)

private theorem late_g2_le_domain_g0 (S : Setup V) (r : Round) :
    late S.E S.hc r .g2 ≤ domain S.E S.hc r .g0 := by
  rw [q10_late_g2_eq_domain_g2]
  exact (q10_domain_g2_lt_domain_g1 S r).le.trans
    (by
      unfold domain Phase.domainOffset
      exact Int.add_le_add_left
        (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _)

/-- Healthy delivery supplies the fixed G2-to-G1 and late reverse cutoffs. -/
theorem twoCutoffDelivery_of_healthyPrefix
    (S : Setup V) (rho : NamedRun V) (cap : Time)
    (healthy : NamedHealthyPrefixDelivery S rho cap)
    (hcap : domain S.E S.hc r .g0 ≤ cap) :
    TwoCutoffDelivery S rho r := by
  have hearlyCap : early S.E S.hc r .g1 ≤ cap :=
    (early_g1_le_domain_g0 S r).trans hcap
  have hlateCap : late S.E S.hc r .g2 ≤ cap :=
    (late_g2_le_domain_g0 S r).trans hcap
  refine ⟨?_, ?_⟩
  · intro source hsource i a t hacc htime target htarget hmissing hhor
    have hdeadline : t + S.E.Δ < early S.E S.hc r .g1 := by
      rw [← early_g2_add_delta_eq_g1 S r]
      exact Int.add_lt_add_right htime S.E.Δ
    have hsend : t + S.E.Δ ≤ cap :=
      (hdeadline.le.trans hearlyCap)
    obtain ⟨td, hlo, hhi, j, hcall⟩ := healthy.relay_attest source hsource i a t hacc
      target htarget hmissing hsend rfl
    exact ⟨td, hlo, hhi.trans hdeadline, j, hcall⟩
  · intro source hsource i a t hacc htime target htarget hmissing hhor
    have hdeadline : t + S.E.Δ < late S.E S.hc r .g2 := by
      rw [← late_g1_add_delta_eq_g2 S r]
      exact Int.add_lt_add_right htime S.E.Δ
    have hsend : t + S.E.Δ ≤ cap :=
      hdeadline.le.trans hlateCap
    obtain ⟨td, hlo, hhi, j, hcall⟩ := healthy.relay_attest source hsource i a t hacc
      target htarget hmissing hsend rfl
    exact ⟨td, hlo, hhi.trans hdeadline, j, hcall⟩

#print axioms twoCutoffDelivery_of_healthyPrefix







end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
