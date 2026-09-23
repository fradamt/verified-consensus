module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.HeightRegimeNamedRunSuccessor

@[expose] public section

/-!
# Run-scoped named regimes above a base
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A top crossing supplies all intermediate crossings in the named
execution. -/
private theorem exists_crossings_below_top_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {first : Nat} {blocked : Height}
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    {n f : Nat} (hf : FirstHeightProgressAt S rho (blocked + n + 1) f) :
    ∀ m : Nat, 1 ≤ m → m ≤ n →
      ∃ f' : Nat, FirstHeightProgressAt S rho (blocked + m + 1) f' := by
  intro m hm1 hmn
  have hfirstLe : first ≤ f := by
    by_contra hn
    have hlt : f < first := Nat.lt_of_not_le hn
    have h1 := hfirst.before f hlt
    rw [hf.frontier] at h1
    exact absurd h1 (Nat.not_le.mpr
      (Nat.succ_lt_succ
        (Nat.lt_succ_of_le (Nat.le_add_right blocked n))))
  rcases eq_or_lt_of_le hmn with heq | hlt
  · exact ⟨f, heq ▸ hf⟩
  · obtain ⟨f', hff', -, hbefore', hfront⟩ :=
      exists_least_honestHMaxBeforeIndex_crossing S
        adm.toNamedDeliveryWellFormed hfirstLe
        (H := blocked + m + 1)
        (by rw [hfirst.frontier]
            exact Nat.succ_le_succ (Nat.add_le_add_left hm1 blocked))
        (by rw [hf.frontier]
            exact Nat.succ_lt_succ
              (Nat.lt_succ_of_lt (Nat.add_lt_add_left hlt blocked)))
    refine ⟨f', ⟨hfirst.positive.trans hff', hfront, ?_⟩⟩
    intro i hi
    by_cases hif : i < first
    · exact (hfirst.before i hif).trans
        (Nat.succ_le_succ (Nat.le_add_right blocked m))
    · exact hbefore' i (Nat.le_of_not_lt hif) hi

namespace NamedHeightRegimeBaseRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first : Nat} {Tprev : NamedBlock V}

/-- Every crossed height above a run-scoped named base has a regime. -/
theorem exists_regime_above_named
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat)
    (hcross : ∀ m : Nat, 1 ≤ m → m ≤ n →
      ∃ f : Nat, FirstHeightProgressAt S rho (blocked + m + 1) f) :
    ∃ (first_n i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T Tprev' : NamedBlock V) (c0 : Round),
      NamedHeightRegimeRun S rho r0 (blocked + n) first_n i a ta
        Cfg T Tprev' c0 := by
  induction n with
  | zero =>
      obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
        h.exists_regime_closed adm hbelow hgst
      exact ⟨first, i, a, ta, Cfg, T, Tprev, a.round, hreg⟩
  | succ n ih =>
      obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
        ih (fun m hm1 hmn => hcross m hm1 (hmn.trans (Nat.le_succ n)))
      obtain ⟨f, hf⟩ :=
        hcross (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (le_refl _)
      have hf' : FirstHeightProgressAt S rho
          (blocked + n + 1 + 1) f := hf
      obtain ⟨i', a', ta', Cfg', T', h', -, -⟩ :=
        hreg.succ_named adm hcom hbelow hgst
          (h.start.trans_le (Nat.le_add_right blocked n))
          (h.positive.trans (Nat.le_add_right blocked n)) hf'
      exact ⟨f, i', a', ta', Cfg', T', T, a.round + 1, h'⟩

#print axioms NamedHeightRegimeBaseRun.exists_regime_above_named

/-- An actual honest row supplies the run-scoped regime at its height, even
when the run never crosses above that height. -/
theorem exists_regime_of_row_named
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1)) :
    ∃ (first_n i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T Tprev' : NamedBlock V) (c0 : Round),
      NamedHeightRegimeRun S rho r0 (blocked + n) first_n i a ta
        Cfg T Tprev' c0 := by
  classical
  by_cases hcross : ∃ f : Nat,
      FirstHeightProgressAt S rho (blocked + n + 1) f
  · obtain ⟨f, hf⟩ := hcross
    obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
      h.exists_regime_above_named adm hcom hbelow hgst n
        (exists_crossings_below_top_named S adm h.crossing hf)
    exact ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩
  · have hnever : ∀ j : Nat,
        honestHMaxBeforeIndex S rho j ≤ blocked + n + 1 := by
      intro j
      by_contra hn
      obtain ⟨f, _, hf⟩ := exists_firstHeightProgressAt S
        adm.toNamedDeliveryWellFormed
        (Nat.succ_le_succ (Nat.zero_le _)) (Nat.lt_of_not_le hn)
      exact hcross ⟨f, hf⟩
    cases n with
    | zero =>
        exfalso
        have h1 := hnever first
        rw [h.crossing.frontier] at h1
        exact Nat.not_succ_le_self _ h1
    | succ n =>
        obtain ⟨j, hj, hout⟩ := hemit
        have hfront : blocked + n + 1 + 1 ≤
            honestHMaxBeforeIndex S rho (j + 1) :=
          honestEmittedHeight_le_honestHMaxBeforeIndex
            S adm hb hj hout (Nat.lt_succ_self j) hrow
        have hcrossings : ∀ m : Nat, 1 ≤ m → m ≤ n →
            ∃ f : Nat,
              FirstHeightProgressAt S rho (blocked + m + 1) f := by
          intro m _ hmn
          obtain ⟨f, _, hf⟩ := exists_firstHeightProgressAt S
            adm.toNamedDeliveryWellFormed
            (H := blocked + m + 1)
            (Nat.succ_le_succ (Nat.zero_le _))
            (lt_of_lt_of_le (Nat.succ_lt_succ (Nat.lt_succ_of_le
              (Nat.add_le_add_left hmn blocked))) hfront)
          exact ⟨f, hf⟩
        obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
          h.exists_regime_above_named adm hcom hbelow hgst n hcrossings
        obtain ⟨i', a', ta', Cfg', T', h', _, _⟩ :=
          hreg.succ_uncrossed_named adm hcom hbelow hgst
            (h.start.trans_le (Nat.le_add_right blocked n))
            (h.positive.trans (Nat.le_add_right blocked n))
            hnever hb ⟨j, hj, hout⟩ hrow
        exact ⟨_, i', a', ta', Cfg', T', T, _, h'⟩

#print axioms NamedHeightRegimeBaseRun.exists_regime_of_row_named

end NamedHeightRegimeBaseRun

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
