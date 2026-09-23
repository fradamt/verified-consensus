module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ModelVocabulary.Execution.GradeRuntime.Transport
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
Cap-aware generic grade transport.
The public theorem surface contains the two transport queries.
-/
namespace DecoupledConsensusModel.Protocol

variable {Key Block : Type*}

section Weights

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem weight_mono (w : V → Nat) {s t : Finset V} (h : s ⊆ t) :
    weight w s ≤ weight w t := Finset.sum_le_sum_of_subset h

end Weights

private theorem clean_excludes_equivocation {raw : Finset (Token Key)} {k j : Nat}
    (hclean : CleanFrom raw k) (hkj : k ≤ j) : ¬ EquivocationAt raw j := by
  rintro ⟨x, hx, y, hy, hxj, hyj, hne⟩
  apply hne
  exact hclean x hx y hy (by simpa only [hxj] using hkj) (hxj.trans hyj.symm)

/-- Transport of each raw vote or a same-round cap witness also transports
any raw equivocation pair. Exact raw-set inclusion is unnecessary. -/
theorem equivocation_back_of_vote_or_equivocation
    {sr tr : Finset (Token Key)}
    (hBack : ∀ x ∈ tr, x ∈ sr ∨ EquivocationAt sr x.round)
    {k : Nat} (h : EquivocationAt tr k) : EquivocationAt sr k := by
  obtain ⟨x, hx, y, hy, hxk, hyk, hne⟩ := h
  rcases hBack x hx with hxS | hxEq
  · rcases hBack y hy with hyS | hyEq
    · exact ⟨x, hxS, y, hyS, hxk, hyk, hne⟩
    · simpa only [hyk] using hyEq
  · simpa only [hxk] using hxEq

/-- Supporting input transport through the actual two-head cap. Only early
covering heads must transfer; late inputs may return as raw equivocation. -/
private theorem supports_transport_with_cap
    (covers : Key → Block → Prop)
    {se sl sr te tl tr : Finset (Token Key)} {B : Block}
    (hSourceLate : se ⊆ sl) (hSourceRaw : sl ⊆ sr)
    (hTargetLate : te ⊆ tl)
    (hForward : ∀ u ∈ se, covers u.key B → u ∈ te ∨ EquivocationAt tr u.round)
    (hLateBack : ∀ x ∈ tl, x ∈ sl ∨ EquivocationAt sr x.round)
    (hEqBack : ∀ k, EquivocationAt tr k → EquivocationAt sr k)
    (h : Supports covers se sl sr B) : Supports covers te tl tr B := by
  obtain ⟨u, hu, _, hcover, hclean, hsweep⟩ := h
  have huT : u ∈ te := by
    rcases hForward u hu hcover with h | h
    · exact h
    · exact False.elim (clean_excludes_equivocation hclean le_rfl (hEqBack _ h))
  obtain ⟨v, hv, hmax⟩ := te.exists_max_image Token.round ⟨u, huT⟩
  have huv : u.round ≤ v.round := hmax u huT
  have hvS : v ∈ sl := by
    rcases hLateBack v (hTargetLate hv) with h | h
    · exact h
    · exact False.elim (clean_excludes_equivocation hclean huv h)
  have hvCover : covers v.key B := by
    by_cases heq : u.round = v.round
    · have hkey := hclean u (hSourceRaw (hSourceLate hu)) v
        (hSourceRaw hvS) le_rfl heq
      simpa only [← hkey] using hcover
    · exact hsweep v hvS (Nat.lt_of_le_of_ne huv heq)
  refine ⟨v, hv, hmax, hvCover, ?_, ?_⟩
  · intro x hx y hy hk hxy
    by_contra hne
    exact clean_excludes_equivocation hclean (huv.trans hk)
      (hEqBack _ ⟨x, hx, y, hy, rfl, hxy.symm, hne⟩)
  · intro x hx hvx
    rcases hLateBack x hx with hxS | hxEq
    · exact hsweep x hxS (lt_of_le_of_lt huv hvx)
    · exact False.elim (clean_excludes_equivocation hclean
        (huv.trans (le_of_lt hvx)) hxEq)

private theorem equivocation_opposes_of_round_bound
    (covers : Key → Block → Prop)
    {early late raw : Finset (Token Key)} {B : Block} {k : Nat}
    (hBound : ∀ u ∈ early, u.round ≤ k) (hEq : EquivocationAt raw k) :
    Opposes covers early late raw B := by
  obtain ⟨x, hx, y, hy, hxk, hyk, hne⟩ := hEq
  exact Or.inr ⟨x, hx, y, hy, fun u hu => by simpa only [hxk] using hBound u hu,
    hxk.trans hyk.symm, hne⟩

/-- Opposition returns through vote-or-equivocation transport, including
when finality projection removes non-covering source early heads. -/
private theorem opposition_back_with_cap
    (covers : Key → Block → Prop)
    {se sl sr te tl tr : Finset (Token Key)} {B : Block}
    (hSourceLate : se ⊆ sl)
    (hForward : ∀ u ∈ se, covers u.key B → u ∈ te ∨ EquivocationAt tr u.round)
    (hLateBack : ∀ x ∈ tl, x ∈ sl ∨ EquivocationAt sr x.round)
    (hEqBack : ∀ k, EquivocationAt tr k → EquivocationAt sr k)
    (h : Opposes covers te tl tr B) : Opposes covers se sl sr B := by
  by_cases hs : Opposes covers se sl sr B
  · exact hs
  · have hRound : ∀ k, (∀ u ∈ te, u.round ≤ k) → ∀ u ∈ se, u.round ≤ k := by
      intro k hk u hu
      obtain ⟨v, hv, hmax⟩ := se.exists_max_image Token.round ⟨u, hu⟩
      have hcover : covers v.key B := by
        by_contra hnot
        exact hs (Or.inl ⟨v, hSourceLate hv, hmax, hnot⟩)
      rcases hForward v hv hcover with hvT | hvEq
      · exact (hmax u hu).trans (hk v hvT)
      · exact False.elim (hs (equivocation_opposes_of_round_bound covers
          hmax (hEqBack _ hvEq)))
    rcases h with ⟨x, hx, hmax, hnot⟩ | ⟨x, hx, y, hy, hmax, hxy, hne⟩
    · rcases hLateBack x hx with hxS | hxEq
      · exact Or.inl ⟨x, hxS, hRound _ hmax, hnot⟩
      · exact equivocation_opposes_of_round_bound covers (hRound _ hmax) hxEq
    · exact equivocation_opposes_of_round_bound covers (hRound _ hmax)
        (hEqBack _ ⟨x, hx, y, hy, rfl, hxy.symm, hne⟩)

/-- The weighted grade keeps its strict margin through the cap-aware hop. -/
theorem grade_transport_with_cap
    {V : Type*} [Fintype V] (w : V → Nat) (covers : Key → Block → Prop)
    {se sl sr te tl tr : V → Finset (Token Key)} {B : Block}
    (hSourceLate : ∀ v, se v ⊆ sl v) (hSourceRaw : ∀ v, sl v ⊆ sr v)
    (hTargetLate : ∀ v, te v ⊆ tl v)
    (hForward : ∀ v u, u ∈ se v → covers u.key B →
      u ∈ te v ∨ EquivocationAt (tr v) u.round)
    (hLateBack : ∀ v x, x ∈ tl v → x ∈ sl v ∨ EquivocationAt (sr v) x.round)
    (hEqBack : ∀ v k, EquivocationAt (tr v) k → EquivocationAt (sr v) k)
    (h : grade w covers se sl sr B) : grade w covers te tl tr B := by
  classical
  have hp : coverSupporters covers se sl sr B ⊆ coverSupporters covers te tl tr B := by
    intro v hv
    simp only [coverSupporters, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact supports_transport_with_cap covers (hSourceLate v) (hSourceRaw v)
      (hTargetLate v) (hForward v) (hLateBack v) (hEqBack v) hv
  have hn : opponents covers te tl tr B ⊆ opponents covers se sl sr B := by
    intro v hv
    simp only [opponents, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact opposition_back_with_cap covers (hSourceLate v) (hForward v)
      (hLateBack v) (hEqBack v) hv
  exact lt_of_le_of_lt (weight_mono w hn) (lt_of_lt_of_le h (weight_mono w hp))

end DecoupledConsensusModel.Protocol

end
