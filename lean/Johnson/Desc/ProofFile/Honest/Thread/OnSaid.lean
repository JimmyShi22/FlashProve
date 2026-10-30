-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/OnSaid.lean: the hypothesis of Honest/Thread/OnFrom.lean over
`ThrS`, the invariant together with `Said` (Honest/Thread/Said.lean): a list's condition at a part's
entry (the parameter On of `Good`, Honest/Side.lean) may speak of what the rounds before have shown
in the clear: a simulator is given these rounds themselves: so the invariant alone cannot prove it.
Definitions, meant as hypotheses; and conditional lemmas on them. General in the parameters: no kind
is named.

  1  `InsideS`, `insideS_zero`, `insideS_front`, `inside_of_insideS`   inside a sub-protocol, at
     `ThrS`
  2  `OnFromS`, `onFromS_of_onFrom`   On follows from `ThrS`
  3  `insideS_mono`, `onFromS_mono`   from one's own clause to the chain's whole `Said`

Met trivially: as the head of Honest/Thread/OnFrom.lean says of `OnFrom`, and that of
Honest/Thread/Said.lean of `Said`. Where the part's simulator reads nothing of `front`: On := True:
the hypothesis holds trivially, and whatever clause of `Said` would have served it is not needed.
`TrueTo` is a hypothesis inside it: that the `front` which a run's rounds as produced give is true
to these rounds is proved at one len, `depthAt F` (Honest/Law/Rule/TrueLaid.lean: `trueTo_one`,
`trueTo_two`, `trueTo_three`).

Limits.
  * It is not proved that the hypothesis can be met.
  * None is one of the library's goals.
  * `insideS_zero` also takes "`chainSteps` … [blk] T.hs = .ok l": the book gives the sub-protocol's
    `Step`s their coins.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.OnFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-! ## 1 Inside a sub-protocol, over `ThrS` -/

/-- **The state of a run after the first n rounds of sub-protocol number b**, reached from a state
at which `ThrS` holds at the border before the sub-protocol: `Inside` (Honest/Thread/Pays.lean) with
`Said` at that same state. It is a definition, meant as a hypothesis. -/
def InsideS (b n : Nat) (k : Coins Bk) (m : Mid W X) (E : Env) : Prop :=
  ∃ blk s m₀ E₀ l ds y, T.bs[b]? = some blk ∧ Thr T b k s m₀ E₀ ∧ Said b k m₀ ∧
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m₀.st.input) [blk] T.hs = .ok l ∧
    drawsFit (blk.rounds.take n) ds = true ∧ play (l.take n) ds [] m₀ = .ok y ∧ m = y.2 ∧
    E = E₀.add y.1

theorem inside_of_insideS {b n : Nat} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : InsideS T Said b n k m E) : Inside T b n k m E := by
  unfold InsideS at h
  obtain ⟨blk, s, m₀, E₀, l, ds, y, h1, h2, -, h4, h5, h6, h7, h8⟩ := h
  unfold Inside
  exact ⟨blk, s, m₀, E₀, l, ds, y, h1, h2, h4, h5, h6, h7, h8⟩

/-- At the border before the sub-protocol: from `ThrS` there. -/
theorem insideS_zero {b : Nat} {blk : Block S Cl} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    {l : List (Step W X)} (hblk : T.bs[b]? = some blk) (hA : ThrS T Said b k s m E)
    (hl : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok l) : ∃ E', InsideS T Said b 0 k m E' := by
  obtain ⟨hT, hs₀⟩ := hA
  unfold InsideS
  exact ⟨_, blk, s, m, E, l, [], ([], m), hblk, hT, hs₀, hl, rfl, rfl, rfl, rfl⟩

/-- **Before the sub-protocol's first round the state is the one at the border**: so `Said` holds at
it. -/
theorem insideS_front {b : Nat} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : InsideS T Said b 0 k m E) : Said b k m := by
  unfold InsideS at h
  obtain ⟨blk, s, m₀, E₀, l, ds, y, -, -, hs₀, -, hd, hy, rfl, -⟩ := h
  have hd0 : ds = [] := by
    have e := drawsFit_length _ _ hd
    rw [List.take_zero] at e
    exact List.eq_nil_of_length_eq_zero e
  subst hd0
  rw [List.take_zero] at hy
  have ey : (([], m₀) : List Played × Mid W X) = y := Except.ok.inj hy
  rw [← ey]
  exact hs₀

/-! ## 2 On follows from `ThrS` -/

/-- **On follows from the invariant and `Said`**: `OnFrom` (Honest/Thread/OnFrom.lean) with
`InsideS` in the place of `Inside`. It is a definition, meant as a hypothesis. Nothing is claimed of
it, and it is none of the library's goals. -/
def OnFromS (L : Lettered Bk S Cl V W X Pb) (b : Nat) (len : Nat → Nat → Nat) : Prop :=
  ∀ σ, L.side T.bs = some σ → ∀ u ∈ σ.members, ∀ k m E ca front,
    InsideS T Said b (σ.off u.number) k m E →
    carriedAt Bk k T.chain ⟨L.place, u.number⟩ u.part = .ok ca →
    TrueTo T.chain len front m.seen E → L.On u ca m front

/-- What follows from the invariant alone follows from `ThrS`. -/
theorem onFromS_of_onFrom {L : Lettered Bk S Cl V W X Pb} {b : Nat} {len : Nat → Nat → Nat}
    (h : OnFrom T L b len) : OnFromS T Said L b len := fun σ hσ u hu k m E ca front hI hca hT =>
  h σ hσ u hu k m E ca front (inside_of_insideS T Said hI) hca hT

/-! ## 3 From one's own clause to the chain's whole `Said` -/

/-- A `Said` that says more reaches fewer states. -/
theorem insideS_mono {Said' : Nat → Coins Bk → Mid W X → Prop}
    (hS : ∀ b k m, Said' b k m → Said b k m) {b n : Nat} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : InsideS T Said' b n k m E) : InsideS T Said b n k m E := by
  unfold InsideS at h
  obtain ⟨blk, s, m₀, E₀, l, ds, y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold InsideS
  exact ⟨blk, s, m₀, E₀, l, ds, y, h1, h2, hS _ _ _ h3, h4, h5, h6, h7, h8⟩

/-- **The hypothesis, proved at one's own clause, holds at every `Said` that says at least that
clause**: so at the chain's whole `Said`, the conjunction of all kinds' clauses. -/
theorem onFromS_mono {Said' : Nat → Coins Bk → Mid W X → Prop}
    (hS : ∀ b k m, Said' b k m → Said b k m) {L : Lettered Bk S Cl V W X Pb} {b : Nat}
    {len : Nat → Nat → Nat} (h : OnFromS T Said L b len) : OnFromS T Said' L b len :=
  fun σ hσ u hu k m E ca front hI hca hT =>
    h σ hσ u hu k m E ca front (insideS_mono T Said hS hI) hca hT

end ProofFile.Honest

#print axioms ProofFile.Honest.inside_of_insideS
#print axioms ProofFile.Honest.insideS_zero
#print axioms ProofFile.Honest.insideS_front
#print axioms ProofFile.Honest.onFromS_of_onFrom
#print axioms ProofFile.Honest.insideS_mono
#print axioms ProofFile.Honest.onFromS_mono
