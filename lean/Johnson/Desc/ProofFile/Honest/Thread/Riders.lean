-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Riders.lean: the rider of a `Thread` (`Thread.rides`,
Honest/Thread/Thr.lean) as a list of clauses, each established by one sub-protocol and carried past
the others by their clauses of `keeps`. A lemma on a sub-protocol often needs a fact on the
verifier's state before it that another sub-protocol has established, and that neither the public
form nor an item says: a flag ("the head's link is open"), a count ("so many rows lie on the pile").
Such a fact is a condition on the input and the state: that is what the rider is for. Here the rider
is a conjunction of clauses: each speaks from a border `lo` to a border `hi`.

Who proves what. The sub-protocol before `lo` establishes the clause: whoever writes that
sub-protocol's prover's side proves it after the sub-protocol's own step (`LaysAt`). That the clause
still holds past a sub-protocol in between follows from that sub-protocol's clause of `keeps`
(`StaysBy`): this is proved by whoever supplies the `Thread`. So `Behind` for a sub-protocol comes
down to: the form; its clause of `keeps`; the riders that the sub-protocol itself establishes
(`behind_of_keeps`). Definitions, meant as hypotheses, and terms; and conditional lemmas. General in
the `Thread` but for section 4.

  1  `RiderCl`, `ridersOf`, `riders_at`, `riders_next`   a clause; the conjunction; one border
     further
  2  `LaysAt`, `StaysBy`   the two hypotheses for each clause
  3  `behind_of_keeps`, `behindS_of_keeps`   `Behind` from the form, `keeps` and the clauses
     established
  4  `riderHead`, `riderPile`   the first chain's two forms of clause: a fact on the head's own part
     of the state; the number of rows on the pile

The two forms of section 4. `riderHead lo hi P`: the chain is in the head's link, and P holds of the
head's own part of the state (Johnson/Desc/First/State.lean: `HeadOwn`). It is meant at P :=
"opened", "what the head's rounds heard has been set", "the tables have been set", "the claim has
been set", "the ledger has its sizes". `riderPile lo hi n`: as many rows lie on the pile as n says
at the border. It is meant at n := the number of segments cleared before.

Limits.
  * Nothing proves that a clause can be established or still holds.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

/-! ## 1 A clause; the conjunction -/

/-- **A clause of the rider**: from the border `lo` to the border `hi`, both included: a condition
on the border's number, the input and the verifier's state. -/
structure RiderCl (W S : Type) where
  lo : Nat
  hi : Nat
  prop : Nat → W → S → Prop

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The rider of a list of clauses.** -/
def ridersOf (cs : List (RiderCl W S)) (b : Nat) (w : W) (s : S) : Prop :=
  ∀ c ∈ cs, c.lo ≤ b → b ≤ c.hi → c.prop b w s

theorem riders_at {cs : List (RiderCl W S)} {b : Nat} {w : W} {s : S} (h : ridersOf cs b w s)
    {c : RiderCl W S} (hc : c ∈ cs) (hl : c.lo ≤ b) (hh : b ≤ c.hi) : c.prop b w s := h c hc hl hh

/-- One border further: each clause that spoke before still holds; each that begins here is
established. -/
theorem riders_next {cs : List (RiderCl W S)} {b : Nat} {w : W} {s s' : S}
    (h : ridersOf cs b w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → c.prop b w s → c.prop (b + 1) w s')
    (hl : ∀ c ∈ cs, c.lo = b + 1 → c.prop (b + 1) w s') : ridersOf cs (b + 1) w s' := by
  intro c hc hlo hhi
  by_cases e : c.lo = b + 1
  · exact hl c hc e
  · have hlo' : c.lo ≤ b := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hlo e)
    exact hst c hc hlo' hhi (h c hc hlo' (Nat.le_of_succ_le hhi))

/-! ## 2 The two hypotheses for each clause -/

variable (T : Thread Bk S Cl V W X Pb)

/-- **Sub-protocol number b establishes the clause**: after its own accepted step the clause holds.
It has to be proved by whoever writes that sub-protocol's prover's side. A definition, meant as a
hypothesis. -/
def LaysAt (b : Nat) (c : RiderCl W S) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    c.prop (b + 1) m.st.input s'

/-- **The clause still holds past sub-protocol number b**: from that sub-protocol's clause of
`keeps` alone. It has to be proved by whoever supplies the `Thread`. A definition, meant as a
hypothesis. -/
def StaysBy (b : Nat) (c : RiderCl W S) : Prop :=
  ∀ w s s', T.keeps b s s' → c.prop b w s → c.prop (b + 1) w s'

/-! ## 3 `Behind` from the form, `keeps` and the clauses established -/

/-- **What `Behind` for a sub-protocol comes down to.** A conditional lemma on this folder's own
definitions. It is none of the library's goals. -/
theorem behind_of_keeps {cs : List (RiderCl W S)} {b : Nat}
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hFK : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      T.Form (b + 1) k s' y.2 ∧ T.keeps b s s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  obtain ⟨hF, hK⟩ := hFK blk hblk k s m E ds y cols s' hA hd hS
  have hA' := hA
  unfold Thr at hA'
  obtain ⟨-, -, -, -, -, hR0, -⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hF, ?_, hK⟩
  rw [ei]
  exact (hr _ _ _).2 (riders_next ((hr _ _ _).1 hR0)
    (fun c hc h1 h2 h0 => hst c hc h1 h2 _ _ _ hK h0)
    fun c hc e => hl c hc e blk hblk k s m E ds y cols s' hA hd hS)

/-- The same with the form and `keeps` asked from `ThrS` (Honest/Thread/Said.lean); it ends in
`BehindS` (Honest/Thread/PaysS.lean). -/
theorem behindS_of_keeps (Said : Nat → Coins Bk → Mid W X → Prop) {cs : List (RiderCl W S)}
    {b : Nat} (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hFK : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      T.Form (b + 1) k s' y.2 ∧ T.keeps b s s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : BehindS T Said b := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  obtain ⟨hF, hK⟩ := hFK blk hblk k s m E ds y cols s' hA hd hS
  have hA' := hA.1
  unfold Thr at hA'
  obtain ⟨-, -, -, -, -, hR0, -⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hF, ?_, hK⟩
  rw [ei]
  exact (hr _ _ _).2 (riders_next ((hr _ _ _).1 hR0)
    (fun c hc h1 h2 h0 => hst c hc h1 h2 _ _ _ hK h0)
    fun c hc e => hl c hc e blk hblk k s m E ds y cols s' hA.1 hd hS)

/-! ## 4 The first chain's two forms of clause -/

/-- **A fact on the head's own part of the state**: the chain is in the head's link, and P holds of
that part. -/
def riderHead (lo hi : Nat) (P : VerifiableInference.Desc.First.HeadOwn → Prop) :
    RiderCl W VerifiableInference.Desc.First.S :=
  ⟨lo, hi, fun _ _ s => ∃ a, s.here = .head a ∧ P a⟩

/-- **The number of rows on the pile**, by the border's number. -/
def riderPile (lo hi : Nat) (n : Nat → Nat) : RiderCl W VerifiableInference.Desc.First.S :=
  ⟨lo, hi, fun b _ s => s.out.pending.length = n b⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.riders_at
#print axioms ProofFile.Honest.riders_next
#print axioms ProofFile.Honest.behind_of_keeps
#print axioms ProofFile.Honest.behindS_of_keeps
