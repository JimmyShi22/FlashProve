-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Said.lean: a second family of conditions beside the invariant,
for what was shown in the clear. No clause of the invariant `Thr` (Honest/Thread/Thr.lean) speaks of
the values that the earlier rounds have shown: its clause on how the verifier's state was made says
that the verifier's own steps accepted these rounds, and no more. Here: a parameter `Said`, by the
border's number, on a run's coins and on the state of the prover's run (its input, what was heard,
what was seen, the columns opened); `ThrS`, the invariant together with that parameter; and one more
hypothesis for each sub-protocol. Definitions, meant as hypotheses; and four conditional lemmas.
They are general in the parameters: no kind is named. Acceptance needs nothing of `Said`: the rules
for a file's acceptance can be stated without it; from `Thr` alone, which does not read the field
`opened`, their hypotheses are asked at every value of that field, `none` too
(Honest/Thread/ThrField.lean, Limits).

  1  `ThrS`, `SaidNext`   the invariant with `Said`; the hypothesis: `Said` holds after the
     sub-protocol's rounds, at the state that has taken the sub-protocol's columns
  2  `playsOn_pair`   its end: `PlaysOn` (Honest/Law/ThreadC.lean) from `ThrS` to `ThrS`; its
     premises, beside `T.bs[b]? = some blk`: `PlaysOn` from `ThrS` to `Thr`, and `SaidNext`
  3  `saidNext_and`, `SaidAt`, `saidNext_carry`, `saidNext_early`   two clauses; a clause by number

The hypothesis `SaidNext`. It is asked at all coins: no acceptance of this sub-protocol's and no
fall is among its hypotheses (the invariant before it includes the acceptance of every earlier
sub-protocol). From `ThrS` before the sub-protocol, a list of challenges that its rounds can draw
(`drawsFit`) and the sub-protocol's played rounds (`Thread.Moved`) it asks for `Said` at the next
border, at the state after them with the columns that the sub-protocol read laid behind those in its
field `opened` (`Mid.took`): the state as the walk of Honest/Walk.lean leaves it where the
sub-protocol's step accepts. No stop is named; but `Thread.Moved` holds only where `play` returns,
and `play` does not return where a part of the sub-protocol stops: there nothing is asked.

What it is for. Wherever a statement is needed on what the earlier rounds show. Its first use: that
their words are below the field's prime (Honest/Thread/SaidOk.lean).

How it can hold vacuously. `Said := False`: it cannot be entered. `Said := True`: it costs nothing
and gives nothing. `Said` reads no state of the verifier's and no table; of the tables it can read
the columns in the state's field `opened` alone.

One parameter for each chain, for all its kinds; the hypothesis has to be proved at every
sub-protocol. So: (1) two kinds' clauses are joined by "and" (`saidNext_and`). (2) A clause names
rounds by their number in what was seen: `SaidAt b₀ n C`: from the border b₀ on, n rounds have been
seen, and C holds of the run's coins, the input and the first n rounds seen. Such a clause is
carried past every later sub-protocol without further proof (`saidNext_carry`), and asks nothing
before its own (`saidNext_early`): so it has to be proved at one sub-protocol, the one before b₀ (at
b₀ = 0: where the chain is entered). (3) Whoever supplies a chain's `Thread` supplies its `Said`:
the conjunction of the kinds' clauses and `SaidOk`.

Limits.
  * It is not proved that the hypothesis can be met.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Ties
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-! ## 1 The invariant with `Said`; the hypothesis -/

/-- **The invariant and `Said`**, at a border. It is a definition, meant as a hypothesis. -/
def ThrS (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) : Prop :=
  Thr T b k s m E ∧ Said b k m

/-- **`Said` holds after the sub-protocol's rounds**, at the state that has taken the sub-protocol's
columns (`y.2.took cols`), at sub-protocol number `b`: at all coins; no acceptance of this
sub-protocol's is among its hypotheses. It is a definition, meant as a hypothesis. Nothing is
claimed of it, and it is none of the library's goals. -/
def SaidNext (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, Thr T b k s m E → Said b k m →
    drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
    Said (b + 1) k (y.2.took cols)

/-! ## 2 `PlaysOn` at `ThrS` -/

theorem playsOn_pair {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    (h : PlaysOn T.φ Bk T.chain T.ft T.hs blk (ThrS T Said b) (Thr T (b + 1)))
    (hS : SaidNext T Said b) :
    PlaysOn T.φ Bk T.chain T.ft T.hs blk (ThrS T Said b) (ThrS T Said (b + 1)) := by
  intro k s m E ds l hA hd hst hl
  obtain ⟨hT, hs₀⟩ := hA
  obtain ⟨y, cols, hy, hc, hB⟩ := h k s m E ds l ⟨hT, hs₀⟩ hd hst hl
  refine ⟨y, cols, hy, hc, fun s' n hs => ?_⟩
  have hM : T.Moved blk k m E ds y cols := by
    unfold Thread.Moved
    exact ⟨⟨l, hl, hy⟩, hc⟩
  exact ⟨hB s' n hs, hS blk hblk k s m E ds y cols hT hs₀ hd hM⟩

/-! ## 3 Two clauses; a clause by number -/

/-- Two kinds' clauses, joined. -/
theorem saidNext_and {Said' : Nat → Coins Bk → Mid W X → Prop} {b : Nat}
    (h : SaidNext T Said b) (h' : SaidNext T Said' b) :
    SaidNext T (fun b k m => Said b k m ∧ Said' b k m) b :=
  fun blk hblk k s m E ds y cols hT hS hd hM =>
    ⟨h blk hblk k s m E ds y cols hT hS.1 hd hM, h' blk hblk k s m E ds y cols hT hS.2 hd hM⟩

/-- **A clause that names rounds by their number in what was seen**: from the border `b₀` on, `n`
rounds have been seen, and `C` holds of the run's coins, the input and the first `n` rounds seen. It
is a definition: a form for choosing the parameter `Said`. -/
def SaidAt (b₀ n : Nat) (C : Coins Bk → W → List Fmt.RoundView → Prop) (b : Nat) (k : Coins Bk)
    (m : Mid W X) : Prop :=
  b₀ ≤ b → n ≤ m.seen.length ∧ C k m.st.input (m.seen.take n)

/-- Such a clause is carried past every sub-protocol after its border, without further proof. -/
theorem saidNext_carry {b₀ n : Nat} {C : Coins Bk → W → List Fmt.RoundView → Prop} {b : Nat}
    (hb : b₀ ≤ b) : SaidNext T (SaidAt b₀ n C) b := by
  intro blk _ k s m E ds y cols _ hS _ hM _
  obtain ⟨hn, hC⟩ := hS hb
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  obtain ⟨hi, -, hs⟩ := play_mid _ _ _ _ _ hy
  show n ≤ y.2.seen.length ∧ C k y.2.st.input (y.2.seen.take n)
  rw [hi, hs, List.take_append_of_le_length hn, List.length_append]
  exact ⟨Nat.le_trans hn (Nat.le_add_right _ _), hC⟩

/-- And it asks nothing before its own sub-protocol. -/
theorem saidNext_early {b₀ n : Nat} {C : Coins Bk → W → List Fmt.RoundView → Prop} {b : Nat}
    (hb : b + 1 < b₀) : SaidNext T (SaidAt b₀ n C) b :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_le_of_lt hb)

end ProofFile.Honest

#print axioms ProofFile.Honest.playsOn_pair
#print axioms ProofFile.Honest.saidNext_and
#print axioms ProofFile.Honest.saidNext_carry
#print axioms ProofFile.Honest.saidNext_early
#print axioms ProofFile.Honest.ThrS
#print axioms ProofFile.Honest.SaidNext
#print axioms ProofFile.Honest.SaidAt
