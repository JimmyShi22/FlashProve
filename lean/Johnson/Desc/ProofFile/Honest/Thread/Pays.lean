-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Pays.lean: the hypotheses on one sub-protocol of a chain's flat
list under which the invariant `Thr` (Honest/Thread/Thr.lean) goes from the border before it to the
border after it; and the state of a run inside a sub-protocol. Each is the definition of a
proposition, meant as a hypothesis of lemmas. No theorem is stated here.

  1  `Thread.Moved`, `Thread.Stepped`   the sub-protocol's own step: the `Step`s that `chainSteps`
     prepares for it are played and the columns that it reads are filled; and its own step accepts
  2  `Thread.fresh`, `Plays`   it plays, at all coins
  3  `Behind`   after its acceptance: the form, the riders (`Thread.rides`), what its step has left
     unchanged; at all coins
  4  `Exchange`   the items that its row owes, after its acceptance; at all coins
  5  `RidesPast`   what rides past: the items that are open and that the row neither shuts nor owes
  6  `MadeNext`   the clauses (F) and (X) after the sub-protocol: generic, for no particular kind
  7  `Accepted`   the acceptance itself, outside the fall
  8  `Inside`   the state of a run after the first n rounds of a sub-protocol

One form for every sub-protocol. The hypotheses speak at the `Step`s that `chainSteps` itself
prepares for the one sub-protocol: with moves where a prover's side is defined, without where none
is. So they cover a sub-protocol with a prover's side, one without a round, and one with a round and
no prover's side. That the book gives every part of the list its coins (`chainSteps … = .ok l`) is a
hypothesis here, not something to be proved.

How the hypotheses are divided. Five say nothing of a fall (`Fall`, Honest/Side.lean: an event at
which a sub-protocol may reject an honest run). `Plays`: the prover's side goes through, at every
run's coins, at every list of challenges that the sub-protocol's rounds can draw and at which
nothing of it stops. `Behind`, `Exchange`, `RidesPast`, `MadeNext`: wherever the sub-protocol's own
step accepts, the invariant holds after it. So, under these five and the executable test `T.fits`,
the invariant holds up to the first rejection, whatever rejects. The sixth, `Accepted`, is the
acceptance itself, and is excused where the parameter `fall` fires: it is used where acceptance is
to be proved, and nowhere else. At some rows what an owed item says is defined in another module
than the sub-protocol (a sending that owes a condition on the array which it sends; the batching,
which owes a condition on every kind's runs after it): so the items are asked separately, in
`Exchange`.

The parameter `fall`. For each sub-protocol: a test on the verifier's state before it and on its own
challenges. It excuses that sub-protocol's own step. Nothing that plays reads it. At
`fun _ _ _ => none` no step is excused. A test that fires wherever the step rejects makes `Accepted`
hold vacuously: what the test is to be, and how many lists it covers at each fixed input and coins,
has to be proved beside it.

Inside a sub-protocol. A list of several parts has no state of the verifier's between two parts.
`Inside T b n` tells the state of the run after the sub-protocol's first n rounds: it is reached, by
`play`, from a state at which the invariant holds at the border before the sub-protocol. `play`
returns there only if no part has stopped (Honest/Law/Play.lean, `tell_yields`;
Honest/Law/Along.lean, `hear_mid`), and `chainSteps` prepares one `Step` for each round
(Honest/Law/Run.lean, `steps_decl`).

Limits.
  * Definitions alone: this file does not prove that any of them can be met at a description of the
    protocol. At the key file's, where no part sends: E2E/KeyPlaysQuiet.lean, E2E/KeyRidesSame.lean.
  * `Plays`, `Behind`, `Exchange`, `RidesPast` and `Accepted` each have the whole invariant at the
    border before the sub-protocol as a hypothesis: at an invariant that is false everywhere all
    five hold vacuously, and `Inside` is false. `MadeNext` has the clauses (F) and (X) alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 1 The sub-protocol's own step -/

/-- **The prover's side of the sub-protocol's step**, from (m, E) at the challenges `ds`. `y`: the
played rounds and the state of the prover's run after them. `cols`: the columns read. -/
def Thread.Moved (blk : Block S Cl) (k : Coins Bk) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) : Prop :=
  (∃ l, chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok l ∧ play l ds [] m = .ok y) ∧
    fillCols (readsOf T.chain T.ft (E.add y.1).stored (E.add y.1).tree blk.rounds ds) [] =
      .ok cols

/-- **The sub-protocol's step**: that, and the acceptance of the sub-protocol's own step
(`Block.step`: its tests on the rounds and on the columns, and its `decide`), from s to s', at just
these columns. -/
def Thread.Stepped (blk : Block S Cl) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : S) : Prop :=
  T.Moved blk k m E ds y cols ∧ blk.step T.ft s (roundsOf y.1) cols = .ok (s', cols.length)

/-! ## 2 It plays -/

/-- The sources that are available after sub-protocol number `b` and not before it. -/
def Thread.fresh (b : Nat) : List Fmt.TreeSource :=
  (T.hand (b + 1)).filter fun σ => !(T.hand b).contains σ

/-- **It plays**, at sub-protocol number `b`: from the invariant before it, at every run's coins, at
every list of challenges that its rounds can draw and at which nothing of it stops: `play` and the
filling of the columns return, and its new trees are the functions' tables. It is a definition,
meant as a hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def Plays (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds l, Thr T b k s m E →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs = .ok l →
    ∃ y cols, T.Moved blk k m E ds y cols ∧ T.Trees (T.fresh b) k y.2 (E.add y.1)

/-! ## 3 After its acceptance -/

/-- **After its acceptance**, at sub-protocol number `b`: from the invariant before it and the
sub-protocol's step, its acceptance included: after it the form and the riders hold, and the step
has left unchanged what `keeps` names. At every run's coins: no fall is in it. It is a definition,
meant as a hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def Behind (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Form (b + 1) k s' y.2 ∧ T.rides (b + 1) y.2.st.input s' ∧ T.keeps b s s'

/-! ## 4 The exchange -/

/-- **The exchange**, at sub-protocol number `b`: from the invariant before it and the
sub-protocol's step: the items that its row owes hold after it. It is a definition, meant as a
hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def Exchange (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Items (T.row b).owes k s' y.2 (E.add y.1)

/-! ## 5 What rides past -/

/-- **What rides past**, at sub-protocol number `b`: an item that is open before it and that the row
neither shuts nor owes, if it holds of a witness before, holds of it at every state `s'` that
`keeps b s s'` allows and after any list `ps` of played rounds is added to the tables: no step is
assumed; the whole invariant before the sub-protocol is given. It is a definition, meant as a
hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def RidesPast (b : Nat) : Prop :=
  ∀ k s m E s' ps i v, Thr T b k s m E → T.keeps b s s' → i ∈ T.opened b →
    i ∉ (T.row b).shuts → i ∉ (T.row b).owes →
    T.means m.st.input i (T.seat k m s) (T.strs E) v →
    T.means m.st.input i (T.seat k m s') (T.strs (E.add ps)) v

/-! ## 6 What is generic -/

/-- **The clauses (F) and (X) after the sub-protocol**: from the two before it and the
sub-protocol's step. No parameter of a table, no item and no definition of a prover's side is in it:
it has to be proved once, not kind by kind. It is a definition, meant as a hypothesis. Nothing is
claimed of it, and it is none of the library's goals. -/
def MadeNext (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', T.Fit b m → T.Made b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Fit (b + 1) y.2 ∧ T.Made (b + 1) k s' y.2 (E.add y.1)

/-! ## 7 The acceptance itself -/

/-- **It is accepted**, at sub-protocol number `b`: from the invariant before it and the prover's
side of the step, where nothing of the sub-protocol stops and the parameter `fall` does not fire:
the sub-protocol's own step accepts. It is a definition, meant as a hypothesis. Nothing is claimed
of it, and it is none of the library's goals. -/
def Accepted (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, Thr T b k s m E →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
    T.Moved blk k m E ds y cols → ∃ s', T.Stepped blk k s m E ds y cols s'

/-! ## 8 Inside a sub-protocol -/

/-- **The state of a run after the first `n` rounds of sub-protocol number `b`**: a condition on a
whole run's coins, the state of the prover's run, and the available tables: it is reached by `play`
over the sub-protocol's first `n` `Step`s from a state at which the invariant holds at the border
before the sub-protocol. No state of the verifier's is among its arguments; the one before the
sub-protocol is named inside. It is a definition, meant as a hypothesis. Nothing is claimed of it,
and it is none of the library's goals. -/
def Inside (b n : Nat) (k : Coins Bk) (m : Mid W X) (E : Env) : Prop :=
  ∃ blk s m₀ E₀ l ds y, T.bs[b]? = some blk ∧ Thr T b k s m₀ E₀ ∧
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m₀.st.input) [blk] T.hs = .ok l ∧
    drawsFit (blk.rounds.take n) ds = true ∧ play (l.take n) ds [] m₀ = .ok y ∧ m = y.2 ∧
    E = E₀.add y.1

end ProofFile.Honest
