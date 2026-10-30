-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Thr/Yes.lean: the closing of a segment (K10) as one member of a thread
(Honest/Thread/Thr.lean): when does the description's own block for the closing accept the rounds that the prover's
side has played? The answer is stated in the form `AcceptedS T Said fall b` (Honest/Thread/PaysS.lean), which the
thread's lemma for a whole chain asks of each member. The thread T and the parameters Said and fall are variables
throughout. No definition; fourteen theorems.

Words used below.
  the block         a block blk with `Tied c Z l p Q blk` (Honest/K10/SimLot.lean): the chain's block at the closing's
                    number in link l. One clause of `Tied` is an equation: blk is the kind's block at the numbers Q,
                    lifted to the chain's state (`K9.closing`), carried to the chain's type of claims and seated
                    (`IM.seatedAs`, Johnson/IMR/SeatForm.lean)
  the record        `K9.recOf t` (Johnson/Desc/First/Batch/Place.lean): what the closing reads of the verifier's state
                    t: the rows owed, the live frame, the statement
  no mark           t.failed = none
  shaped            of a list rs of rounds: rs.length = 2 + Q.k and `ShapedAll rs`
                    (Johnson/Desc/K10/Honest/YesFree.lean): the first round shows nothing, the second one element,
                    each later one two; each drew one element, no position and no matrix entry
  the two tests     `closeShapeB Q` of the record, and `closeValsB` of the record and the rounds
                    (Johnson/Desc/K10/Honest/Split.lean). Both are executable. Of the rounds the second reads what the
                    first one drew, and nothing else
  a stand           coins k, a verifier's state s, a state m of the prover's run and tables En at which
                    `ThrS T Said b k s m En` holds: the thread's invariant in front of member number b, and Said

What is proved.
  `retype_step`     a block carried to another type of claims has the same step
  `tied_fits_iff`   the tests that the block's step makes on rounds and columns before it decides (`Block.Fits`) pass
                    just if the rounds are shaped: `seated_fits_iff` (Johnson/Desc/K10/Honest/SeatYes.lean) at the
                    equation
  **`tied_step_iff`**   the block's step accepts at a state t just if t has no mark, the rounds are shaped, and the
                    two tests pass: `seated_step_iff` (SeatYes.lean) at the equation
  `tied_step`       one direction, from the stronger test `closeBaseB` (Johnson/Desc/K10/Honest/BaseB.lean), with the
                    result written out: the state after the step is t with some record laid back (`K9.putRec`), and no
                    column is taken: `closing_step_of` (AtS.lean), then `IM.step_alone` (SeatForm.lean)
  `vals_of_drawn`   the second test gives the same answer at a list of rounds and at the list that has the same
                    challenges and shows nothing
  `stepped_of_yes`  at any thread and any block: the prover's side of the step (`Thread.Moved`) and an acceptance of
                    the block's step at the rounds as played, whatever number of columns it reports as taken, give
                    `Thread.Stepped`: by `step_takes` (Honest/Thread/Ties.lean)
  `unmarked_at`     under the premise front (below), the verifier's state at which the invariant holds has no mark
  `moved_shaped`    where T.hs has a prover's side at the block's place and the challenges fit the block's rounds, the
                    rounds as played are shaped: by `fits_of_halved`, `halved_of_half` (Honest/Thread/FitsAll.lean).
                    What that side sends is not read
  `tests_of_stepped`   from `Thread.Stepped` at the block: no mark before the step, and the two tests pass
  **`close_accepted_iff`**   `AcceptedS T Said fall b` holds if and only if, at every stand, list of challenges and
                    prover's side of the step that it quantifies over, the state has no mark and the two tests pass
  `close_accepted_tests`   so `AcceptedS` follows from front and the two tests at the stands
  `close_accepted_base`   and from front and `closeBaseB` at the stands
  `close_accepted_of_tests`, **`close_accepted`**   these two again, with the premises on T taken from `CloseAt`
                    (Honest/K10/Thr/CloseAt.lean)

The premises, by name.
  on T's fields     T.bs[b]? is the block; T.hs has a prover's side at the block's place. `CloseAt` gives both
  front             also on a field of T: at number b, `T.form` passes at no state that has a mark
  ready             not a fact on T's fields: at every stand and every list of challenges at which `fall b` returns
                    none, `closeBaseB` passes at the record of the verifier's state. In `close_accepted_tests` and
                    `close_accepted_of_tests`: at such a stand and list, if the challenges also fit the block's
                    rounds, the two tests pass, the second at these challenges

Limits. ready is proved of no state: neither `closeBaseB` nor the two tests are derived from the invariant, and this
file does not say whether they can fail at a stand. By `close_accepted_iff`, no mark and the two tests are exactly what
`AcceptedS` asks wherever the prover's side of the step exists. `closeBaseB` implies the first test, and the second
wherever the first round drew one element (`split_of_base`, Split.lean; not used here); the converse is not proved.
Acceptance depends on nothing that is sent beyond the rounds being shaped: of the closing's job the last two lemmas read
the place's numbers J.pub.par, and no lemma reads its part's moves or the function that supplies its statement; of the
prover's side they use only that one is found at the place. So every lemma here holds equally of a side that sends the
words computed at empty tables (Honest/K10/Wipe/Speaks.lean tells such a side from one that speaks of its own tables).
`Tied`, `CloseAt`, `Thr`, `ThrS` and `Thread.Moved` are premises here. At a thread whose invariant is false everywhere,
at a `fall` that never returns none, and where `chainSteps` returns no steps for the block (`Thread.Moved` holds its
return), `AcceptedS` holds vacuously. Of the state after the step only `tied_step` says anything. No property of the
protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Thr.CloseAt
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.FitsAll
import Johnson.Desc.ProofFile.Honest.Thread.MovedDrawn
import Johnson.Desc.K10.Honest.SeatYes
import Johnson.Desc.K10.Honest.AtS
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par Rec putRec_keeps)

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## The seated block's step -/

/-- A block carried to another type of claims has the same step. -/
theorem retype_step {σ C C' : Type} (x : Block σ C) (ft : Nat) (s : σ) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    (x.retype : Block σ C').step ft s rs cols = x.step ft s rs cols := rfl

section
variable {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Q : Par}
  {blk : Block S ProofFile.Cl}

/-- At the seated block, the tests that the step makes on rounds and columns before it decides pass just if there are
2 + k rounds of the kind's shape. -/
theorem tied_fits_iff (Td : Tied c Z l p Q blk) (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    blk.Fits ft rs cols ↔ rs.length = 2 + Q.k ∧ YesFree.ShapedAll rs := by
  obtain ⟨-, -, -, he, -⟩ := Td
  rw [he]
  exact YesFree.seated_fits_iff Q _ _ _ ft rs cols

/-- **The seated block's step accepts just if** the state has no mark of failure, the rounds are 2 + k of the kind's
shape, and both tests pass at the state's record. -/
theorem tied_step_iff (Td : Tied c Z l p Q blk) (ft : Nat) (t : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    (∃ t' n, blk.step ft t rs cols = .ok (t', n)) ↔
      t.failed = none ∧ rs.length = 2 + Q.k ∧ YesFree.ShapedAll rs ∧
        YesFree.closeShapeB Q (VerifiableInference.Desc.K9.recOf t) = true ∧
        YesFree.closeValsB (VerifiableInference.Desc.K9.recOf t) rs = true := by
  obtain ⟨-, -, -, he, -⟩ := Td
  rw [he]
  exact YesFree.seated_step_iff Q _ _ ft t rs cols

/-- Where `closeBaseB` passes at the state's record, the state has no mark and the rounds are 2 + k of the kind's shape,
the seated block's step accepts: it returns the state with some record laid back, and takes no column. -/
theorem tied_step (Td : Tied c Z l p Q blk) {t : S}
    (h : YesFree.closeBaseB Q (VerifiableInference.Desc.K9.recOf t) = true) (hm : t.failed = none) (ft : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hl : rs.length = 2 + Q.k) (hs : YesFree.ShapedAll rs) :
    ∃ r, blk.step ft t rs cols = .ok (VerifiableInference.Desc.K9.putRec t r, 0) := by
  obtain ⟨-, -, -, he, -⟩ := Td
  have he' : IM.LaidAlone ProofFile.sameReply blk (VerifiableInference.Desc.K9.closing (Cl := Unit) Q).retype blk.name
      (IM.cAt l (IM.subAt l) 1 KindName.K10) := he
  obtain ⟨r, hr⟩ := YesFree.closing_step_of (Cl := Unit) h ft rs cols hl hs
  have hk : (IM.cAt l (IM.subAt l) 1 KindName.K10).kind ≠ KindName.K7 := by
    show KindName.K10 ≠ KindName.K7
    decide
  have hsame : ProofFile.sameReply t (VerifiableInference.Desc.K9.putRec t r) = true := by
    unfold ProofFile.sameReply
    rw [(putRec_keeps t r).2.2.2.1]
    exact beq_self_eq_true _
  have hr' : ((VerifiableInference.Desc.K9.closing (Cl := Unit) Q).retype : Block S ProofFile.Cl).step ft t rs cols =
      .ok (VerifiableInference.Desc.K9.putRec t r, 0) :=
    (retype_step _ ft t rs cols).trans hr
  exact ⟨r, (IM.step_alone he' hk ft t _ 0 rs cols).2 ⟨hr', (putRec_keeps t r).2.2.1.trans hm, hsame⟩⟩

end

/-- The second test gives the same answer at a list of rounds and at the list that has the same challenges and shows
nothing. -/
theorem vals_of_drawn (s : Rec) (rs : List Fmt.RoundView) :
    YesFree.closeValsB s ((rs.map (·.drawn)).map fun d => (⟨[], d⟩ : Fmt.RoundView)) = YesFree.closeValsB s rs := by
  have e : YesFree.batDraw ((rs.map (·.drawn)).map fun d => (⟨[], d⟩ : Fmt.RoundView)) = YesFree.batDraw rs := by
    cases rs <;> rfl
  unfold YesFree.closeValsB
  rw [e]

/-! ## At a thread -/

/-- The prover's side of a member's step, and an acceptance of the member's block at the rounds as played, give
`Thread.Stepped`: an accepting step takes exactly the columns that were filled. -/
theorem stepped_of_yes {σ C : Type} (T : Thread Bk σ C V W X Pb) {blk : Block σ C} {k : Coins Bk} {s s' : σ}
    {m : Mid W X} {En : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn} {n : Nat}
    (hM : T.Moved blk k m En ds y cols) (hs : blk.step T.ft s (roundsOf y.1) cols = .ok (s', n)) :
    T.Stepped blk k s m En ds y cols s' := by
  have hM' := hM
  unfold Thread.Moved at hM'
  obtain ⟨-, hc⟩ := hM'
  have hn : n = cols.length := step_takes (moved_drawn T hM) hc hs
  subst hn
  unfold Thread.Stepped
  exact ⟨hM, hs⟩

/-- Where `T.form` at number b passes at no state that has a mark of failure, the verifier's state at which the
invariant holds has none. -/
theorem unmarked_at {C : Type} (T : Thread Bk S C V W X Pb) {b : Nat}
    (front : ∀ (a : T.P) (s : S), T.form b (a, s) = true → s.failed = none) {k : Coins Bk} {s : S} {m : Mid W X}
    {En : Env} (hA : Thr T b k s m En) : s.failed = none := by
  obtain ⟨-, -, hF, -⟩ := hA
  unfold Thread.Form Thread.seat at hF
  exact front _ s hF.1

section
variable {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Q : Par}
  {blk : Block S ProofFile.Cl} (T : Thread Bk S ProofFile.Cl V W X Pb) {Said : Nat → Coins Bk → Mid W X → Prop} {b : Nat}

/-- Where a prover's side is found at the closing's place and the challenges fit the block's rounds, the rounds as
played are 2 + k rounds of the kind's shape. -/
theorem moved_shaped (Td : Tied c Z l p Q blk) {g : Placed V W X}
    (hh : (T.hs.find? fun h => h.place == blk.place) = some g) {k : Coins Bk} {m : Mid W X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn} (hd : drawsFit blk.rounds ds = true)
    (hM : T.Moved blk k m En ds y cols) :
    (roundsOf y.1).length = 2 + Q.k ∧ YesFree.ShapedAll (roundsOf y.1) := by
  unfold Thread.Moved at hM
  obtain ⟨⟨ss, hl, hy⟩, hc⟩ := hM
  exact (tied_fits_iff Td T.ft (roundsOf y.1) cols).1 (fits_of_halved hl (halved_of_half hh) hy hd hc)

/-- From `Thread.Stepped` at the closing's block: the state before the step has no mark of failure, and both tests pass
at its record, the second at the step's challenges. -/
theorem tests_of_stepped (Td : Tied c Z l p Q blk) {k : Coins Bk} {s s' : S} {m : Mid W X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hS : T.Stepped blk k s m En ds y cols s') :
    s.failed = none ∧ YesFree.closeShapeB Q (VerifiableInference.Desc.K9.recOf s) = true ∧
      YesFree.closeValsB (VerifiableInference.Desc.K9.recOf s) (ds.map fun d => (⟨[], d⟩ : Fmt.RoundView)) = true := by
  unfold Thread.Stepped at hS
  obtain ⟨hM, hs⟩ := hS
  obtain ⟨h1, -, -, h4, h5⟩ := (tied_step_iff Td T.ft s (roundsOf y.1) cols).1 ⟨s', _, hs⟩
  have e := vals_of_drawn (VerifiableInference.Desc.K9.recOf s) (roundsOf y.1)
  rw [moved_drawn T hM] at e
  exact ⟨h1, h4, e.trans h5⟩

/-- **What `AcceptedS` asks at the closing's member, in both directions**: it holds if and only if, at everything that
it quantifies over, the verifier's state has no mark of failure and both tests pass at its record. -/
theorem close_accepted_iff (Td : Tied c Z l p Q blk) (hblk : T.bs[b]? = some blk) {g : Placed V W X}
    (hh : (T.hs.find? fun h => h.place == blk.place) = some g)
    (fall : Nat → S → List Fmt.Drawn → Option String) :
    AcceptedS T Said fall b ↔
      ∀ k s m En ds y cols, ThrS T Said b k s m En → drawsFit blk.rounds ds = true →
        chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
        T.Moved blk k m En ds y cols →
        s.failed = none ∧ YesFree.closeShapeB Q (VerifiableInference.Desc.K9.recOf s) = true ∧
          YesFree.closeValsB (VerifiableInference.Desc.K9.recOf s) (ds.map fun d => (⟨[], d⟩ : Fmt.RoundView)) = true := by
  constructor
  · intro hA k s m En ds y cols hT hd hst hf hM
    obtain ⟨s', hS⟩ := hA blk hblk k s m En ds y cols hT hd hst hf hM
    exact tests_of_stepped T Td hS
  · intro H blk' hblk' k s m En ds y cols hT hd hst hf hM
    have e : blk = blk' := Option.some.inj (hblk.symm.trans hblk')
    subst e
    obtain ⟨h1, h2, h3⟩ := H k s m En ds y cols hT hd hst hf hM
    obtain ⟨hlen, hsh⟩ := moved_shaped T Td hh hd hM
    have e3 := vals_of_drawn (VerifiableInference.Desc.K9.recOf s) (roundsOf y.1)
    rw [moved_drawn T hM] at e3
    obtain ⟨s', n, hs⟩ := (tied_step_iff Td T.ft s (roundsOf y.1) cols).2 ⟨h1, hlen, hsh, h2, e3.symm.trans h3⟩
    exact ⟨s', stepped_of_yes T hM hs⟩

/-- `AcceptedS` at the closing's member, from the premise front on `T.form` and the premise ready in its weakest form:
the two tests pass wherever the invariant and Said hold, the challenges fit and `fall` returns none. -/
theorem close_accepted_tests (Td : Tied c Z l p Q blk) (hblk : T.bs[b]? = some blk) {g : Placed V W X}
    (hh : (T.hs.find? fun h => h.place == blk.place) = some g)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (front : ∀ (a : T.P) (s : S), T.form b (a, s) = true → s.failed = none)
    (ready : ∀ k s m En ds, ThrS T Said b k s m En → drawsFit blk.rounds ds = true → fall b s ds = none →
      YesFree.closeShapeB Q (VerifiableInference.Desc.K9.recOf s) = true ∧
        YesFree.closeValsB (VerifiableInference.Desc.K9.recOf s) (ds.map fun d => (⟨[], d⟩ : Fmt.RoundView)) = true) :
    AcceptedS T Said fall b :=
  (close_accepted_iff T Td hblk hh fall).2 fun k s m En ds _ _ hT hd _ hf _ =>
    ⟨unmarked_at T front hT.1, ready k s m En ds hT hd hf⟩

/-- `AcceptedS` at the closing's member, from front and the stronger form of ready: `closeBaseB`, which reads no
challenge, passes wherever the invariant and Said hold and `fall` returns none. -/
theorem close_accepted_base (Td : Tied c Z l p Q blk) (hblk : T.bs[b]? = some blk) {g : Placed V W X}
    (hh : (T.hs.find? fun h => h.place == blk.place) = some g)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (front : ∀ (a : T.P) (s : S), T.form b (a, s) = true → s.failed = none)
    (ready : ∀ k s m En ds, ThrS T Said b k s m En → fall b s ds = none →
      YesFree.closeBaseB Q (VerifiableInference.Desc.K9.recOf s) = true) :
    AcceptedS T Said fall b := by
  intro blk' hblk' k s m En ds y cols hT hd _ hf hM
  have e : blk = blk' := Option.some.inj (hblk.symm.trans hblk')
  subst e
  obtain ⟨hlen, hsh⟩ := moved_shaped T Td hh hd hM
  obtain ⟨r, hs⟩ := tied_step Td (ready k s m En ds hT hf) (unmarked_at T front hT.1) T.ft (roundsOf y.1) cols hlen hsh
  exact ⟨_, stepped_of_yes T hM hs⟩

end

/-! ## From the named premises on the thread's fields -/

section
variable {T : Thread Bk S ProofFile.Cl V W X Pb} {b : Nat} {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat}
  {p : VerifiableInference.Desc.K9.Where} {blk : Block S ProofFile.Cl} {J : CloseJob W}

/-- `close_accepted_tests`, with the premises on the thread's fields taken from `CloseAt`. -/
theorem close_accepted_of_tests (H : CloseAt T b c Z l p blk J) {Said : Nat → Coins Bk → Mid W X → Prop}
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (front : ∀ (a : T.P) (s : S), T.form b (a, s) = true → s.failed = none)
    (ready : ∀ k s m En ds, ThrS T Said b k s m En → drawsFit blk.rounds ds = true → fall b s ds = none →
      YesFree.closeShapeB J.pub.par (VerifiableInference.Desc.K9.recOf s) = true ∧
        YesFree.closeValsB (VerifiableInference.Desc.K9.recOf s) (ds.map fun d => (⟨[], d⟩ : Fmt.RoundView)) = true) :
    AcceptedS T Said fall b := by
  obtain ⟨g, hg, -⟩ := H.halfAt
  exact close_accepted_tests T H.tied H.blkAt hg fall front ready

/-- **`AcceptedS` at the closing's member**, at every `fall` and Said, from `CloseAt`, front and ready (`closeBaseB`):
`close_accepted_base`, with the premises on the thread's fields taken from `CloseAt`. -/
theorem close_accepted (H : CloseAt T b c Z l p blk J) {Said : Nat → Coins Bk → Mid W X → Prop}
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (front : ∀ (a : T.P) (s : S), T.form b (a, s) = true → s.failed = none)
    (ready : ∀ k s m En ds, ThrS T Said b k s m En → fall b s ds = none →
      YesFree.closeBaseB J.pub.par (VerifiableInference.Desc.K9.recOf s) = true) :
    AcceptedS T Said fall b := by
  obtain ⟨g, hg, -⟩ := H.halfAt
  exact close_accepted_base T H.tied H.blkAt hg fall front ready

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.retype_step
#print axioms ProofFile.Honest.K10.tied_fits_iff
#print axioms ProofFile.Honest.K10.tied_step_iff
#print axioms ProofFile.Honest.K10.tied_step
#print axioms ProofFile.Honest.K10.vals_of_drawn
#print axioms ProofFile.Honest.K10.stepped_of_yes
#print axioms ProofFile.Honest.K10.unmarked_at
#print axioms ProofFile.Honest.K10.moved_shaped
#print axioms ProofFile.Honest.K10.tests_of_stepped
#print axioms ProofFile.Honest.K10.close_accepted_iff
#print axioms ProofFile.Honest.K10.close_accepted_tests
#print axioms ProofFile.Honest.K10.close_accepted_base
#print axioms ProofFile.Honest.K10.close_accepted_of_tests
#print axioms ProofFile.Honest.K10.close_accepted
