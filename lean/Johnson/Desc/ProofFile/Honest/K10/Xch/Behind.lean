-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/Behind.lean: the closing of a segment (K10): from an acceptance of the step of a
chain's block at a closing's number, in the seated form (`Tied`), to the verifier's state after that step. It holds
thirteen lemmas and no definition.

Words.
  the block           a block blk with `Tied c Z l p Q blk` (Honest/K10/SimLot.lean): the chain's block at the
                      closing's number in link l. One clause of `Tied` is an equation: blk is the kind's block at the
                      numbers Q, lifted to the chain's state (`K9.closing`, Johnson/Desc/First/Batch/Place.lean: "the
                      lifted block"), carried to the chain's type of claims and seated under two guards
                      (`IM.seatedAs`, Johnson/IMR/SeatForm.lean)
  the step accepts    `blk.step ft s rs cols = .ok (s', n)` (`Block.step`, Johnson/Desc/Block.lean). ft: the number of
                      the first tree. s, s': the verifier's state before and after. rs: the rounds. cols: the columns
                      at hand. n: how many of them the step takes
  shaped              of a list of rounds: `ShapedAll` (Johnson/Desc/K10/Honest/YesFree.lean): the first round shows
                      nothing, the second one element, each later one two; each drew one element, no position and no
                      matrix entry
  the record          `K9.recOf s` (Place.lean): what the closing reads of the state s: the rows owed, the live frame,
                      the statement. `K9.putRec s r` is s with the record r laid back
  without its digest  `noDigest` (Block.lean): the form in which a block's step shows a round to the block's decision

What is proved.
  `drawnOf_noDigest`, `sentOf_noDigest`, `drawn_noDigest`, `claimOf_noDigest`, `foldOutAt_noDigest`
                      the readers of a round in Johnson/Prover/Link/FormFold.lean (the element drawn, the elements
                      sent, the running claim, the single rows that the fold returns) return the same at rounds with
                      and without their digests
  **`tied_decides`**  where the block's step accepts (premises Td: `Tied`; hs: the acceptance): rs are 2 + `Q.k`
                      shaped rounds; the lifted block's decision, at the rounds without their digests and at no group
                      of columns, returns s'; s' has no mark of failure (`s'.failed = none`); n = 0
  **`tied_keeps`**    under Td and hs: `K10Keeps s s'` (Johnson/Desc/K10/Honest/Keeps.lean: what an acceptance of the
                      closing leaves and changes of the state)
  **`behind_of_tied`**
                      under Td and hs: s' is the state that `behind Q s rs` returns
                      (Johnson/Desc/K10/Honest/CarryTests.lean: the state after the lifted block's step, without the
                      guards, at first tree 0 and no columns). This is the premise h5 of `carryExact_of_tests`; the
                      head of CarryTests.lean names it as not shown there
  **`tied_behind`**   under Td and hs, and where the facts `CloseBase Q (K9.recOf s) D`
                      (Johnson/Desc/K10/Honest/Base.lean) are given (H): the rounds without their digests are rB, rE
                      and a list rR, 2 + `Q.k` in all and shaped; the batching returns a row at the element that rB
                      drew; and s' is s with this record laid back: nothing owed; the frame with the single rows
                      `foldOutAt` of that row at rE :: rR, no mask, the link's number one more, the next call "first";
                      the statement with the test begun and the mask's message marked as spent. The number, the shape,
                      the row and the state are the premises hl, hsh, hrow and hs₁ of `carryExact_from_front`
                      (Johnson/Desc/K10/Honest/CarryWords.lean), in its own wording
  `tied_behind_rounds`
                      the same with rB, rE and rR the rounds themselves, with their digests
  `stepped_keeps`, `stepped_behind_is`, **`stepped_behind`**
                      `tied_keeps`, `behind_of_tied` and `tied_behind_rounds` at a thread's step (hS:
                      `Thread.Stepped`, Honest/Thread/Pays.lean). The thread T is a variable; ft is T.ft, and the
                      rounds are the rounds as played, `roundsOf y.1`. The last adds that no column was filled

By what. The readers: by the definitions' texts and `claimOf_cons` (Johnson/Prover/Link/FormFoldLaws.lean). The guards
off the seated block: `IM.step_alone` (SeatForm.lean) and `retype_step` (Honest/K10/Thr/Yes.lean). The step opened:
`step_iff` (Johnson/Top/H0/StepLaws/StepLaws.lean), `groups_nil` and `shapedAll_noDigest`
(Johnson/Desc/K10/Honest/Step.lean), `tied_step_iff` (Thr/Yes.lean). Then `closing_turns` (Keeps.lean),
`closing_step_is` (CarryTests.lean) and `closing_leaves` (Johnson/Desc/K10/Honest/CarryAtLink.lean): a decision
returns one value, so the state that `closing_leaves` writes out is s'.

Two definitions are named `spent`. `Johnson.Prover.Link.spent` (FormFold.lean) is the one in this file's statements,
as in the lemmas on the carry (CarryWords.lean, CarryTests.lean, CarryAtLink.lean).
`VerifiableInference.Desc.First.Close.spent` (Johnson/Desc/First/Close/Law/StBehind.lean) is the one in `K10Keeps`.
The two have the same text; no lemma here says that they are equal. In a file that opens both namespaces whole the
bare name has two readings: this file opens the first by name, and of the second namespace `Par` and `entries` alone.

Limits. `Tied` (Td), the step's acceptance (hs, hS) and `CloseBase` (H) are premises: none is proved here of any
chain, state or thread. Where the step rejects, every lemma from `tied_decides` on holds vacuously. `CloseBase` is not
derived from the acceptance here: `tied_behind`, `tied_behind_rounds` and `stepped_behind` say nothing at a state at
which it fails. Of `Thread.Stepped` the second half alone is read, the acceptance: nothing is drawn from what the
prover's side sent, and the invariant `Thr` is no premise. Not spoken of: what the rounds show; whether the row or the
single rows are true of any words; whether the way into the next code switch (`doorZ`) returns at s'. So the other
premises of `carryExact_from_front` and `carryExact_of_tests` stay; for the latter's two tests on the rounds (h2, h3)
this file gives the propositions, not that the tests return true. At the first chain's type of state and at the type
of claims `ProofFile.Cl`. Nothing is shown of a run of the protocol. No property of the protocol is claimed: nothing is said
on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Thr.Yes
import Johnson.Desc.K10.Honest.CarryTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open Johnson.Prover.Link (spent sentOf drawnOf claimOf foldOutAt)
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par entries)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase ShapedAll K10Keeps)

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 The fold's readers of a round do not see the digest -/

/-- The element that a round drew first is the same without the round's digest. -/
theorem drawnOf_noDigest (r : Fmt.RoundView) : drawnOf (noDigest r) = drawnOf r := rfl

/-- The elements that a round shows as sent are the same without the round's digest. -/
theorem sentOf_noDigest (r : Fmt.RoundView) : sentOf (noDigest r) = sentOf r := rfl

/-- The elements that the rounds of a list drew are the same without the rounds' digests. -/
theorem drawn_noDigest (rs : List Fmt.RoundView) : (rs.map noDigest).map drawnOf = rs.map drawnOf := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact congrArg (drawnOf r :: ·) ih

/-- The running claim behind a list of rounds is the same without the rounds' digests. -/
theorem claimOf_noDigest (rs : List Fmt.RoundView) : ∀ x : OnBytes.E, claimOf (rs.map noDigest) x = claimOf rs x := by
  induction rs with
  | nil => exact fun _ => rfl
  | cons r rs ih =>
    intro x
    rw [List.map_cons, Johnson.Prover.Link.claimOf_cons, Johnson.Prover.Link.claimOf_cons, sentOf_noDigest,
      drawnOf_noDigest]
    exact ih _

/-- The single rows that the fold returns are the same at rounds without their digests. -/
theorem foldOutAt_noDigest (S₀ : OnBytes.Statement) (F : OnBytes.FoldShape) (row : OnBytes.GroupRow) (i : Nat)
    (rs : List Fmt.RoundView) : foldOutAt S₀ F row i (rs.map noDigest) = foldOutAt S₀ F row i rs := by
  cases rs with
  | nil => rfl
  | cons rE rR =>
    show OnBytes.foldOutput (spent S₀ i) F row i (drawnOf rE) ((rR.map noDigest).map drawnOf)
        (claimOf (rR.map noDigest)
          (OnBytes.maddE ((sentOf rE).getD 0 OnBytes.zeroE) (drawnOf rE) row.target)) =
      OnBytes.foldOutput (spent S₀ i) F row i (drawnOf rE) (rR.map drawnOf)
        (claimOf rR (OnBytes.maddE ((sentOf rE).getD 0 OnBytes.zeroE) (drawnOf rE) row.target))
    rw [drawn_noDigest, claimOf_noDigest]

/-! ## 2 The seated block's step -/

section
variable {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Q : Par}
  {blk : Block S ProofFile.Cl}

/-- **Where the seated block's step accepts**: the rounds are 2 + `Q.k` rounds of the kind's shape; the lifted block's
decision, at the rounds without their digests and at no group of columns, returns the state that the step returns;
that state has no mark of failure; no column is taken. -/
theorem tied_decides (Td : Tied c Z l p Q blk) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat}
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    rs.length = 2 + Q.k ∧ ShapedAll rs ∧
      (K9.closing (Cl := Unit) Q).decide s (rs.map noDigest) [] = .ok s' ∧ s'.failed = none ∧ n = 0 := by
  obtain ⟨-, hl, hsh, -, -⟩ := (tied_step_iff Td ft s rs cols).1 ⟨s', n, hs⟩
  obtain ⟨-, -, -, he, -⟩ := Td
  have he' : IM.LaidAlone ProofFile.sameReply blk (K9.closing (Cl := Unit) Q).retype blk.name
      (IM.cAt l (IM.subAt l) 1 KindName.K10) := he
  have hk : (IM.cAt l (IM.subAt l) 1 KindName.K10).kind ≠ KindName.K7 := by
    show KindName.K10 ≠ KindName.K7
    decide
  obtain ⟨h0, hm, -⟩ := (IM.step_alone he' hk ft s s' n rs cols).1 hs
  have h1 : (K9.closing (Cl := Unit) Q).step ft s rs cols = .ok (s', n) :=
    (retype_step _ ft s rs cols).symm.trans h0
  obtain ⟨-, hD, hn⟩ := (VerifiableInference.Desc.step_iff ft _ s s' rs cols n).1 h1
  have g : groupsOf ft (K9.closing (Cl := Unit) Q).rounds (rs.map (·.drawn)) = [] :=
    YesFree.groups_nil ft (entries Q) _
  have hw : (K9.closing (Cl := Unit) Q).want ft rs = [] := by
    unfold Block.want
    rw [g]
    rfl
  have hsn : (K9.closing (Cl := Unit) Q).shown ft rs cols = [] := by
    unfold Block.shown
    rw [g]
    rfl
  rw [hsn] at hD
  rw [hw] at hn
  exact ⟨hl, hsh, hD, hm, hn⟩

/-- **An acceptance of the seated block's step gives `K10Keeps`** between the state before it and the state after it. -/
theorem tied_keeps (Td : Tied c Z l p Q blk) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat}
    (hs : blk.step ft s rs cols = .ok (s', n)) : K10Keeps s s' := by
  obtain ⟨-, -, hD, hm, -⟩ := tied_decides Td hs
  exact ⟨YesFree.closing_turns hD, hm⟩

/-- **The state after the seated block's step is the state that `behind` returns**: the state after the lifted block's
step, without the guards, at first tree 0 and no columns. -/
theorem behind_of_tied (Td : Tied c Z l p Q blk) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {n : Nat} (hs : blk.step ft s rs cols = .ok (s', n)) : LeftIs.Tests.behind Q s rs = some s' := by
  obtain ⟨hl, hsh, hD, -, -⟩ := tied_decides Td hs
  have e := LeftIs.Tests.closing_step_is (Cl := Unit) Q 0 s s' rs [] hl hsh hD
  exact (congrArg (fun x : Except String (S × Nat) => x.toOption.map (·.1)) e :)

/-- **The state after the seated block's step, written out**, where the facts `CloseBase` hold at the record of the
state before it. rB, rE, rR: the rounds without their digests. row: what the batching returns at the element that rB
drew. -/
theorem tied_behind (Td : Tied c Z l p Q blk) {D : BaseData} {ft : Nat} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {n : Nat} (H : CloseBase Q (K9.recOf s) D) (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (row : OnBytes.GroupRow),
      rs.map noDigest = rB :: rE :: rR ∧ (rB :: rE :: rR).length = 2 + Q.k ∧ ShapedAll (rB :: rE :: rR) ∧
        Own.batch (D.S1 (K9.recOf s)) (K9.recOf s).frame.group
          ⟨Own.layoutOf (K9.recOf s).st D.G, OnBytes.Slice.runRows (K9.recOf s).st D.G⟩ (drawnOf rB) = some row ∧
        s' = K9.putRec s ⟨none, { (K9.recOf s).frame with
          rows := foldOutAt (D.S1 (K9.recOf s)) (D.F (K9.recOf s)) row D.m (rE :: rR), mask := none
          link := (K9.recOf s).frame.link + 1, next := .first },
        spent (D.S1 (K9.recOf s)) D.m⟩ := by
  obtain ⟨hl, hsh, hD, -, -⟩ := tied_decides Td hs
  obtain ⟨rB, rE, rR, hr⟩ : ∃ rB rE rR, rs.map noDigest = rB :: rE :: rR := by
    match rs, hsh with
    | a :: b :: t, _ => exact ⟨_, _, _, rfl⟩
  have hl' : (rB :: rE :: rR).length = 2 + Q.k := by rw [← hr, List.length_map, hl]
  have hs' : ShapedAll (rB :: rE :: rR) := hr ▸ YesFree.shapedAll_noDigest hsh
  obtain ⟨row, hrow, hdec⟩ := LeftIs.closing_leaves (Cl := Unit) H rB rE rR [] hl' hs'
  rw [hr] at hD
  exact ⟨rB, rE, rR, row, hr, hl', hs', hrow, Except.ok.inj (hD.symm.trans hdec)⟩

/-- The same with rB, rE, rR the rounds themselves, with their digests. -/
theorem tied_behind_rounds (Td : Tied c Z l p Q blk) {D : BaseData} {ft : Nat} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {n : Nat} (H : CloseBase Q (K9.recOf s) D) (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (row : OnBytes.GroupRow),
      rs = rB :: rE :: rR ∧ (rB :: rE :: rR).length = 2 + Q.k ∧ ShapedAll (rB :: rE :: rR) ∧
        Own.batch (D.S1 (K9.recOf s)) (K9.recOf s).frame.group
          ⟨Own.layoutOf (K9.recOf s).st D.G, OnBytes.Slice.runRows (K9.recOf s).st D.G⟩ (drawnOf rB) = some row ∧
        s' = K9.putRec s ⟨none, { (K9.recOf s).frame with
          rows := foldOutAt (D.S1 (K9.recOf s)) (D.F (K9.recOf s)) row D.m (rE :: rR), mask := none
          link := (K9.recOf s).frame.link + 1, next := .first },
        spent (D.S1 (K9.recOf s)) D.m⟩ := by
  obtain ⟨hl, hsh, -, -, -⟩ := tied_decides Td hs
  obtain ⟨qB, qE, qR, row, hq, -, -, hrow, e⟩ := tied_behind Td H hs
  obtain ⟨rB, rE, rR, hr⟩ : ∃ rB rE rR, rs = rB :: rE :: rR := by
    match rs, hsh with
    | a :: b :: t, _ => exact ⟨_, _, _, rfl⟩
  subst hr
  have hq' : noDigest rB :: List.map noDigest (rE :: rR) = qB :: qE :: qR := hq
  obtain ⟨eB, eT⟩ := List.cons.inj hq'
  have eF := foldOutAt_noDigest (D.S1 (K9.recOf s)) (D.F (K9.recOf s)) row D.m (rE :: rR)
  rw [← eB] at hrow
  rw [← eT] at e
  rw [eF] at e
  exact ⟨rB, rE, rR, row, rfl, hl, hsh, hrow, e⟩

end

/-! ## 3 At a thread's step -/

section
variable {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Q : Par}
  {blk : Block S ProofFile.Cl} (T : Thread Bk S ProofFile.Cl V W X Pb) {k : Coins Bk} {s s' : S} {m : Mid W X} {En : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}

/-- **A thread's step at the closing's block gives `K10Keeps`** between the verifier's states before and after it. -/
theorem stepped_keeps (Td : Tied c Z l p Q blk) (hS : T.Stepped blk k s m En ds y cols s') : K10Keeps s s' :=
  tied_keeps Td hS.2

/-- The verifier's state after a thread's step at the closing's block is the state that `behind` returns at the rounds
as played. -/
theorem stepped_behind_is (Td : Tied c Z l p Q blk) (hS : T.Stepped blk k s m En ds y cols s') :
    LeftIs.Tests.behind Q s (roundsOf y.1) = some s' :=
  behind_of_tied Td hS.2

/-- **The verifier's state after a thread's step at the closing's block, written out**, where the facts `CloseBase` hold
at the record of the state before it. rB, rE, rR: the rounds as played. No column was filled. -/
theorem stepped_behind (Td : Tied c Z l p Q blk) {D : BaseData} (H : CloseBase Q (K9.recOf s) D)
    (hS : T.Stepped blk k s m En ds y cols s') :
    ∃ (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (row : OnBytes.GroupRow),
      roundsOf y.1 = rB :: rE :: rR ∧ (rB :: rE :: rR).length = 2 + Q.k ∧ ShapedAll (rB :: rE :: rR) ∧
        Own.batch (D.S1 (K9.recOf s)) (K9.recOf s).frame.group
          ⟨Own.layoutOf (K9.recOf s).st D.G, OnBytes.Slice.runRows (K9.recOf s).st D.G⟩ (drawnOf rB) = some row ∧
        s' = K9.putRec s ⟨none, { (K9.recOf s).frame with
          rows := foldOutAt (D.S1 (K9.recOf s)) (D.F (K9.recOf s)) row D.m (rE :: rR), mask := none
          link := (K9.recOf s).frame.link + 1, next := .first },
        spent (D.S1 (K9.recOf s)) D.m⟩ ∧
        cols = [] := by
  obtain ⟨rB, rE, rR, row, h1, h2, h3, h4, h5⟩ := tied_behind_rounds Td H hS.2
  obtain ⟨-, -, -, -, hn⟩ := tied_decides Td hS.2
  exact ⟨rB, rE, rR, row, h1, h2, h3, h4, h5, List.eq_nil_of_length_eq_zero hn⟩

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.drawnOf_noDigest
#print axioms ProofFile.Honest.K10.sentOf_noDigest
#print axioms ProofFile.Honest.K10.drawn_noDigest
#print axioms ProofFile.Honest.K10.claimOf_noDigest
#print axioms ProofFile.Honest.K10.foldOutAt_noDigest
#print axioms ProofFile.Honest.K10.tied_decides
#print axioms ProofFile.Honest.K10.tied_keeps
#print axioms ProofFile.Honest.K10.behind_of_tied
#print axioms ProofFile.Honest.K10.tied_behind
#print axioms ProofFile.Honest.K10.tied_behind_rounds
#print axioms ProofFile.Honest.K10.stepped_keeps
#print axioms ProofFile.Honest.K10.stepped_behind_is
#print axioms ProofFile.Honest.K10.stepped_behind
