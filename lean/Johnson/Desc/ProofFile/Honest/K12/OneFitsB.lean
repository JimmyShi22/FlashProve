-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OneFitsB.lean: the public clauses of a job made of a sending
(`OneFits`, JobOne.lean in this folder) as one test with code, on the sending's public data and on
the shape of the test's plain data (`PlainS`, Johnson/Desc/K12/Honest/Shape/TestDoor.lean), which
holds no field element; and so `DataFront`'s first three clauses (ShapeAll.lean) from that test. The
test is `oneFitsB`, a function with values in Bool. It has every clause of `OneFits` but one,
`layout`: "the layout is the state's". Where the test is true and that clause holds, `OneFits` holds
(`oneFits_of_B`), and so do the three clauses at the job `jobOne` (`three_of_B`). General in the
test's place p, in what is taken of the sending, Q, in the plain data Dp and in the job's function
`rec₀`. Two definitions with code, and four theorems with their proofs.

In the list: a job (`TestJob`, Test.lean in this folder) is what a caller supplies for its proximity
test. A sending is the sub-protocol of the kind K1, which sends oracle messages. `jobOne p Q rec₀`
(JobOne.lean) is the job made of a sending: the group under test has one member, message number 0 of
the sending, and the first fold's fresh table is message number 1 of the same sender. `rec₀` gives
the state on entry to the test. Q (`OneSent`, JobOne.lean) is what is taken of the sending; P, in
the theorems `Q.P` (`K1.Par`, Johnson/Desc/K1/Send.lean), is its public data, with the codes
`P.codes` and the list of messages `P.sent`. p (`P12`, Johnson/Desc/K12/Frame.lean) holds the
numbers of the test's place. `stA p` (PlanB.lean in this folder) is its first stage
(`Fmt.M1.Stage`), with the numbers k and h, the main code C and the mask code Z; `kk` of a stage is
h + (k - h) (Johnson/Desc/K12/Law/FirstOk.lean). Dp (`Plain`, FirstOk.lean) are the plain data of
the group under test: a statement, a book of trees `book` (`TreeBook`, OnBytes/Iop/Ground.lean), the
layout `L` (`GroupLayout`, Ground.lean), the members `mems`, the fresh table `fresh`, the places
`ts` of their trees in the book, and the declared openings. `PlainS` is `Plain` with the statement's
codes in place of the statement, and the book's shape (`BookSh`,
Johnson/Desc/Ground/Shape/Core.lean) in place of the book; `plainSh` (TestDoor.lean) maps `Plain` to
`PlainS`. A seat (`Seat1`, FirstOk.lean) is an oracle message as a part of a tree; each member and
the fresh table is a seat. Ly (`TreeLay`, Ground.lean) says how the oracle messages of one sending
are placed in trees. t₀ is a state (`T12`, Johnson/Desc/K12/Join.lean); `layoutAt t₀` (JobOne.lean)
is the layout of its group under test, an empty one where there is no such group. w is the prover's
input, fr what precedes the test (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean), C the coins that
`testAll` reads (`TestCoins`, Test.lean).

  `oneFits_of_B`: if the test is true at the shape of the plain data, and the layout is the state's,
    then there are the seat s, the tree's place u in the book and the sending's layout Ly, and
    `OneFits` holds. In Lean: from `oneFitsB p Q.P (plainSh Dp) = true` and `Dp.L = layoutAt t₀`
    follows `∃ s u Ly, OneFits p Q t₀ Dp s u Ly`
  `three_of_B`: under the same two hypotheses, with `rec₀ w fr` for t₀, at every C: the fields
    `cols`, `state` and `trees` of `DataFront`, in this order, at `jobOne p Q rec₀`. Write Pst for
    the first stage's state `(jobOne p Q rec₀).first w fr C` (Test.lean), T for the job's list of
    trees `trees₀ w fr C.mem Pst`, c for `colsFrom T Dp.ts` (Johnson/Desc/K12/Honest/FirstAsks.lean)
    and R for `plainOne Q w (C.mem 0) Pst` (JobOne.lean). Then `ColsAt (stA p) Dp c R`
    (Johnson/Desc/K12/Honest/FirstRows.lean) holds, `StateAt (stA p) Dp Pst R`
    (Johnson/Desc/K12/Honest/FirstState.lean) holds, and the job's trees are the group's: T is
    `groupTrees Dp.ts (logAt Dp.book) c` (Johnson/Desc/K12/Honest/GroupState.lean)
  `oneFitsB p P D`: a definition: the test: all clauses of `OneFits` but "the layout is the
    state's". It is false unless `D.mems` is one seat s, `D.ts` is one place u, and `layTrees`
    (Ground.lean) returns a layout Ly at `P.codes` and `P.sent`. There it is true where all of these
    hold. P passes `K1.planOkOwn` (Johnson/Desc/K1/Own.lean). The sending has more than one message.
    `seatIsB` is true at the first stage for message 0 and s, and for message 1 and `D.fresh`. Ly
    states the tree 0 for both messages (read by `getD`, which gives 0 also where Ly has no entry).
    Ly has the shape of at least one tree. The tree of each of the two seats is at the place u.
    `D.fresh` has 2 ^ h mask rows. `oM D.L 0` plus the number of main rows of s is at most 2 ^
    `kk (stA p)`, and `oZ D.L 0` plus its number of mask rows at most 2 ^ h (`oM`, `oZ`,
    FirstOk.lean: the first rows that the layout states for a member). The depth and the width of
    the book's shape at u (`logAtS`, `widthAtS`, TestDoor.lean; 0 where it has no tree at u) are
    `logN` of the sending's tree number 0 (`K1.Par.trees`, Send.lean), and the main width plus the
    mask width of shape number 0 of Ly
  `oneFitsB_congr`: the test reads of the sending's public data the codes and the list of messages
    only. In Lean: where `P.codes = P'.codes` and `P.sent = P'.sent`, `oneFitsB p P D` is
    `oneFitsB p P' D`
  `seatIsB a P Ly k s`: a definition: `SeatIs` (Johnson/Desc/K12/Honest/SentMember.lean: the seat s
    is message number k of the sending) as a test: its six fields in their order, each by `decide`.
    For the two fields of the form "where the seat has such rows, their code is the stage's" it has
    "the number of such rows is 0, or their code is the stage's"
  `seatIs_of_B`: where `seatIsB a P Ly k s` is true, `SeatIs a P Ly k s` holds

By what. `seatIs_of_B` and `oneFits_of_B` unfold the tests and turn `&&`, `||` and `decide` into
propositions by `simp only`. In `oneFits_of_B` the fields `mems` and `ts` of `plainSh Dp` are those
of Dp by `rfl`; the match gives the clauses `mems`, `ts` and `lay`; `seatIs_of_B` gives the two on
the seats; `logAtS_eq` and `widthAtS_eq` (TestDoor.lean) carry the depth and the width over from the
book's shape to the book. `oneFitsB_congr` unfolds the test, `seatIsB` and `K1.planOkOwn` down to
`K1.planOk`, `K1.Par.tuple`, `K1.Par.trees` (Send.lean) and `shapeAt`
(Johnson/Prover/Send/Core.lean), and rewrites by its two hypotheses. `three_of_B` is `oneFits_of_B`
with `cols_one`, `state_one` and `trees_one` (JobOne.lean).

Hypotheses of `oneFits_of_B` and `three_of_B`. h: the test is true at p, `Q.P` and `plainSh Dp`. hL:
`Dp.L` is `layoutAt t₀`; in `three_of_B`, `layoutAt (rec₀ w fr)`.

Limits.
- That the test is true is shown at no place here. `plain_at_KR` (FrontPlainAtKey.lean in this
  folder) gives plain data at which it is true, at one written place, thin shape and sending.
- "The layout is the state's" is a hypothesis (hL): it holds wherever the plain data are made at the
  layout of the group under test. That is not shown in this file; `frontPlain_of_B`
  (FrontPlainB.lean in this folder) concludes it for the plain data that it gives.
- The limits of JobOne.lean hold here too. Among them: one member, one tree; a group of several
  members is not covered. The last clause of `DataFront` (`allSay`) is not shown and not used, so
  `DataFront` is shown at no value here.
- `rec₀` and t₀ are free parameters. t₀ and the values of `rec₀` have the type of the verifier's
  state inside a test (`T12`); nothing here shows that they are the verifier's state.
- "Public" is said of the test by its arguments: p, P and the shape D. The hypothesis hL is not of
  that kind: in `three_of_B` it is at `rec₀ w fr`, so it reads the prover's input w and the front
  fr, through `rec₀`. Dp is a free parameter: it is not stated to be a function of public data.
- Only the direction from a test to its clauses is proved: where `oneFitsB` or `seatIsB` is false,
  nothing is stated.
- The test asks that the sending has more than one message, not that it has two. `OneSent.rows`
  (JobOne.lean) gives the fresh table's rows to every message number from 1 on. So at a sending with
  a third message in tree 0 that has mask rows, the job's column (`col`,
  Johnson/Prover/Send/Core.lean) holds symbols of the fresh table's rows a second time; `three_of_B`
  covers such a sending all the same, wherever its hypotheses hold. `same_one` (SameAtOne.lean in
  this folder) has the hypothesis `Q.P.sent.size = 2`.
- The test takes of Q the field `P` only. It reads nothing of what rides (`Q.ride`): neither that
  `Q.ride 1` holds the first stage's two numbers, nor anything of `Q.ride 0`, which enters the count
  of coins in the job's `members` and the member's rows `Q.mem`. The first is a hypothesis
  elsewhere: the field `ride` of `BookTies` (CoinsTieBook.lean in this folder), and hR of
  `same_one`.
- The test asks neither that the fresh table's seat has no main rows, nor that a mask row's message
  has room for the packing. At a message 1 with main rows, `OneSent.rows` gives 0 for these rows and
  for their tails. Without the room, the fresh table's rows in the first stage's state (`fM`) are 0
  everywhere (`packedN`, Johnson/Prover/Link/BodyPack.lean). Both are clauses or hypotheses
  elsewhere: the clause "f:main" of `gpL` (FirstOk.lean), the clause "room" of `planL` (PlanB.lean),
  and hm and hl of `same_one`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.JobOne
import Johnson.Desc.K12.Honest.Shape.TestDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.Sh (PlainS plainSh logAtS widthAtS logAtS_eq widthAtS_eq)

variable {W X : Type}

/-- `SeatIs` (Johnson/Desc/K12/Honest/SentMember.lean) as a test: its six fields, in their
order. -/
def seatIsB (a : Fmt.M1.Stage) (P : K1.Par) (Ly : TreeLay) (k : ℕ) (s : Seat1) : Bool :=
  decide (s.sh = shapeAt P k) && decide (s.tsh = Ly.shapes.getD (Ly.tree.getD k 0) {}) &&
  decide (s.part = Ly.part.getD k 0) && (decide (s.sh.mainDeg = 1) || decide (s.sh.mainDeg = 3)) &&
  (decide (s.sh.mainRows = 0) || decide (codeOf (P.codes.base.getD s.sh.code default) = a.C)) &&
  (decide (s.sh.maskRows = 0) || decide (codeOf (P.codes.mask.getD s.sh.maskCode default) = a.Z))

theorem seatIs_of_B {a : Fmt.M1.Stage} {P : K1.Par} {Ly : TreeLay} {k : ℕ} {s : Seat1}
    (h : seatIsB a P Ly k s = true) : SeatIs a P Ly k s := by
  unfold seatIsB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, fun hp => h5.resolve_left (Nat.ne_of_gt hp),
    fun hp => h6.resolve_left (Nat.ne_of_gt hp)⟩

/-- All clauses of `OneFits` but "the layout is the state's" (the field `layout`). False unless D
has one member and one tree's place, and `layTrees` returns a layout. -/
def oneFitsB (p : P12) (P : K1.Par) (D : PlainS) : Bool :=
  match D.mems, D.ts, layTrees P.codes P.sent with
  | [s], [u], some Ly =>
    K1.planOkOwn P && decide (1 < P.sent.size) && seatIsB (stA p) P Ly 0 s &&
    seatIsB (stA p) P Ly 1 D.fresh && decide (Ly.tree.getD 0 0 = 0) &&
    decide (Ly.tree.getD 1 0 = 0) && decide (0 < Ly.shapes.size) && decide (s.t = u) &&
    decide (D.fresh.t = u) && decide (D.fresh.sh.maskRows = 2 ^ (stA p).h) &&
    decide (oM D.L 0 + s.sh.mainRows ≤ 2 ^ kk (stA p)) &&
    decide (oZ D.L 0 + s.sh.maskRows ≤ 2 ^ (stA p).h) &&
    decide (logAtS D.book u = (P.trees.getD 0 {}).logN) &&
    decide (widthAtS D.book u = (Ly.shapes.getD 0 {}).mainWidth + (Ly.shapes.getD 0 {}).maskWidth)
  | _, _, _ => false

/-- The test reads of the sending's public data its codes and its list of messages only. -/
theorem oneFitsB_congr (p : P12) (P P' : K1.Par) (D : PlainS) (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) : oneFitsB p P D = oneFitsB p P' D := by
  unfold oneFitsB seatIsB K1.planOkOwn K1.planOk K1.Par.tuple K1.Par.trees shapeAt
  rw [hc, hs]

/-- **The test's "true" gives the public clauses.** h: the test is true at the shape of the plain
data. hL: the layout is the state's. t₀: a state, a free parameter. -/
theorem oneFits_of_B (p : P12) (Q : OneSent W) (t₀ : T12) (Dp : Plain)
    (h : oneFitsB p Q.P (plainSh Dp) = true) (hL : Dp.L = layoutAt t₀) :
    ∃ s u Ly, OneFits p Q t₀ Dp s u Ly := by
  unfold oneFitsB at h
  have em : (plainSh Dp).mems = Dp.mems := rfl
  have et : (plainSh Dp).ts = Dp.ts := rfl
  rw [em, et] at h
  split at h
  · rename_i s u Ly hm ht hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩,
      a14⟩ := h
    have b13 : logAt Dp.book u = (Q.P.trees.getD 0 {}).logN := (logAtS_eq Dp.book u).symm.trans a13
    have b14 : widthAt Dp.book u =
        (Ly.shapes.getD 0 {}).mainWidth + (Ly.shapes.getD 0 {}).maskWidth :=
      (widthAtS_eq Dp.book u).symm.trans a14
    exact ⟨s, u, Ly, a1, hl, a2, hm, ht, seatIs_of_B a3, seatIs_of_B a4, a5, a6, a7, a8, a9, a10,
      hL, a11, a12, b13, b14⟩
  · cases h

/-- **The first three clauses of `DataFront`, at the job made of the sending.** In the order `cols`,
`state`, `trees`. rec₀: the state on entry to the test, of the type of the verifier's state inside a
test; a free parameter, not shown to be the verifier's. -/
theorem three_of_B (p : P12) (Q : OneSent W) (rec₀ : W → Front X → T12) (w : W) (fr : Front X)
    (C : TestCoins) (Dp : Plain) (h : oneFitsB p Q.P (plainSh Dp) = true)
    (hL : Dp.L = layoutAt (rec₀ w fr)) :
    ColsAt (stA p) Dp
        (colsFrom ((jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C)) Dp.ts)
        (plainOne Q w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) ∧
      StateAt (stA p) Dp ((jobOne p Q rec₀).first w fr C)
        (plainOne Q w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) ∧
      (jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C) =
        groupTrees Dp.ts (logAt Dp.book)
          (colsFrom ((jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C))
            Dp.ts) := by
  obtain ⟨s, u, Ly, H⟩ := oneFits_of_B p Q (rec₀ w fr) Dp h hL
  exact ⟨cols_one p Q rec₀ w fr C H, state_one p Q rec₀ w fr C H, trees_one p Q rec₀ w fr C H⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.seatIs_of_B
#print axioms ProofFile.Honest.K12.oneFitsB_congr
#print axioms ProofFile.Honest.K12.oneFits_of_B
#print axioms ProofFile.Honest.K12.three_of_B
#print axioms ProofFile.Honest.K12.seatIsB
#print axioms ProofFile.Honest.K12.oneFitsB
