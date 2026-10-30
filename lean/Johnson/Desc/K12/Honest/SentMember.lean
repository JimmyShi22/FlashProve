-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/SentMember.lean: two theorems on the written column of a sending (`col`,
Johnson/Prover/Send/Core.lean). A sending is the sub-protocol that sends oracle messages (the kind
K1, Johnson/Desc/K1/Own.lean); the prover's side of it writes, for each of its trees and each
position, a column of words from the rows that its caller hands. `hy_atFirst_rows`
(Johnson/Desc/K12/Honest/FirstRows.lean), the theorem on what the first code switch of a proximity
test reads, assumes `ColsAt` of the prover's data, a structure of three fields. For one seat of the
test that is a message of a sending, the two theorems prove, at the sending's column, what two of
the three fields say of that seat: `MemAt`, which the field `mem` states at every member's seat, and
the equation of the field `fresh` on the fresh table. General in the stage, the place of the
sending, the rows, the message's number, the seat and the position, under the hypotheses below. A
definition, and theorems with their proofs. It does not depend on the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list and below: a (`Fmt.M1.Stage`) is a stage of the test, `a.C` the code of a main row,
`a.Z` the code of a mask row. A code (`Fmt.M1.Code`) has three numbers a, l and r: code words of
length 2 ^ a, messages of l entries and tails of r entries. P (`K1.Par`, Johnson/Desc/K1/Send.lean)
holds the numbers of the place of the sending, `P.sent` its messages in the order of sending;
`shapeAt P k` (Core.lean) is the shape of message number k. V k (`Rows`, Core.lean) holds the rows
that the caller hands of message number k. Ly (`TreeLay`, OnBytes/Iop/Ground.lean) is the sending's
layout: for each message its tree and its part of that tree, and the trees' shapes. The test's plain
data (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean) hold a book (`TreeBook`, Ground.lean: the trees,
and for each oracle message its tree and its part of that tree) and a seat for each member of the
group under test and for the fresh table. A seat s (`Seat1`, FirstOk.lean) is an oracle message as a
part of a tree: its shape `sh`, its tree's place `t` in the book and shape `tsh`, and the number
`part` of its part. `skM s.tsh s.part` and `skZ s.tsh s.part` (FirstOk.lean) are the numbers of the
words at which the main symbols and the mask symbols of the seat's part begin in a column. R
(`PlainRows`, FirstRows.lean) holds the prover's rows as plain functions of numbers. A row's symbol
at a position is `symG` (Johnson/Prover/Link/Base.lean) of the row's code, the position, the row's
message and its tail. `read3` (Johnson/Desc/K12/Honest/Written.lean) reads three words of a column
as an element of the extension field.

  `sent_memAt`: under `SeatIs`, if the plain rows of member j are the rows that the sending's caller
    handed of message k, below the codes' lengths, then `MemAt` holds at the sending's column, at
    every position. In Lean: `MemAt a (col P V (Ly.tree.getD k 0) x) R s j x`, for every R, j and x;
    x is any number
  `sent_freshAt`: the like for a fresh table that a sending has sent as a message of mask rows
    alone. In Lean: for every R, every x and every b below `s.sh.maskRows`, `read3` of the column
    `col P V (Ly.tree.getD k 0) x` at word `skZ s.tsh s.part + 3 * b` is
    `symG a.Z (x % 2 ^ a.Z.a) (R.F b) (R.FT b)`. That is the equation in the field `fresh` of
    `ColsAt`
  `SeatIs a P Ly k s`: a seat of the test's plain data is message number k of a sending: its shape
    is the message's; its tree's shape and its part are the sending's layout's; where it has main
    rows, their code is the stage's; where it has mask rows, theirs is the stage's mask code. In
    Lean, a structure of six fields, a proposition. `shape`: `s.sh = shapeAt P k`. `tree`: `s.tsh`
    is the entry of `Ly.shapes` at the number `Ly.tree.getD k 0`. `part`:
    `s.part = Ly.part.getD k 0`. `deg`: `s.sh.mainDeg` is 1 or 3. `codeM`: where `s.sh.mainRows` is
    above 0, `codeOf` (OnBytes/Slice/ProgCodes.lean) of the entry of `P.codes.base` at the number
    `s.sh.code` is `a.C`. `codeZ`: where `s.sh.maskRows` is above 0, `codeOf` of the entry of
    `P.codes.mask` at the number `s.sh.maskCode` is `a.Z`

By what. Both proofs first put the sending's rows in the place of the plain rows by `symG_congr`
(Base.lean), which asks that they agree below the code's l and r. `sent_memAt` then calls, for the
main rows, `sent_main1` or `sent_main3`, as the field `deg` says, and for the mask rows `sent_mask`;
`sent_freshAt` calls `sent_mask` (all three: Johnson/Desc/K12/Honest/SentCols.lean). Their
statements are rewritten by the fields of `SeatIs`. They have `skipMain` and `skipMask`
(Johnson/Prover/Send/Front.lean) where `MemAt` has `skM` and `skZ`; the two pairs agree by
unfolding.

Hypotheses. The first four are those of both theorems.
  hP: `K1.planOkOwn P = true` (Johnson/Desc/K1/Own.lean): the place passes its own test on the plan
  hL: `layTrees P.codes P.sent` (Ground.lean) returns Ly
  hk: k is below `P.sent.size`
  hS: `SeatIs a P Ly k s`
  hM, hT (`sent_memAt`): for every i below `s.sh.mainRows`, `R.M j i` agrees below `a.C.l` with main
    row i of V k, and `R.T j i` below `a.C.r` with that row's tail. The row and its tail are read by
    `Rows.main` (Core.lean) and `Rows.mainTl` (Front.lean): over the extension field where
    `s.sh.mainDeg` is 3, else over the base field and taken into the extension field
  hZ, hZT (`sent_memAt`): for every i below `s.sh.maskRows`, `R.Z j i` agrees below `a.Z.l` with
    `(V k).mask i`, and `R.ZT j i` below `a.Z.r` with `(V k).maskTl i`
  hb, hF, hFT (`sent_freshAt`): b is below `s.sh.maskRows`; `R.F b` agrees below `a.Z.l` with
    `(V k).mask b`, and `R.FT b` below `a.Z.r` with `(V k).maskTl b`

Limits.
- `SeatIs` is a hypothesis: that the book before the test states what the sending's layout stated is
  not shown here.
- No value that meets `SeatIs` is given in this file.
- No clause of `SeatIs` says at which place of the book the sending's tree is: the seat's fields
  `t`, `id` and `num` are in no clause. `ColsAt` speaks of the column of the tree at the seat's
  place `t`; that this column is the sending's column is not shown here.
- `SeatIs` reads `Ly.tree`, `Ly.part`, `Ly.shapes`, `P.codes.base` and `P.codes.mask` with a default
  value where there is no such entry, and `shapeAt` does the same with `P.sent`. It has no clause
  that k is below `P.sent.size`; that is hk of the two theorems.
- The field `width` of `ColsAt`, on the columns' width, is not proved here.
- `sent_freshAt` speaks of the rows b below `s.sh.maskRows`, the field `fresh` of `ColsAt` of the
  rows b below `2 ^ a.h`. That the two numbers agree is no clause of `SeatIs` and is not shown here.
  Neither `sent_freshAt` nor `SeatIs` asks that the message has no main row.
- The hypotheses on the rows (hM, hT, hZ, hZT, hF, hFT) are hypotheses on the prover's data; they
  are not shown here.
- No other file of this folder calls these two theorems.
- The place passes its own test on the plan: both theorems have that as the hypothesis hP.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.SentCols
import Johnson.Desc.K12.Honest.FirstRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Cb VerifiableInference.Desc
open H2K.First (Seat1 skM skZ)
open Johnson.Prover.Link (symG symG_congr)
open Johnson.Prover.Send

/-- A seat of the test's plain data is message number k of a sending. a: the stage. P: the numbers
of the sending's place. Ly: the sending's layout. s: the seat. -/
structure SeatIs (a : Fmt.M1.Stage) (P : K1.Par) (Ly : TreeLay) (k : ℕ) (s : Seat1) : Prop where
  shape : s.sh = shapeAt P k
  tree : s.tsh = Ly.shapes.getD (Ly.tree.getD k 0) {}
  part : s.part = Ly.part.getD k 0
  deg : s.sh.mainDeg = 1 ∨ s.sh.mainDeg = 3
  codeM : 0 < s.sh.mainRows → codeOf (P.codes.base.getD s.sh.code default) = a.C
  codeZ : 0 < s.sh.maskRows → codeOf (P.codes.mask.getD s.sh.maskCode default) = a.Z

section
variable {a : Fmt.M1.Stage} (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (Ly : TreeLay)
  (hL : layTrees P.codes P.sent = some Ly) (k : ℕ) (hk : k < P.sent.size) {s : Seat1}
  (hS : SeatIs a P Ly k s)
include hP hL hk hS

/-- **A sending's column holds a member's rows' symbols at the member's seat.** -/
theorem sent_memAt (R : PlainRows) (j x : ℕ)
    (hM : ∀ i e, i < s.sh.mainRows → e < a.C.l →
      R.M j i e = (V k).main (s.sh.mainDeg == 3) i e)
    (hT : ∀ i q, i < s.sh.mainRows → q < a.C.r →
      R.T j i q = (V k).mainTl (s.sh.mainDeg == 3) i q)
    (hZ : ∀ i e, i < s.sh.maskRows → e < a.Z.l → R.Z j i e = (V k).mask i e)
    (hZT : ∀ i q, i < s.sh.maskRows → q < a.Z.r → R.ZT j i q = (V k).maskTl i q) :
    MemAt a (col P V (Ly.tree.getD k 0) x) R s j x := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hC := hS.codeM (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)
    have hi' : i < (shapeAt P k).mainRows := by rw [← hS.shape]; exact hi
    rw [symG_congr a.C x _ _ _ _ (fun e he => hM i e hi he) fun q hq => hT i q hi hq]
    rcases hS.deg with h1 | h3
    · have h1' : (shapeAt P k).mainDeg = 1 := by rw [← hS.shape]; exact h1
      have e := sent_main1 P V hP Ly hL k x hk h1' i hi'
      rw [← hS.shape, hC, ← hS.tree, ← hS.part] at e
      rw [h1]
      exact e
    · have h3' : (shapeAt P k).mainDeg = 3 := by rw [← hS.shape]; exact h3
      have e := sent_main3 P V hP Ly hL k x hk h3' i hi'
      rw [← hS.shape, hC, ← hS.tree, ← hS.part] at e
      rw [h3]
      exact e
  · have hZc := hS.codeZ (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)
    have hi' : i < (shapeAt P k).maskRows := by rw [← hS.shape]; exact hi
    rw [symG_congr a.Z _ _ _ _ _ (fun e he => hZ i e hi he) fun q hq => hZT i q hi hq]
    have e := sent_mask P V hP Ly hL k x hk i hi'
    rw [← hS.shape, hZc, ← hS.tree, ← hS.part] at e
    exact e

/-- **A sending's column holds a fresh table's rows' symbols at the table's seat.** -/
theorem sent_freshAt (R : PlainRows) (x b : ℕ) (hb : b < s.sh.maskRows)
    (hF : ∀ e, e < a.Z.l → R.F b e = (V k).mask b e)
    (hFT : ∀ q, q < a.Z.r → R.FT b q = (V k).maskTl b q) :
    read3 (col P V (Ly.tree.getD k 0) x) (skZ s.tsh s.part + 3 * b) =
      symG a.Z (x % 2 ^ a.Z.a) (R.F b) (R.FT b) := by
  have hZc := hS.codeZ (Nat.lt_of_le_of_lt (Nat.zero_le _) hb)
  have hb' : b < (shapeAt P k).maskRows := by rw [← hS.shape]; exact hb
  rw [symG_congr a.Z _ _ _ _ _ hF hFT]
  have e := sent_mask P V hP Ly hL k x hk b hb'
  rw [← hS.shape, hZc, ← hS.tree, ← hS.part] at e
  exact e

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.sent_memAt
#print axioms ProofFile.Honest.K12.sent_freshAt
#print axioms ProofFile.Honest.K12.SeatIs
