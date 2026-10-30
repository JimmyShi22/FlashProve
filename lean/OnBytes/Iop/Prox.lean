-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Prox.lean: the proximity test on a group, from its open rows to the verifier's yes or
no, and its last step, the block BASE.
C++ counterparts: blocks/iop/iopp.h (the stages), blocks/iop/base_case.h (BASE).

   BAT                   all open rows of the group and the sample rows of all its oracle messages
                         into one claim
   for each stage except the last:
     FOLD                the stage's 2^k main rows and 2^h mask rows into three single rows
     CS                  these rows into one new oracle message under shorter codes: the next stage
   BASE                  the last stage is one main row and one mask row: they are shown, masked,
                         and compared

BASE starts from a complex of single rows (SingleRows, OnBytes/Iop/Fold.lean) without kept rows,
with messages M, encoding randomness R and one linear claim <c, M> = target. It ends the test.
   prover    a masking oracle of the same shape (unless it came with an earlier message), with
             messages M* and randomness R* that the prover chooses; and target* = <c, M*>
   verifier  lambda                                                 round "BASE lambda"
   prover    M' = M* + lambda M and R' = R* + lambda R, in the clear: the messages row by row, then
             the randomness row by row
   verifier  a list of positions                                    round "BASE"
Tests: <c, M'> = target* + lambda target; at every listed position and for every row, the encoding
of (M', R') there equals the masking oracle's symbol + lambda times the row's symbol. These two are
the protocol's own tests in a proximity test.

The masking oracle has rows of its own and gets no out-of-domain sample. It is read at BASE's own
list of positions and at no other, so its class of leaves must be one that is read at that list
only. It serves one BASE (Blk.spendAsMask).

When the masks are sent is a setting (IoppChoice.masksRide). By default FOLD's fresh mask and BASE's
masking oracle come in their block's first message. With masksRide, those of the stages from the
second on come earlier, in the prover's message of the switch that makes their stage. There they are
read at the same list as the stage's oracle message and at no other, so they may share its tree.

What is not asked here. The C++ channel compares the codes and numbers of rows on which a stage runs
with those from which the plan's errors were computed (require_group, require_codes). An entry of a
plan (Fmt.Entry) does not hold these numbers, so the comparison is not made. Params.configure sizes
the shapes, the stages among them, from the configuration files' numbers (Params.sized) and makes
the plans from these shapes. No theorem says that a plan's errors are those of the stages that run.

Words. An oracle is short for an oracle message (OnBytes/Iop/Ground.lean). CS is the code switch
(OnBytes/Iop/Cs.lean). In names, iopp stands for the proximity test (interactive oracle proof of
proximity).

Not claimed here: soundness or hiding. No theorem is stated here.

Main definitions: baseMaskNotice, baseVerify, stageOk, ioppOk, ioppFoldShape, ioppLastRows,
ioppStagesVerify, ioppVerify.
-/
import OnBytes.Iop.Cs
import OnBytes.Params.Items

namespace OnBytes

open Params (IoppStage IoppChoice)

/-! ## BASE -/

/-- The masking oracle as it is announced: one main row over the extension field and as many mask
rows as the complex has, no sample. -/
def baseMaskNotice (code maskCode masks leafClass : Nat) : OracleNotice :=
  { shape := { code := code, mainRows := 1, mainDeg := 3, maskCode := maskCode, maskRows := masks,
               answers := 0 },
    leafClass := leafClass }

/-- The complex has no kept rows and, if it has mask rows, its mask code is not longer than its main
code. The oracle that was named as the masking oracle has one row for each row of the complex under
the same codes, is none of the complex's oracles and has no sample. -/
def baseShapeOk (S : Statement) (R : SingleRows) (star : Nat) : Bool :=
  match S.oracles[star]? with
  | none => false
  | some o =>
    R.keptRows == 0 && R.kept.isEmpty &&
    (R.masks == 0 ||
      maskFits (S.codes.base.getD R.code default) (S.codes.mask.getD R.maskCode default)) &&
    o.shape.mainRows == 1 && o.shape.mainDeg == 3 && o.shape.code == R.code &&
    o.shape.maskRows == R.masks && (R.masks == 0 || o.shape.maskCode == R.maskCode) &&
    !o.sampled && o.shape.answers == 0 && !(singleRowsOracles R).contains star

/-- Receives one vector of the extension field for each length. -/
def recvVectors : List Nat → Blk (List (Array E))
  | [] => pure []
  | n :: ns => do
    let v ← Blk.recvEsInto n #[]
    let vs ← recvVectors ns
    pure (v :: vs)

/-- The name of BASE's first test. -/
def baseLinearName : String := "BASE: the linear claim"

/-- The name of BASE's second test. -/
def basePositionsName : String := "BASE: the symbols at the positions"

/-- The names of the two named tests on values that a proximity test makes (Blk.check). The two
unnamed conditions on values (Blk.test: no seed's factor is 0, no row reads a pad) are not in this
list. -/
def proxNames : List String := [baseLinearName, basePositionsName]

/-- BASE. mask: the number of the masking oracle, if it came in an earlier message; otherwise its
root is received here, under the class of leaves leafClass. -/
def baseVerify (R : SingleRows) (mask : Option Nat) (leafClass : Nat) : Blk Unit := do
  let S0 ← Blk.statement
  let code ← Blk.get S0.codes.base[R.code]?
  let star ← match mask with
    | some id => pure id
    | none => do
      let got ← Blk.receiveOracles #[baseMaskNotice R.code R.maskCode R.masks leafClass]
      Blk.get got[0]?
  let S ← Blk.statement
  Blk.must (baseShapeOk S R star)
  Blk.spendAsMask star
  let targetStar ← Blk.recvE
  let lam ← Blk.closeOne "BASE lambda"
  let zk := S.codes.mask.getD R.maskCode default
  Blk.must (R.masks == 0 || decide (R.maskCode < S.codes.mask.size))
  let codeOf (j : Nat) : Code := if j == 0 then code else zk
  let m ← recvVectors ((List.range R.rows).map fun j => (codeOf j).ell)
  let r ← recvVectors ((List.range R.rows).map fun j => (codeOf j).r)
  Blk.testOnView fun _ =>
    R.c.fits (ceilLog2 code.ell) && R.d.size == R.masks && R.d.all (·.size == zk.ell)
  let left ← Blk.onView zeroE fun _ => (List.range R.masks).foldl (fun s j =>
    addE s (inner (R.d.getD j #[]) (m.getD (1 + j) #[])))
    (R.c.dot (ceilLog2 code.ell) (m.getD 0 #[]))
  let right := maddE targetStar lam R.target
  Blk.note "BASE: left side of the linear check" left
  Blk.note "BASE: right side of the linear check" right
  Blk.check baseLinearName (left == right)
  let (pos, more) ← Blk.closePositions "BASE" code.logN
  Blk.must more.isEmpty
  let opened ← Blk.readOpened ((singleRowsOracles R).push star) pos
  let y ← Blk.get (singleRowsSymbols R opened pos.all.size)
  let stars ← Blk.get opened.back?
  Blk.checkOnView basePositionsName fun _ =>
   (List.range pos.all.size).all fun i =>
    let col := stars.getD i {}
    let at0 := pos.all.getD i 0
    (List.range R.rows).all fun j =>
      let cj := codeOf j
      let x := if j == 0 then at0 else shortPosition cj.logN at0
      let shown := if j == 0 then col.main.getD 0 zeroE else col.mask.getD (j - 1) zeroE
      let masked := maddE shown lam (y.getD (i * R.rows + j) zeroE)
      symbolAt cj x (m.getD j #[]) (r.getD j #[]) == masked

/-! ## The stages -/

/-- The conditions on a stage by itself: not too many row variables, and no more mask rows than main
rows. -/
def stageOk (s : IoppStage) : Bool := decide (s.k ≤ mostLogN) && decide (s.h ≤ s.k)

/-- The conditions on one stage, given the stage before it (nothing for the first) and whether it is
the last. -/
def ioppStageOk (codes : Codes) (answers : Nat) (before : Option IoppStage) (s : IoppStage)
    (last : Bool) : Bool :=
  match codes.base[s.code]?, codes.mask[s.maskCode]? with
  | some c, some zk =>
    c.ok && zk.ok && powerOfTwo c.ell && powerOfTwo zk.ell && maskFits c zk && stageOk s &&
    (if last then s.k == 0
     else decide (1 ≤ s.k) && decide (foldMaskColumns s.k s.h ≤ zk.ell)) &&
    (match before with
      | none => true
      | some p =>
        let pc := codes.base.getD p.code default
        let pzk := codes.mask.getD p.maskCode default
        c.ell * 2 ^ s.k == pc.ell &&
        decide (2 * pzk.ell + pc.r + 2 * pzk.r + answers ≤ zk.ell * 2 ^ s.h) &&
        decide (answers ≤ zk.ell))
  | _, _ => false

/-- The conditions on a list of consecutive stages, given the stage before the first of them
(nothing if the list begins with the first stage). -/
def ioppStagesOk (codes : Codes) (answers : Nat) : Option IoppStage → List IoppStage → Bool
  | _, [] => true
  | before, s :: rest =>
    ioppStageOk codes answers before s rest.isEmpty && ioppStagesOk codes answers (some s) rest

/-- True if the sizes of a proximity test's stages fit together. l and r are the message length and
the random tail of a stage's main code, l_zk and r_zk those of its mask code. From a stage to the
next (primed):
l = 2^k' l' (the folded main message fills the next main rows exactly);
2^h' l_zk' ≥ 2 l_zk + r + 2 r_zk + answers (the next mask rows take the two folded mask rows'
messages, the encoding randomness of all three folded rows, and the pad);
l_zk ≥ 2 k + 1 - h (room for the hiding polynomial's coefficients);
k ≥ 1 and h ≤ k at every stage except the last, where k = h = 0.
Also required: at least two stages and one answer; every code exists and is in order (Code.ok);
every message length is a power of two; no mask code is longer than its main code; k is at most
mostLogN; a mask row from the second stage on is at least as long as the pad (answers ≤ l_zk'). -/
def ioppOk (codes : Codes) (stages : List IoppStage) (answers : Nat) : Bool :=
  decide (2 ≤ stages.length) && decide (1 ≤ answers) && ioppStagesOk codes answers none stages

/-- The shape of the fold at a stage. The layout's members are not known before the stage's oracle
message is sent; a mask can be announced without them. -/
def ioppFoldShape (s : IoppStage) (L : GroupLayout) : FoldShape :=
  { code := s.code, maskCode := s.maskCode, layout := { L with k := s.k, h := s.h } }

/-- The last stage as single rows. A group has at least one row variable, also a group of one main
row, whose second row is a row of zeros that nobody sent: the variable is fixed at 0, which picks
the first row. Nothing unless the layout has one row variable, no mask row variable and one member.
A layout of two main rows also has one row variable, and this function does not tell the two apart:
that the last stage has one main row follows from ioppOk (k = 0) and switchTargetStage. -/
def ioppLastRows (s : IoppStage) (L : GroupLayout) (row : GroupRow) : Option SingleRows :=
  if L.k == 1 && L.h == 0 && L.members.size == 1 then
    some { code := s.code, maskCode := s.maskCode, masks := 1, c := row.c.fixLow [zeroE],
           d := #[row.d], target := row.target, layout := { L with k := 0 } }
  else none

/-- The stages of a proximity test from the stage cur on. answers: the answers to each sample. ride:
the masks ride (IoppChoice.masksRide). cur: the present stage; then the stages after it; row, L: the
claim on cur and its layout. The last argument is the number of the oracle that holds cur's mask, if
it has come: the fresh mask of its fold or, at the last stage, BASE's masking oracle. Ends with
BASE. -/
def ioppStagesVerify (answers : Nat) (ride : Bool) :
    IoppStage → List IoppStage → GroupRow → GroupLayout → Option Nat → Blk Unit
  | cur, [], row, L, baseMask => do
    baseVerify (← Blk.get (ioppLastRows cur L row)) baseMask 0
  | cur, next :: rest, row, L, foldMask => do
    let rows ← foldVerify (ioppFoldShape cur L) row foldMask
    Blk.note "FOLD: target" rows.target
    let toLast := rest.isEmpty
    let to ← Blk.newGroup next.code next.maskCode
    let others : Array OracleNotice :=
      if !ride then #[]
      else if toLast then #[baseMaskNotice next.code next.maskCode 1 0]
      else #[foldMaskNotice (ioppFoldShape next {})]
    let (s, row', L') ← csVerify rows
      (switchTargetStage next.code next.maskCode next.k next.h answers) to others
    Blk.note "CS: target" row'.target
    Blk.noteBy "CS: c'[0]" fun _ => row'.c.entry 0
    Blk.note "CS: d'[0]" (row'.d.getD 0 zeroE)
    Blk.note "CS: d's last entry" (row'.d.back?.getD zeroE)
    let mask ← if ride then (do pure (some (← Blk.get s.others[0]?))) else pure none
    ioppStagesVerify answers ride next rest row' L' mask

/-- The proximity test on group g. firstMask: the number of the oracle that holds the fresh mask of
the first fold, if it came in an earlier prover's message. A group with a kept member is refused at
the first switch (switchTargetStage names no oracle message for kept rows). stages and choice are
arguments: in the C++ the entry points take them from the chain's first query, and here the caller
answers for where they come from. A success says nothing of rounds that are left over: the caller's
walk must use them up. -/
def ioppVerify (g : Nat) (stages : List IoppStage) (choice : IoppChoice)
    (firstMask : Option Nat := none) : Blk Unit := do
  let answers ← Blk.samples
  Blk.must (ioppOk (← Blk.statement).codes stages answers)
  let (row, L) ← batVerify g
  Blk.note "BAT: target" row.target
  match stages with
  | [] => Blk.fail
  | first :: rest =>
    let G ← Blk.group g
    Blk.must (G.code == first.code && G.maskCode == first.maskCode && L.k == first.k &&
      L.h == first.h)
    ioppStagesVerify answers choice.masksRide first rest row L firstMask

end OnBytes
