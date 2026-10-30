-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Base/Base.lean: the last step of a proximity test (the base case) as a plain
function on data, at one type of steps: Step S := S → List Fmt.RoundView → List Col → Option (S × Nat). The
step says how many opened columns it took.

What it stands for: the last case of ioppStagesVerify in the library's hand-written verifier program
(OnBytes/Iop/Prox.lean:215-216): ioppLastRows (:202-207), then baseVerify (:103-144), in the case
that the masking message came in an earlier message ("the masks ride").

How it is made. The two tests on the prover's values are ONE CALL of the format's own
Fmt.M1.baseOK (Fmt/M1Fold.lean:152-159: baseB1, the linear claim; baseB2At, two equations at each
drawn position). It is a Bool: a failed test is a refusal at once, where the program's two calls of
Blk.check (Prox.lean:129, :135) mark and go on. Around that call stand the public guards that
Fmt.M1's own string (Fmt/M1Dec.lean:150-159) does not ask: the list is beneath baseEW. Pure routines
of the program are called by name: ioppLastRows, baseShapeOk, singleRowsOracles, singleRowsSymbols,
Positions.ofDraws, Form.fits, Form.writeOut, ceilLog2.
Two functions are arguments: spend (the mark that a masking message is spent once) and read (the
opened columns taken in order; the book's count). This file does not say what stands in them.

  SB      what crosses the border: the statement; the book of trees; whether the round closed last
          owes no count; the test's own five values (the present stage; the stages behind it; the
          claim on its group; that group's layout; the masking message's number).
  ParB    what the step has of the plan: the chain's first tree's number; the two rounds' entries.
  baseEW  the step with the words of the refusal, over a given test on values (an argument only so
          that a test of this file can lay a planted copy).
  baseE   baseEW at Fmt.M1.baseOK.   baseStep   at the one type of steps.
No Blk, no Ctx, no digest, no dry run. No theorem. Nothing on soundness.


-/
import OnBytes.Iop.Prox
import Fmt.M1Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Base
open OnBytes

abbrev Col : Type := Nat × Nat × List UInt64

abbrev Step (S : Type) : Type := S → List Fmt.RoundView → List Col → Option (S × Nat)

structure SB where
  st : Statement
  book : TreeBook
  /-- the round closed last owes no count of rows (the program's Chan.settled) -/
  settled : Bool
  cur : Params.IoppStage
  later : List Params.IoppStage
  row : GroupRow
  L : GroupLayout
  mask : Option Nat

structure ParB where
  firstTree : Nat
  eLam : Fmt.Entry
  eBase : Fmt.Entry

/-- The message o is marked as spent as a mask; nothing if it cannot be. -/
abbrev SpendFn : Type := Statement → Nat → Option Statement

/-- What a reading of opened columns gives: the book with its counts, how many columns were taken,
each message's symbols at each position. -/
structure Got where
  book : TreeBook
  took : Nat
  opened : Array (Array Column)

/-- Statement; book; the chain's first tree's number; the columns not yet taken; the messages asked
for; the positions. -/
abbrev ReadFn : Type :=
  Statement → TreeBook → Nat → List Col → Array Nat → Positions → Option Got

/-- The type of Fmt.M1.baseOK at the field of the release. -/
abbrev TestFn : Type :=
  Fmt.M1.Code → Fmt.M1.Code → Array Fmt.M1.E → Array Fmt.M1.E → Fmt.M1.E → Fmt.M1.E → Fmt.M1.E →
    List Fmt.M1.E → List Fmt.M1.E → List Fmt.M1.E → List Fmt.M1.E → List Nat →
    (Nat → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)) → Bool

/-- The items of a message, if each is an element of the extension field. -/
def elemsOf : List Fmt.ItemValue → Option (List Fmt.M1.E)
  | [] => some []
  | .e x :: l => (elemsOf l).map (x :: ·)
  | _ => none

/-- What the program's Blk.close asks of the plan's entry and of the round's draws
(OnBytes/Iop/Ground.lean:825, :841-842). -/
def entryOK (e : Fmt.Entry) (name : String) (settled : Bool) (r : Fmt.RoundView) : Bool :=
  e.name == name && e.drawNZ == 0 && settled && r.drawn.elems.length == e.drawE &&
    r.drawn.poss.length == e.poss && r.drawn.trits.length == e.trits

def codeOf (c : Code) : Fmt.M1.Code := ⟨c.logN, c.ell, c.r⟩

def opt {α : Type} (why : String) : Option α → Except String α
  | some a => .ok a
  | none => .error why

def need (why : String) (b : Bool) : Except String Unit := if b then .ok () else .error why

/-- **The step, with the words of the refusal.** The list: each guard, then the program's file and
line.
 [BS]  the stretch has just two rounds: whoever deals the rounds.
 [B0]  no stage is left: Prox.lean:215 (the case "cur, []").
 [B1]  the last group has one row variable, no mask row variable, one member: Prox.lean:203
       (ioppLastRows).
 [B2]  the main code is in the list: Prox.lean:105.
 [B3]  the mask code is in the list: Prox.lean:117 (masks = 1 by :204).
 [B4]  the masking message has come: Prox.lean:106-107. THE OTHER CASE (:108-110) IS NOT IN THIS
       STEP: it is refused.
 [B5]  the complex and the masking message have the shapes asked: Prox.lean:112 (baseShapeOk).
 [B6]  the masking message is not sampled, has no answers, IS NOT SPENT; it is marked: Prox.lean:113
       over OnBytes/Iop/Ground.lean:1279-1282: the argument spend.
 [B7]  "BASE lambda": the entry's name; no element other than 0; the round before owes no count; the
       numbers of draws: Prox.lean:115 over OnBytes/Iop/Ground.lean:825, :841-842.
 [B8]  its message is one element and nothing else: Prox.lean:114 (recvE:
       OnBytes/Iop/Ground.lean:778-781) with OnBytes/Iop/Ground.lean:841 (r.vals.isEmpty).
 [B9]  one element is drawn: OnBytes/Iop/Ground.lean:869-872.
 [B10] "BASE": the like; "BASE lambda" owes no count: its entry counts no rows: Prox.lean:130 over
       OnBytes/Iop/Ground.lean:825 with :602-605, :841-842.
 [B11] the entry's range is the main code's, and it draws a position: OnBytes/Iop/Ground.lean:880.
 [B12] no element is drawn behind the positions: Prox.lean:131.
 [B13] "BASE" owes no count: a step asks it of each of its own entries, the last included.
 [B14] every item of its message is an element: Prox.lean:119-120 (recvE).
 [B15] they are as many as the two messages and the two tails, and none is left: Prox.lean:119-120
       with OnBytes/Iop/Ground.lean:841.
 [B16] the claim's form fits the main message; one written-out vector of the mask message's length:
       Prox.lean:121-122.
 [B17] NOT THE PROGRAM's: both codes are no longer than 2^32 and each drawn position lies in the
       range: there Fmt.M1's point of a position (Fmt/M1Codes.lean: point) is the program's
       (OnBytes/Iop/Ground.lean:161-166: codePoint).
 [B18] NOT THE PROGRAM's: the written-out form has just as many entries as the main message
       (Fmt.M1's dot ends at the shorter list).
 [B19] the columns are read: Prox.lean:132 over OnBytes/Iop/Ground.lean:1600-1607: argument read.
 [B20] the columns fit the layout: Prox.lean:133.
 [B21] the masking message's columns are there: Prox.lean:134.
 [B22] NOT THE PROGRAM's (there a symbol that is missing counts as 0: Prox.lean:137-143, getD): what
       was read has a symbol for each row at each listed position, and each column of the masking
       message one main and one mask symbol: so that no 0 is laid in for what read, an argument,
       left out.
 [B23] THE LINEAR CLAIM AND THE SYMBOLS AT THE POSITIONS: Prox.lean:123-129 and :135-144:
       Fmt.M1.baseOK. -/
def baseEW (test : TestFn) (spend : SpendFn) (read : ReadFn) (P : ParB) (s : SB)
    (rounds : List Fmt.RoundView) (cols : List Col) : Except String (SB × Nat) :=
  match rounds with
  | [rL, rB] => do
    need "B0: a stage is left" s.later.isEmpty
    let R ← opt "B1: the last group is not of one row" (ioppLastRows s.cur s.L s.row)
    let code ← opt "B2: the main code is not there" s.st.codes.base[R.code]?
    let zk ← opt "B3: the mask code is not there" s.st.codes.mask[R.maskCode]?
    let star ← opt "B4: the masking message has not come" s.mask
    need "B5: the shapes" (baseShapeOk s.st R star)
    let S1 ← opt "B6: the masking message cannot be spent" (spend s.st star)
    need "B7: the entry BASE lambda" (entryOK P.eLam "BASE lambda" s.settled rL)
    let tauS ← match rL.vals with
      | [.e x] => pure x
      | _ => throw "B8: the message is not one element"
    let lam ← match rL.drawn.elems with
      | [x] => pure x
      | _ => throw "B9: not one element is drawn"
    need "B10: the entry BASE" (entryOK P.eBase "BASE" (P.eLam.rows == 0) rB)
    need "B11: the entry's range or number of positions"
      (P.eBase.logN == code.logN && decide (0 < P.eBase.poss))
    need "B12: an element is drawn behind the positions" rB.drawn.elems.isEmpty
    need "B13: the entry BASE counts rows that nobody asks" (P.eBase.rows == 0)
    let sent ← opt "B14: an item is no element" (elemsOf rB.vals)
    need "B15: the number of elements shown" (sent.length == code.ell + zk.ell + code.r + zk.r)
    need "B16: the claim's form does not fit"
      (R.c.fits (ceilLog2 code.ell) && R.d.size == R.masks && R.d.all (·.size == zk.ell) &&
        R.masks == 1)
    need "B17: a code beyond 2^32, or a position out of the range"
      (decide (code.logN ≤ 32) && decide (zk.logN ≤ 32) &&
        rB.drawn.poss.all fun x => decide (x < 2 ^ code.logN))
    let c := (R.c.writeOut (ceilLog2 code.ell)).map (·.triple)
    need "B18: the written-out form's length" (c.size == code.ell)
    let d := (R.d.getD 0 #[]).map (·.triple)
    let pos := Positions.ofDraws code.logN rB.drawn.poss
    let o ← opt "B19: the columns cannot be read"
      (read S1 s.book P.firstTree cols ((singleRowsOracles R).push star) pos)
    let y ← opt "B20: the columns do not fit the layout"
      (singleRowsSymbols R o.opened pos.all.size)
    let stars ← opt "B21: the masking message's columns are not there" o.opened.back?
    need "B22: a symbol is missing in what was read"
      (y.size == pos.all.size * R.rows && R.rows == 2 && stars.size == pos.all.size &&
        stars.all fun m => m.main.size == 1 && m.mask.size == 1)
    let col (x : Nat) : Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E) :=
      (pos.indexOf x).map fun i =>
        let m := stars.getD i {}
        ((y.getD (i * R.rows) zeroE).triple, (m.main.getD 0 zeroE).triple,
          (y.getD (i * R.rows + 1) zeroE).triple, (m.mask.getD 0 zeroE).triple)
    need "B23: the linear claim, or a symbol at a position"
      (test (codeOf code) (codeOf zk) c d R.target.triple tauS lam (sent.take code.ell)
        ((sent.drop code.ell).take zk.ell) ((sent.drop (code.ell + zk.ell)).take code.r)
        (sent.drop (code.ell + zk.ell + code.r)) rB.drawn.poss col)
    pure ({ s with st := S1, book := o.book, settled := true }, o.took)
  | _ => .error "BS: the stretch has not two rounds"

/-- **The base case.** -/
def baseE : SpendFn → ReadFn → ParB → SB → List Fmt.RoundView → List Col → Except String (SB × Nat) :=
  baseEW (Fmt.M1.baseOK .two)

def baseStep (spend : SpendFn) (read : ReadFn) (P : ParB) : Step SB := fun s r c =>
  (baseE spend read P s r c).toOption

end VerifiableInference.Desc.First.Base
