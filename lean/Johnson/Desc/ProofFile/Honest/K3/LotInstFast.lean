-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotInstFast.lean: the lookups' lot's honest side with another term
for the reader of the input at the lookups on the digits, in which the counts of a call are made in
one pass, and the theorem that it is the same lot. Definitions with code, and theorems without a
hypothesis.

Terms. Honest/K3/GLOSSARY.md. In this file: the reader of the input at a site is the field `wit` of
`Fill` (Honest/K3/LotRow.lean): of the chain's input and the challenges heard, the keys and bits
that the lookup's row is given.

Why. `theLot` (Honest/K3/LotFilled.lean) and `theLotInst` (Honest/K3/LotInst.lean) set that reader
to `askOf` (Honest/K3/Wit.lean). At a lookup on the digits a bit of that term is a bit of a count
over all places of its call; as the head of Honest/K3/WitDigitsFast.lean reads the term, it makes
that count anew for every row and every plane. `fastAsk` (there) makes the counts of a call in one
pass. It yields the same structure (`fastAsk_tied`, there), but a program that takes the halves out
of the lot's list evaluates the term that the lot holds. The lots of this file hold `fastAsk`.
Whether a program evaluates them faster has not been measured; the head of
Honest/K3/SeatFitsDigitsLive.lean [not in this library] tells one measurement, of the term `askOf`
alone, at a synthetic site.

What is defined.
  `fastWit`: the reader at a site: `fastAsk` where the site names the round that samples the matrix,
    the filling's own reader elsewhere.
  `fastFillAsk`: the letters of `fastFill` (Honest/K3/LotRow.lean) with that reader.
  `theLotFast`: the lot at these letters, at a letter `req` for the reader of the instance.
  `theLotInstFast`: the same at `req := reqAt Z` (Honest/K3/WitReq.lean), at every public part.

What is shown.
  `fastWit_eq`, `fastFillAsk_eq`: the reader, and so the letters, are those of `fastFill`.
  `theLotFast_eq`: `theLotFast cells weights req = theLot cells weights req`.
  `theLotInstFast_eq`: `theLotInstFast cells weights = theLotInst cells weights`.
  `theLotFast_is`, `theLotInstFast_is`: so their halves at a public part and a ground are the same
    lists.

How the proof goes. `wit_digits_fast` (Honest/K3/LotDigitsFast.lean) at a site that names such a
round; `rfl` elsewhere.

Imported, through the two files that this file imports: six files directly under Honest/
(BookOf.lean, ForKinds.lean, Frame.lean, SeatTests.lean, Side.lean, Sum.lean),
Honest/K8/Digits.lean, Honest/K8/Part.lean and Johnson/HonestTrace/DigitsAtTrace.lean.
No file under Honest/K3/Law/ is imported.

Users. A program that plays the lot's halves. Every theorem that is stated of `theLot` or
`theLotInst` holds of these lots by rewriting with the two equations. Honest/K3/LotInstKeep.lean,
Honest/K3/WitBound.lean, Honest/K3/Law/Keep/SiteRng.lean and Honest/K3/Law/Thread/LotInstFind.lean
import this file.

Limits. Only one of `theLot`, `theLotInst`, these two and the other lots named in
Honest/K3/LotInst.lean may stand in a list of lots' honest sides at a time: all bear the one lot's
name. The equations say that the terms are equal, not how long either takes: that the counts are
made once at a move is a matter of how a program evaluates the term. The stages' summands are
`fastFill`'s own: nothing is exchanged there. On the calls the reader is `askOf`, as before. Nothing
is evaluated in this file.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotInst
import Johnson.Desc.ProofFile.Honest.K3.LotDigitsFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- The reader of the input at a site: `fastAsk` where the site names the round that samples the
matrix, the filling's own reader elsewhere. -/
def fastWit (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    Local W₀ Rc Xi Tr → Ask :=
  match s.rng with
  | some r => fun t heard => fastAsk Z.p.X s.link r (cells t.trace) heard
  | none => (fastFill (Rc := Rc) (sourcesAt cells weights req Z)).wit s

/-- It is the filling's own reader, at every site. -/
theorem fastWit_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    fastWit (Rc := Rc) cells weights req Z s =
      (fastFill (Rc := Rc) (sourcesAt cells weights req Z)).wit s := by
  unfold fastWit
  split
  · rename_i r hr
    exact (wit_digits_fast cells weights req Z s r hr).symm
  · rfl

/-- The letters of `fastFill` with `fastWit` for the reader. -/
def fastFillAsk (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) : Fill (Local W₀ Rc Xi Tr) :=
  { jobs := (fastFill (Rc := Rc) (sourcesAt cells weights req Z)).jobs
    wit := fastWit cells weights req Z }

/-- They are the letters of `fastFill`. -/
theorem fastFillAsk_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) :
    fastFillAsk (Rc := Rc) cells weights req Z = fastFill (sourcesAt cells weights req Z) := by
  unfold fastFillAsk
  rw [show fastWit (Rc := Rc) cells weights req Z =
    (fastFill (Rc := Rc) (sourcesAt cells weights req Z)).wit from
      funext (fastWit_eq cells weights req Z)]

/-- The lot's honest side with `fastWit` for the reader of the input, at a letter for the reader of
the instance. In the place of `theLot`, never beside it. -/
def theLotFast (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotAt fun Z => fastFillAsk cells weights req Z

/-- It is `theLot`. -/
theorem theLotFast_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) :
    theLotFast (Rc := Rc) (X := X) cells weights req = theLot cells weights req :=
  congrArg rowLotAt (funext fun Z => fastFillAsk_eq cells weights req Z)

/-- The same at the proof file's own instance. In the place of `theLotInst`, never beside it. -/
def theLotInstFast (cells : Tr → Cells) (weights : W₀ → Weights) :
    HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotAt fun Z => fastFillAsk cells weights (reqAt Z) Z

/-- It is `theLotInst`. -/
theorem theLotInstFast_eq (cells : Tr → Cells) (weights : W₀ → Weights) :
    theLotInstFast (Rc := Rc) (X := X) cells weights = theLotInst cells weights :=
  congrArg rowLotAt (funext fun Z => fastFillAsk_eq cells weights (reqAt Z) Z)

/-- At each public part and ground its halves are those of `theLot`. -/
theorem theLotFast_is (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    (theLotFast (Rc := Rc) (X := X) cells weights req).halves Z G =
      (theLot (Rc := Rc) (X := X) cells weights req).halves Z G := by
  rw [theLotFast_eq]

/-- At each public part and ground its halves are those of `theLotInst`. -/
theorem theLotInstFast_is (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    (theLotInstFast (Rc := Rc) (X := X) cells weights).halves Z G =
      (theLotInst (Rc := Rc) (X := X) cells weights).halves Z G := by
  rw [theLotInstFast_eq]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.fastWit_eq
#print axioms ProofFile.Honest.K3.fastFillAsk_eq
#print axioms ProofFile.Honest.K3.theLotFast_eq
#print axioms ProofFile.Honest.K3.theLotInstFast_eq
#print axioms ProofFile.Honest.K3.theLotFast_is
#print axioms ProofFile.Honest.K3.theLotInstFast_is
