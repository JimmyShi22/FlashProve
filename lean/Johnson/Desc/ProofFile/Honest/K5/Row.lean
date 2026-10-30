-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Row.lean: the honest side of the kind "an attention segment's own
rounds" (K5), in the form of Honest/Frame.lean: the row at a place, the kind's half, and the lot's
honest side. The kind's own text does not hold what the prover sends
(Johnson/Desc/First/Att/K5AttentionKind.lean): this file holds it. Definitions with code; no theorem but one
equation of two names.

What is sent. The place's rounds are, in order: a masked sumcheck for each softmax-table unit (query
times key); one for the denominator times the output; a batching element; two for the value product,
below the diagonal and on it; a point; the row maxima at that point, as masked scalars in a round of
their own; three sumchecks for "the maximum is the score at a committed index, whose cells are
bits", each behind a batching element. No root is sent and no column is read.

  `jobs`      for each part: the values that are sent by themselves, each under a mask entry, and
              the summand (Johnson/Desc/K5/Honest/Alone.lean, Products.lean, Index.lean)
  `labelOf`, `inOf`   the segment's cells out of the common reader of cells (`Cells`,
              Honest/ForKinds.lean): a cell's name to its matrix, row and column by the library's
              own rule `addrA` (Johnson/Road/Lane5AttDef.lean); a matrix by the name that the
              verifier's plan gives it
  `Seat5`     a place's public data
  `chalOf`    the challenges that a part may read, of all that were heard
  `blankDraws`, `Seat5.fits`, `Seat5.roundsFit`   two tests on public data: the key points have the
              lengths at which the named points are made; the declared rounds at the place are this
              row's
  `seatAt`    the public data at a segment; nothing where a test fails
  `k5Row`, `k5Half`, `k5Lot`   the row; the kind's half; the halves at the places of the lot
              "K5: the attention segments' own rounds" (Johnson/Desc/ProofFile/Lot/K5.lean)

Four of the values that go under a mask entry are typed as the sums of the sumchecks that start from
them: the score value of a softmax-table unit, the denominator times the output, and the two value
products.

What is read. Of the witness: cells of the matrices as, ah, ao and qa of the segment, through
`Cells.cell` alone. Of the index, the stored tables' pads and encoding randomness and the instance:
nothing. Of the challenges in front of the place: each lookup call's key point, by the function
`keyAt`, which is a field of the public data: it is the text of the kind that draws these
challenges, not this file's. The coins: Honest/K5/RowOf.lean. No part has a stop.

Limits. Nothing holds `keyAt` or `base` against the description here. That public data which fit at
challenges that are all 0 fit at every list that the rounds in front can draw is a law under a named
premise on `keyAt`: of the challenges its key points' lengths hang on nothing but how many elements
each round drew (`fits_of_blank` under `KeySizes`, Honest/K5/Law/Fits.lean; `fits_of_blank_wide`
under `KeyWide`, Honest/K5/Law/FitsRun.lean); both premises are had where `keyAt` is `keyOfK3`
(Honest/K5/Law/KeyOfK3.lean). A cell beyond a matrix is whatever the reader yields.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.RowOf
import Johnson.Desc.K5.Honest.Alone
import Johnson.Desc.K5.Honest.Products
import Johnson.Desc.K5.Honest.Index
import Johnson.Desc.ProofFile.Lot.K5
import Johnson.Road.Lane5AttDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.Att.P (entriesOf script)
open H2K5.Honest (Pub5 K5In Chal iSE iVM iVD iM6 iSF iSD aloneKR leadK leadSE aloneOk m6 sK sSE sVM
  sVD sSF sSD sHB)

variable {W₀ Rc Xi Tr X : Type}

/-- **What is sent by itself and what is summed**, part by part. -/
def jobs (P : Pub5) : Jobs K5In :=
  let x := P.x
  { alone := fun p w c =>
      if p < x.score.length then
        (if p == 0 then aloneKR P w c else []) ++ leadK P w c p (sK P w c p).total
      else if p == iSE x then leadSE P w c (sSE P w c).total
      else if p == iVM x then [(sVM P w c).total, (sVD P w c).total]
      else if p == iM6 x then m6 P w c
      else []
    sum := fun p w c =>
      if p < x.score.length then sK P w c p
      else if p == iSE x then sSE P w c
      else if p == iVM x then sVM P w c
      else if p == iVD x then sVD P w c
      else if p == iSF x then sSF P w c
      else if p == iSD x then sSD P w c
      else sHB P w c }

/-- The name that the verifier's plan gives the matrix number a of the segment's list
(OnBytes/Model/AttentionPlan.lean: `matrices`). -/
def labelOf (S : OnBytes.Attention.Shape) (a : Nat) : String :=
  if a < S.cf.NAs then "as" ++ toString a
  else if a == S.cf.NAs then "ah"
  else if a == S.cf.NAs + 1 then "ao"
  else if a == S.cf.NAs + 2 then "bA"
  else "qa"

/-- **The segment's cells**, out of the common reader. l: the segment's number. -/
def inOf (S : OnBytes.Attention.Shape) (l : Nat) (cells : Cells) : K5In :=
  ⟨fun q =>
    let a := OnBytes.Road.L5.addrA S q
    eOfF (cells.cell l (labelOf S a.1) a.2.1 a.2.2)⟩

/-- **A place's public data.** -/
structure Seat5 where
  /-- the segment's number in the first chain -/
  link : Nat
  P : Pub5
  /-- how many rounds of the first chain stand in front of the place's first -/
  base : Nat
  /-- each lookup call's key point, of the challenges heard -/
  keyAt : List Fmt.Drawn → Array (Array E)

def Seat5.place (Z : Seat5) : Place := ⟨1, some Z.link, 3, .K5⟩

/-- The challenges that a part may read. In the first chain the challenge number i of those heard is
that of the chain's round number i. -/
def chalOf (Z : Seat5) (heard : List Fmt.Drawn) : Chal := ⟨Z.keyAt heard, heard.drop Z.base⟩

/-- Challenges of the declared shapes, all 0: as many elements a round as it draws. -/
def blankDraws (ds : List Fmt.DeclaredRound) : List Fmt.Drawn :=
  ds.map fun r => ⟨List.replicate r.entry.drawE (0, 0, 0), [], [], none⟩

/-- **THE PUBLIC DATA FIT, FIRST TEST: with code, on public data alone.** front: challenges of the
shapes of the rounds in front of the place. It asks that these are as many as `base` says, and that
at the key points made of them the verifier's own function for the named points returns, with planes
enough and as many softmax-table units as the planner's numbers count (`aloneOk`,
Johnson/Desc/K5/Honest/Alone.lean). WHY: where that function refuses, no move refuses. By their
texts the values of Alone.lean and the summands of Products.lean are then empty lists and zeros,
which the parts pad; what Index.lean computes is then computed of the cells at empty points and has
no meaning (its Limits). No theorem says this. The fault would pass in silence. The test is meant to
be a premise of every law on what this row sends, and `seatAt` yields nothing where it fails. Its
answer hangs on the key points through their lengths alone (`aloneOk_congr`,
Johnson/Desc/K5/Honest/Law/FitsSizes.lean), so it is asked at challenges that are all 0
(`fits_congr`, `aloneOk_run`, Honest/K5/Law/: conditional). WHAT IT DOES NOT CATCH: key points of
the right lengths that are another call's, or in another order; planner's numbers of these rounds
that are not the shape's: then two lists of values may have another length than the row's shape
wants (`Pub5.counted`, Johnson/Desc/K5/Honest/Law/Lengths.lean: a second test, which `seatAt` does
not ask); the summands' own counts (`Jobs.fits`, which is dear). -/
def Seat5.fits (Z : Seat5) (front : List Fmt.Drawn) : Bool :=
  front.length == Z.base && aloneOk Z.P (chalOf Z front)

/-- **SECOND TEST: the declared rounds from number `base` on are this row's**: as many as the row
has, each with the verifier's own name, bytes sent and number of elements drawn
(`entriesOf`, Johnson/Desc/First/Att/K5AttentionKind.lean; the bits of proof of work are not compared). WHY: a
part reads the place's own challenges by number, and one that has not been heard reads as 0. Where
this test says yes, the challenges that a part reads are those of rounds that stand in front of it
and draw as many elements as it reads; a wrong `base` shows unless other rounds of just these
shapes stand there. No theorem in this file says any of this. -/
def Seat5.roundsFit (Z : Seat5) (ds : List Fmt.DeclaredRound) : Bool :=
  let es := entriesOf 0 (script Z.P.x)
  ((ds.drop Z.base).take es.length).map (fun r => (r.entry.name, r.entry.msg, r.entry.drawE)) ==
    es.map fun y => (y.name, y.msg, y.drawE)

/-- **The row**, at the small input. -/
def k5Row (Z : Seat5) : List (Part Unit K5In Unit) := rowOf Z.place Z.P.x (chalOf Z) (jobs Z.P)

/-- **The kind's half.** cells: the reader of the witness. -/
def k5Half (cells : Tr → Cells) :
    KindHalf Seat5 (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fun Z => ⟨Z.place, (k5Row Z).map fun p =>
    p.lift (fun _ => ()) (fun t => inOf Z.P.S Z.link (cells t.trace)) (fun _ => ()) fun x _ => x⟩

/-- The public data at the attention segment number l of the name nm and the group g; nothing where
the public files have no plan of the group, where the table of steps lacks the place's first step,
or where these data do not fit (`Seat5.fits` at the first chain's declared rounds in front;
`Seat5.roundsFit` at the rounds from there on). Where it yields nothing the lot's honest side has no
half at that place, without a word, though the verifier's lot may bring its block there. -/
def seatAt (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground)
    (l : Nat) (nm : String) (g : Nat) : Option Seat5 :=
  (G.W.A[g]?).bind fun A =>
    (Z.roundsBefore? (nm ++ ".2.scores")).bind fun base =>
      let Y : Seat5 := ⟨l, ⟨A.S, A.own⟩, base, keyOf Z G l⟩
      if Y.fits (blankDraws (Z.D.1.take base)) && Y.roundsFit Z.D.1 then some Y else none

/-- **The lot's honest side**: a half at every attention segment. keyOf: the key points' reader at a
segment. -/
def k5Lot (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  { name := "K5: the attention segments' own rounds"
    halves := fun Z G => (H2K5.k5Places G).filterMap fun y =>
      (seatAt keyOf Z G y.1 y.2.1 y.2.2).map (k5Half cells) }

/-- The name is the lot's, letter for letter. -/
theorem k5Lot_name (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) :
    (k5Lot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).name = (H2K5.lotN Z).name := rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Lot_name
