-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Part.lean: the honest side of the sub-protocol "the output head's
own rounds". The verifier's description writes the honest prover's messages only in part
(Johnson/Desc/Kinds/Head.lean, under SENDS; Johnson/Desc/Kinds/Law/HeadSends.lean); this file writes
them in the form of Honest/Frame.lean. Definitions with code and two examples; no theorem. A
simulator beside each part, and the side, stand in Honest/K6/Side.lean.

What is sent. The sub-protocol's 16 + 2 lPd + 4 lt rounds are cut into eight parts:

  0  one round: nothing is sent; the point pV on the positions is drawn
  1  one round: nine hidden scalars: the sums of limb products of the stream's squares at pV
  2  a masked sumcheck in lPd + lt variables, without a claimed sum of its own, two end values
  3  one round: nothing is sent; an element is drawn that nothing reads
  4  one round: seven hidden scalars: the products of the fields of the norm's row at pV
  5  a masked sumcheck in lt variables, four end values
  6  a masked sumcheck in lt variables, two end values
  7  a masked sumcheck in lt + lPd variables, two end values

The coins. Every coin that the row uses is an entry of the segment's mask row, in a run that a part
spends: no part takes a coin of its own, and none is handed a run to carry. (That no entry is handed
to two parts is the book's to keep.) The nine and the seven hidden scalars and the three claimed
sums are sent as value plus entry. An end value is sent as value plus the last challenge times its
entry. The other scalars of a masked sumcheck (the hiding polynomial's sum, the rounds'
coefficients, those in the further variable) are made of several entries of the part's own two
runs: how, is Honest/Sum.lean's text. No round sends a root. No part has a stop.

  `pointShape`    a masked sumcheck's shape where every variable is summed at a point and every
                  round polynomial has three coefficients
  `pairJob`       what the masked sumcheck's part asks of its caller, of a sum of weighted products
                  of pairs of maps (Johnson/Desc/K6/Honest/Pairs.lean)
  `headSquaresSum`, `headProductsSum`, `headNormedSum`, `headLogitsSum`   what the four sumchecks
                  sum, of the input and the challenges heard; with the three claimed sums
                  beside them
  `headNormedSumAt`, `headNormedLeadAt`, `headLogitsSumAt`, `headLogitsLeadAt`   the two at the
                  lookup's point, at letters that are handed in
  `headSquaresJob`, `headProductsJob`, `headNormedJob`, `headLogitsJob`   the four calls
  `headNine`, `headSeven`   the values of the two rounds of hidden scalars
  `headScalarsUse`, `headRunName`   the word for such scalars in a run's name; a part's run's name
  `headParts`     the eight parts, at the small input
  `headPlace`, `headRow`, `headHalf`, `headLot`   the row seated; the half; the lot's honest side

The masked sumcheck is not written here: `sumPart` (Honest/Sum.lean) plays its rounds. Nor are the
round that sends nothing and the round that sends hidden scalars: `quietPart` and `scalarsPart`
(Honest/ForKinds.lean). What is summed stands in Johnson/Desc/K6/Honest/Tables.lean.

Limits. A claimed sum is not sent as the total of the sum that is played. For the stream times the
reciprocal and for the head's own sumcheck it is the term in which the library's laws on the
verifier's text write the true sum; for the products it is made of the seven hidden products and the
batching element. That claimed sum and total are one, and that the four jobs' round polynomials are
the partial sums of what the verifier's text means, is proved of no job by name, and of the
program's words by no theorem. Of the readings in the
field the library proves, for the sums that the jobs call: the claimed sum, or for the squares the
start form, and the total read as one term, conditional on a point's length
(Johnson/Desc/K6/Honest/TablesLaw.lean: `prLead_reads` with `prTotal_reads`, and the like); and, for
every such sum, while a variable is left, a round's polynomial summed at the variable's point reads
as the sum's partial sum so far, and at its challenge as the next
(Johnson/Desc/K6/Honest/PairLaw.lean: `round_sums`, `round_at`). Each job and each round of hidden
scalars names its part's number in the row as a written numeral: Honest/K6/Cut.lean tries these at
labelled challenges. That the two rounds of hidden scalars hand `scalarsPart` these values of the
challenges heard is seen by no line there. The lot's name is written here a second time. Nothing on
any
property.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.ProofFile.Honest.K6.Ask
import Johnson.Desc.K6.Honest.Tables
import Johnson.Desc.ProofFile.Lots.PureLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open VerifiableInference.Desc.Kinds (Head.Par Head.Given Head.Law.NCells)
open VerifiableInference.Desc.Kinds.Head.Honest (PairSum wScalars pScalars sqSum prSum nmSum lgSum
  prLead nmLead lgLead)

variable {V W X Pb W₀ Rc Tr : Type}

/-! ## 1 The four calls of the masked sumcheck -/

/-- The shape of a call in n variables, each summed at a point, each round's polynomial of three
coefficients; the degree in the further variable is 2. The points are stand-ins here: the run's are
laid by the job. -/
def pointShape (lead n ends : Nat) : Call :=
  ⟨lead, List.replicate n (.point zeroE 3), some ⟨2, ends⟩⟩

/-- **A job of a sum of weighted products of pairs of maps.** sumAt: the sum, of the input and the
challenges in front of the part. -/
def pairJob (shape : Call) (sumAt : W → Front X → PairSum) (lead : W → Front X → List E) :
    SumJob W X :=
  { shape, points := fun w fr => (sumAt w fr).z, lead
    round := fun w fr rs => (sumAt w fr).round rs
    inY := fun w fr rs m => (sumAt w fr).inY rs m
    ends := fun w fr rs => (sumAt w fr).ends rs }

/-- The sums of squares, part 2: the sum, of the input and the challenges heard in front of the
part. -/
def headSquaresSum (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : PairSum :=
  let _ := p.sizes
  let own := headOwn p 2 heard
  sqSum a.cells (headPV own) (headGam own)

/-- Its call. The sum that it must equal is a form on the nine scalars of part 1, so the call has no
lead. -/
def headSquaresJob (p : Head.Par) : SumJob HeadAsk Unit :=
  pairJob (pointShape 0 (headLPd p + headLt p) 2) (fun a fr => headSquaresSum p a fr.heard)
    fun _ _ => []

/-- The products of the row's fields, part 5: the sum. -/
def headProductsSum (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : PairSum :=
  let _ := p.sizes
  let own := headOwn p 5 heard
  prSum a.cells (headPV own) (headOm p own)

/-- Its claimed sum. -/
def headProductsLead (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : E :=
  let _ := p.sizes
  let own := headOwn p 5 heard
  prLead a.cells (headPV own) (headOm p own)

/-- Its call. -/
def headProductsJob (p : Head.Par) : SumJob HeadAsk Unit :=
  pairJob (pointShape 1 (headLt p) 4) (fun a fr => headProductsSum p a fr.heard)
    fun a fr => [headProductsLead p a fr.heard]

/-- The two sums at the lookup's point, and their claimed sums, at letters that are handed in. THE
LETTERS ARE AN ARGUMENT, AND THE FOUR ARE NOT INLINED, FOR THE COST ALONE. With the letters as a
local instance in the caller's body one call of a round takes several hundred times as long under
Lean's evaluator, by a measurement at a small size, with the same values: it seems that the
structure of letters is then made anew at every entry of every map; as an argument it is made once
for each call. -/
@[noinline] def headNormedSumAt (g : Head.Given) (c : Head.Law.NCells) : PairSum :=
  let _ := g
  nmSum c
@[inherit_doc headNormedSumAt, noinline]
def headNormedLeadAt (g : Head.Given) (c : Head.Law.NCells) : E :=
  let _ := g
  nmLead c
@[inherit_doc headNormedSumAt, noinline]
def headLogitsSumAt (g : Head.Given) (c : Head.Law.NCells) : PairSum :=
  let _ := g
  lgSum c.toCells
@[inherit_doc headNormedSumAt, noinline]
def headLogitsLeadAt (g : Head.Given) (c : Head.Law.NCells) : E :=
  let _ := g
  lgLead c.toCells

/-- The stream times the reciprocal, at the lookup's point on the positions, part 6: the sum. -/
def headNormedSum (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : PairSum :=
  headNormedSumAt (a.given p (headFront p 6 heard)) a.cells

/-- Its claimed sum. -/
def headNormedLead (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : E :=
  headNormedLeadAt (a.given p (headFront p 6 heard)) a.cells

/-- Its call. -/
def headNormedJob (p : Head.Par) : SumJob HeadAsk Unit :=
  pairJob (pointShape 1 (headLt p) 2) (fun a fr => headNormedSum p a fr.heard)
    fun a fr => [headNormedLead p a fr.heard]

/-- The head's own sumcheck, part 7: the sum. -/
def headLogitsSum (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : PairSum :=
  headLogitsSumAt (a.given p (headFront p 7 heard)) a.cells

/-- Its claimed sum. -/
def headLogitsLead (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : E :=
  headLogitsLeadAt (a.given p (headFront p 7 heard)) a.cells

/-- Its call. -/
def headLogitsJob (p : Head.Par) : SumJob HeadAsk Unit :=
  pairJob (pointShape 1 (headLt p + headLPd p) 2) (fun a fr => headLogitsSum p a fr.heard)
    fun a fr => [headLogitsLead p a fr.heard]

/-! ## 2 The row -/

/-- The word for "hidden scalars that ride in a round by themselves" in a run's name
(Honest/ForKinds.lean, `runName`'s docstring). -/
def headScalarsUse : String := "scalars"

/-- The run of the segment's mask row that part number i at a place spends, for a use. -/
def headRunName (at_ : Place) (i : Nat) (use : String) : String := runName maskRowRun ⟨at_, i⟩ use

/-- The nine hidden scalars of part 1: of the input and the challenges heard in front of the part.
-/
def headNine (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : List E :=
  let _ := p.sizes
  wScalars a.cells (headPV (headOwn p 1 heard))

/-- The seven hidden scalars of part 4, likewise. -/
def headSeven (p : Head.Par) (a : HeadAsk) (heard : List Fmt.Drawn) : List E :=
  let _ := p.sizes
  pScalars a.cells (headPV (headOwn p 4 heard))

/-- **The eight parts**, at the small input. at_: the place, which the runs' names bear. -/
def headParts (p : Head.Par) (at_ : Place) : List (Part Unit HeadAsk Unit) :=
  let sum (i : Nat) (J : SumJob HeadAsk Unit) : Part Unit HeadAsk Unit :=
    sumPart (headRunName at_ i "sum") (headRunName at_ i "ends") J
  [quietPart,
   scalarsPart (headRunName at_ 1 headScalarsUse) 9 (fun a fr => headNine p a fr.heard),
   sum 2 (headSquaresJob p),
   quietPart,
   scalarsPart (headRunName at_ 4 headScalarsUse) 7 (fun a fr => headSeven p a fr.heard),
   sum 5 (headProductsJob p),
   sum 6 (headNormedJob p),
   sum 7 (headLogitsJob p)]

/-- The place: in the first chain, at a link's number and a piece. -/
def headPlace (link piece : Nat) : Place := ⟨1, some link, piece, .K6⟩

/-- **The row, seated** in the first chain's letters. wit: the small input of the prover's input. -/
def headRow (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    List (Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X) :=
  (headParts p at_).map fun q => q.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x

/-- **The sub-protocol's half**, at a link's number and a piece; its parameter is the verifier's
text's own: the place's public numbers. -/
def headHalf (wit : Local W₀ Rc Inst Tr → HeadAsk) (link piece : Nat) :
    KindHalf Head.Par (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  fun p => ⟨headPlace link piece, headRow wit p (headPlace link piece)⟩

/-- The place's public numbers at the proof file's description, as the seated block takes them
(Johnson/Stored/HeadSeatAt.lean: `blockOf`). -/
def headParAt (G : Ground) : Head.Par :=
  VerifiableInference.Desc.Kinds.Head.parOf G.W.hS
    ((OnBytes.Params.settingOf G.W.P.frame).workOf .field .request)

/-- **The lot's honest side**: one half for each block that the lot seats, at that block's own
place: one, or none where the lot seats none. (`headLot_seated`, Honest/K6/Cut.lean, proves that the
place is piece 4 of the last link, and that the block's rounds are those of `headParAt`.) wit: of
the public part and the segments' built data. fits: A TEST WITH CODE ON THE PUBLIC PART AND THE
SEGMENTS' BUILT DATA: WHERE IT SAYS NO, NO HALF IS LAID, so no part makes a value of numbers that do
not fit. That is visible, and no refusal of a player's: `lacking` (Honest/Frame.lean), which goes by
places, names the sub-protocol (`lotsLacking`, which goes by the lots' names, does not); the rounds
are marked as made by no half, and nothing is sent in them (or, by `run` (Honest/Frame.lean), which
falls back on a stored run, that run's rounds); `runC` (Honest/Walk.lean) then asks the
sub-protocol's own step on them and books a no by place. That this step says no to rounds in which
nothing is sent is not shown here. THE NAME IS WRITTEN A SECOND TIME HERE; the line below holds it
against the lot's own. -/
def headLot (fits : Pub → Ground → Bool) (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) :
    HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  { name := "the output head's own rounds (K6)"
    halves := fun Z G =>
      if fits Z G then
        (P4.k6Hear Z G).map fun b => ⟨b.place, headRow (wit Z G) (headParAt G) b.place⟩
      else [] }

-- the name is the name of the lot that seats the sub-protocol's block, at every public part; and
-- that lot is the first of the two that the description's list of lots takes for the head
example (fits : Pub → Ground → Bool) (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk)
    (Z : Pub) : (headLot (X := X) fits wit).name = (P4.k6Lot Z).name := rfl
example (Z : Pub) : (p4Pure Z).head?.map (·.name) = some (P4.k6Lot Z).name := rfl

end ProofFile.Honest.K6
