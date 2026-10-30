-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Own.lean (kind K13: the members' batching and the linear claim's first part):
DEFINITIONS WITH CODE; NO THEOREM: five functions that K13's text (Johnson/Desc/K13/Text.lean)
calls, which match functions of the program `verify-on-bytes`, IN THE KIND'S OWN WORDS. Every test
bears a name; no function of `verify-on-bytes` that can refuse is called.

What they are for. Behind the last segment of a proof file's first chain a pile of rows on the
committed matrix of weights is made into one row, by random weights and a sumcheck over the matrix's
column variables; that row is read as the claim of the test on the table; and a row on the witness W
of that test is laid.

Main names (each: an answer, or the name of the test that refused).
  `pileOnTable st S indexMasks pile`: the pile's rows and the message of index masks have the form
    that the table's shape asks: five tests.
  `pileForm kCol pile`: the pile's rows have a form that the batching allows: three tests.
  `runSum c S fresh h`: **what one run of the masked sumcheck hands on**, from the claim, the
    summand, the fresh mask entries and what was heard: eight tests on sizes, then the row.
  `messageW S`: what the prover's message with W holds, in order: one test.
  `evalRow S claim w wLay`: the row on W: one test.

WHICH OF THE TESTS LOOK AT WHAT A PROVER SENT. `messageW`: none: the public shape alone.
`pileOnTable`, `pileForm`, `evalRow`: sizes and message numbers in records that the verifier's own
text has made (how many coordinates a point has, how many variables a weight has, which message a
mask entry names) and the statement's shapes: no sent value. `runSum`: three of its tests count what
was SENT (how many rounds were heard, how many values, how many coefficients in each round). What a
yes of each gives is a proposition with a proof in Johnson/Desc/K13/OwnLaws.lean.

AGAINST `verify-on-bytes`: pileOnTable = memberRowsFit, messageW = linMessageW, maskNotice =
linMaskNotice, evalRow = linEvalRow, splitNeeded = LinShape.ownSplitNeeded (OnBytes/Iop/Lin.lean) ·
pileForm = Batt.fits (OnBytes/Iop/Batt.lean) · runSum = Psc.run, weightFits = Psc.Weight.fits, the
first three tests of runSum = Psc.formOK (OnBytes/Iop/Psc.lean): the same tests and the same values:
theorems of Johnson/Desc/K13/OwnLaws.lean, at all arguments. The records (Statement, LinShape,
TensorRow, LinClaim, Tensor, Row, Slot, OracleNotice, VectorLay, IoppStage, Psc.Weight, Psc.Claim,
Psc.Summand, Psc.Heard, Psc.Out) and the functions on them that cannot refuse (Psc.varsOf, masksOf,
hidingWalk, claimAfter, scaleForm; LinShape.kRow; Tensor.vars, Tensor.eq; addLaid; foldMaskNotice;
ioppFoldShape; the field's addE, subE, mulE) are the library's and are called by name.


-/
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Own
open OnBytes OnBytes.Params

/-- An answer, or the name of the test that refused. -/
abbrev Ans (α : Type) : Type := Except String α

/-- A test, under its name. -/
def need (name : String) (b : Bool) : Ans Unit := if b then .ok () else .error name

/-- A value that must be there, under the name of the test that it is. -/
def there {α : Type} (name : String) : Option α → Ans α
  | some x => .ok x
  | none => .error name

/-! ## 1 The pile against the table -/

/-- The message of index masks: mask rows alone; sampled; under the mask code of the request's own
group. -/
def masksMessageFits (o : OracleShape) (S : LinShape) : Bool :=
  o.mainRows == 0 && decide (0 < o.maskRows) && decide (0 < o.answers) &&
    o.maskCode == S.ownMaskCode

/-- A row of the pile: every mask entry is an entry of the message of index masks; its point has a
coordinate for each column variable; each of its weights has a variable for each row bit. -/
def rowOnTable (S : LinShape) (indexMasks : Nat) (r : TensorRow) : Bool :=
  (r.masks.all fun m => m.1.oracle == indexMasks) && r.psi.length == S.kCol &&
    r.g.all (·.vars == S.kRow)

/-- **The pile's rows and the message of index masks have the form that the table's shape asks.** -/
def pileOnTable (st : Statement) (S : LinShape) (indexMasks : Nat) (pile : List TensorRow) :
    Ans Unit := do
  let x ← there "K13.index-masks-sent" st.oracles[indexMasks]?
  need "K13.index-masks-shape" (masksMessageFits x.shape S)
  need "K13.pile-has-a-row" !pile.isEmpty
  need "K13.table-has-a-column-variable" (decide (0 < S.kCol))
  need "K13.rows-on-the-table" (pile.all (rowOnTable S indexMasks))

/-! ## 2 The pile's form -/

/-- A row of the pile: its point has kCol coordinates; it has a weight; each of its weights has so
many variables. -/
def rowForm (kCol : Nat) (vars : Option Nat) (s : TensorRow) : Bool :=
  s.psi.length == kCol && !s.g.isEmpty && s.g.all fun t => some t.vars == vars

/-- **The pile's rows have a form that the batching allows**: there is a row; the matrix has more
than one column; every row has the form, at the number of variables of the first row's first
weight. -/
def pileForm (kCol : Nat) (pile : List TensorRow) : Ans Unit := do
  let r ← there "K13.batching-has-a-row" pile.head?
  need "K13.batching-has-a-column-variable" (decide (1 ≤ kCol))
  need "K13.rows-of-one-form" (pile.all (rowForm kCol (r.g.head?.map Tensor.vars)))

/-! ## 3 One run of the masked sumcheck -/

/-- The sizes of a weight fit each other. -/
def weightFits (w : Psc.Weight) : Bool :=
  decide (2 ≤ w.d) && w.moment.length == w.d && decide (w.psi.length ≤ w.d) &&
    decide (w.fixed < w.d)

/-- **What one run hands on.** fresh: mask entries just taken from an oracle message's ledger. h:
what was heard. -/
def runSum (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (h : Psc.Heard) : Ans Psc.Out := do
  let vars := Psc.varsOf c S
  let challenges := h.rounds.map (·.2)
  let point := challenges.take c.vars.length
  let a := S.coeffs point h.values
  let hw := Psc.hidingWalk (vars.zip challenges)
  let last := Psc.claimAfter vars h.rounds (addE h.mu (mulE h.eps c.target))
  let beta := if S.shown == 0 then none else challenges.getLast?
  need "K13.degree-0-just-if-none-shown" ((S.shown == 0) == (S.degree == 0))
  need "K13.something-to-sum-or-show" (decide (0 < S.shown) || !c.vars.isEmpty)
  need "K13.weights-fit" (c.vars.all weightFits)
  need "K13.mask-entries-counted" (fresh.length == Psc.masksOf c S)
  need "K13.a-round-a-variable" (h.rounds.length == vars.length)
  need "K13.values-counted" (h.values.length == S.shown)
  need "K13.a-coefficient-a-kept-map" (a.length == 1 + S.kept)
  need "K13.sent-coefficients-counted"
    ((vars.zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d)
  pure {
    point := point
    rowMasks := fresh.zip hw.1 ++ Psc.scaleForm (mulE h.eps hw.2) c.masks
    rowMaps := (a.drop 1).map fun x => mulE h.eps x
    rowTarget := subE last (mulE h.eps (a.headD zeroE))
    ends := ((fresh.drop hw.1.length).zip h.values).map fun p =>
      ⟨point, [(p.1, beta.getD zeroE)], p.2⟩
    eps := h.eps
    beta := beta }

/-! ## 4 W's message, and the row on W -/

/-- W and Omega differ in code, so a later row is split, and the split's message goes out with W. -/
def splitNeeded (S : LinShape) : Bool := S.w.code != S.omega.code

/-- The notice of the fresh mask message of a proximity test's first fold, for a mask that is sent
ahead. -/
def maskNotice (test : List IoppStage) (leafClass : Nat) : Ans OracleNotice := do
  let s ← there "K13.own-test-has-a-stage" test.head?
  pure (foldMaskNotice { ioppFoldShape s {} with maskLeafClass := leafClass })

/-- **What the prover's message with W holds, in order.** -/
def messageW (S : LinShape) : Ans (Array OracleNotice) :=
  let a : Array OracleNotice := #[⟨S.w, S.wLeafClass⟩]
  let b := if splitNeeded S then a.push ⟨S.ownSplit, S.ownSplitLeafClass⟩ else a
  if S.masksAhead then (maskNotice S.testOwn S.wLeafClass).map b.push else pure b

/-- **The row on W**: W at the claim's point, plus the claim's masks, is the target. -/
def evalRow (S : LinShape) (claim : LinClaim) (w : Nat) (wLay : VectorLay) : Ans Row := do
  need "K13.a-coordinate-a-column-variable" (claim.psi.length == S.kCol)
  pure (addLaid { units := claim.masks, target := claim.target } w wLay [Tensor.eq claim.psi])

end VerifiableInference.Desc.K13.Own
