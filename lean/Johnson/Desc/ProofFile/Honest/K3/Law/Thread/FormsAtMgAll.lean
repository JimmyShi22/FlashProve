-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/FormsAtMgAll.lean: THE PREMISE ON THE FIELD "forms" OF
Honest/K3/Law/Thread/ExchangeDigitsAll.lean (hT: an equation of functions) HELD AGAINST THE
LIBRARY'S COMPOSED MEANING: at that meaning, at letters that are named here, the equation holds. So
that a premise which was spelled from a reading is seen to be met where it is to be spent.

  `FormsText`          hT's text, under a name: a copy, letter for letter
  `formsText_mgAll`    it holds at `mgAll Dm Mg`, at every Dm and Mg: the library's `mgAll_forms`
  `formsText_gives`    the name unfolds to hT's own form

THE LETTERS AT WHICH IT HOLDS. runs := Dm.runs; Rd := Dm.Rd; sent := Dm.N.sent; own := Dm.N.group;
ah := Dm.ah; tabOf := seatTab Dm.cs Dm.arr Dm.ms; wt := Dm.wt.

Limits. It holds ONE premise of that theorem at the library's composed meaning, general in its data.
That the frame's letters at the library's own lay such a meaning at every input is not typed here;
since, under the head: `formsText_lettersAt` (FormsAtLetters.lean). Nothing on soundness,
completeness or any other property of a protocol.
-/
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.Sound (MsgT MsgQ formsQ formsQA mgAll MgData mgAll_forms seatTab
  CellsQ)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The premise's text, under a name.** -/
def FormsText {P Cells Tok : Type} (Mg : Meaning P (Wit Cells Tok MsgT))
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers)
    (sent : Nat → Nat → List (Nat × Nat)) (own : Nat → List (Nat × Nat))
    (ah : Nat → String → Bool) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop) : Prop :=
  Mg.forms = fun i k r a y v =>
    (∀ p ∈ runs i k r,
      if ah p.1 p.2 = true then formsQA (sent i) (own i) (Rd i) p.1 p.2 a.2 (tabOf v)
      else formsQ (Rd i) (own i) p.1 p.2 a.2 (tabOf v)) ∧ (r = "weights" → wt i a y v)

/-- **It holds at the library's composed meaning**, at every Dm and Mg. -/
theorem formsText_mgAll {Xi P Tok : Type} {rows cols nR : Nat}
    {X : OnBytes.Model.Verify.Public} (Dm : MgData Xi P Tok rows cols nR X)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) :
    FormsText (mgAll Dm Mg) Dm.runs Dm.Rd Dm.N.sent Dm.N.group Dm.ah
      (seatTab Dm.cs Dm.arr Dm.ms) Dm.wt :=
  mgAll_forms Dm Mg

/-- The name unfolds to the premise's own form. -/
theorem formsText_gives {P Cells Tok : Type} {Mg : Meaning P (Wit Cells Tok MsgT)}
    {runs : Nat → Nat → String → List (Nat × String)} {Rd : Nat → Readers}
    {sent : Nat → Nat → List (Nat × Nat)} {own : Nat → List (Nat × Nat)}
    {ah : Nat → String → Bool} {tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ}
    {wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop}
    (h : FormsText Mg runs Rd sent own ah tabOf wt) :
    Mg.forms = fun i k r a y v =>
      (∀ p ∈ runs i k r,
        if ah p.1 p.2 = true then formsQA (sent i) (own i) (Rd i) p.1 p.2 a.2 (tabOf v)
        else formsQ (Rd i) (own i) p.1 p.2 a.2 (tabOf v)) ∧ (r = "weights" → wt i a y v) := h

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.formsText_mgAll
#print axioms ProofFile.Honest.K3.Law.Exchange.formsText_gives
