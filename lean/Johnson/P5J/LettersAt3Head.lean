-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAt3Head.lean: THE COMPOSED MEANING's PARAMETER headPart (the output head's
part of the model's relation), AT THE OUTPUT HEAD's FILES' TERM (Johnson/Desc/Kinds/). Definitions.

  `At.tabH x` := `tabOf (rowH x)` (Johnson/Desc/Kinds/HeadTables.lean;
    Johnson/Desc/First/Look/K3CallerHeadParts.lean): the table of the exponential's lookup, off the
    rows of the place x of the lookup on the head's calls. x IS AN OPTION's VALUE (`headAt (X Zp)`,
    Johnson/Desc/First/Look/K3CallerHead.lean): AN ARGUMENT; the named test: `(headAt (X
    Zp)).isSome`; the premise: `headAt (X Zp) = some x`.
  `At.𝔇AtHead Zp x 𝔇₁`: over a structure 𝔇₁: headPart := `headPartK6 𝔇₁.cs 𝔇₁.arr 𝔇₁.ms 𝔇₁.N
    (sizesOf X) (seatLay X 𝔇₁.layout num) X (plAt (num 24 0) 0) (tabH x) 𝔇₁.put (oneDec 𝔇₁.decT
    𝔇₁.H) tokHOf` (Johnson/Desc/Kinds/Law/HeadCutsK6.lean; PlanK6At.lean): these files' own term, as
    read in a text of this project that is not in this repository; WHAT IS A FIELD OF THE STRUCTURE
    IS READ OFF 𝔇₁ ITSELF: no second copy of a value; num := `At.num Zp` (no field); tokHOf:
    Johnson/P5J/TokTerms.lean. (uH: LettersAt3HeadArm.lean.)
IN THAT TERM's TEXT some parts of the head's relation are "True" (`partsAtX`'s last arm): these
parts are said elsewhere, or by nobody: not settled here. The numeral 24 (the head's segment)
stands in that term.
Limits. Definitions. NO EXAMPLE shows that the sentences can be met. Nothing on soundness.

-/
import Johnson.P5J.LettersRec
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Desc.Kinds.Law.PlanK6At
import Johnson.Desc.Kinds.HeadTables
import Johnson.Desc.First.Look.K3CallerHeadParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc.Sound (MgData oneDec)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6 seatLay plAt tabOf rowH)

/-- The table of the exponential's lookup, off the rows of the lookup's place. -/
def tabH (x : VerifiableInference.Desc.First.Look.Place) : ℕ → ℕ :=
  tabOf (rowH x)

/-- headPart, laid: at 𝔇₁'s own codes, arr, members, numbers, layout, put, decoder and reading. -/
noncomputable def 𝔇AtHead (Zp : ProofFile.Pub) {nR : ℕ} (x : VerifiableInference.Desc.First.Look.Place)
    (𝔇₁ : MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp) :=
  { 𝔇₁ with
    headPart := headPartK6 𝔇₁.cs 𝔇₁.arr 𝔇₁.ms 𝔇₁.N (Meaning.sizesOf (X Zp))
      (seatLay (X Zp) 𝔇₁.layout (num Zp)) (X Zp) (plAt (num Zp 24 0) 0) (tabH x) 𝔇₁.put
      (oneDec 𝔇₁.decT 𝔇₁.H) tokHOf }

end P5J.At
