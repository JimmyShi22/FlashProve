-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/BuiltOfParts.lean: WHERE EACH STEP OF `buildLinksH`
(OnBytes/Model/StagesLinks.lean) RETURNS, `buildLinksH` RETURNS, AND AT WHICH VALUE: the premise
h₁ of `madeAt_of_parts` (Johnson/AtFull/Made/Ledger.lean) from eleven named premises, each in its
step's own terms. Two theorems: joinings.
  `buildLinksH_of_parts`: the routine is eleven steps in a row: `headLast`, `linksCount`,
    `declareLinks` (a₂, a₃, a₄: the ledger's own three); eight tests: `heldAgainst`, `tableRows`,
    `weightLimbs`, `tableHeld`, `reqOk`, `listedFits`, `linksFit`, `numbersHeld` (h₄ to h₁₁); and
    it returns the links that `declareLinks` returned. SO THE VALUE IS NO SEARCH: { links := links
    }.
  `built_of_parts`: the same at the public parameters' three parts and the first chain's
    parameters as read back: the ledger's h₁ to the letter, at built := { links := links }.
Limits. A JOINING: the proof unfolds one definition and rewrites by the premises. IT PAYS NO
PREMISE: none of the eleven is shown at any files by Lean's kernel. WHETHER THE ELEVEN CAN
BE MET TOGETHER IS NOT SHOWN HERE: they hold together just where the routine returns (another file
cuts its return into them: OnBytes/Tie/Pv/Lookup/Ends/FoBuiltCut.lean), and no return is shown at
any files but by evaluation. No soundness is claimed.

-/
import OnBytes.Model.VerifyStages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params

/-- **`buildLinksH` returns**, and what it returns. -/
theorem buildLinksH_of_parts {links₀ links : Array LinkH} {declared : Array FrameLink} {NGr : Nat}
    {p4 : Bool} {wsLay : WsLay} {p : Params.First}
    (a₂ : headLast links₀ = .ok ()) (a₃ : linksCount links₀ = .ok ())
    (a₄ : declareLinks links₀ NGr p4 = .ok (links, declared))
    (h₄ : heldAgainst declared p = .ok ()) (h₅ : tableRows links NGr = .ok ())
    (h₆ : weightLimbs wsLay = .ok ()) (h₇ : tableHeld wsLay p = .ok ())
    (h₈ : reqOk p.codes p.shape = true) (h₉ : listedFits p = .ok ())
    (h₁₀ : linksFit links p.codes p.shape p.layout p.lin.kCol = .ok ())
    (h₁₁ : numbersHeld links p = .ok ()) :
    buildLinksH links₀ NGr p4 wsLay p = .ok { links := links } := by
  unfold buildLinksH
  simp only [a₂, a₃, a₄, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, bind, Except.bind, pure, Except.pure,
    Bool.not_true, Bool.false_eq_true, if_false]

/-- **The ledger's premise h₁**, at built := { links := links }. -/
theorem built_of_parts {X : Public} {chains : Chains} {links₀ links : Array LinkH}
    {declared : Array FrameLink}
    (a₂ : headLast links₀ = .ok ()) (a₃ : linksCount links₀ = .ok ())
    (a₄ : declareLinks links₀ X.NGr X.p4 = .ok (links, declared))
    (h₄ : heldAgainst declared chains.proof.first = .ok ())
    (h₅ : tableRows links X.NGr = .ok ()) (h₆ : weightLimbs X.layers.wsLay = .ok ())
    (h₇ : tableHeld X.layers.wsLay chains.proof.first = .ok ())
    (h₈ : reqOk chains.proof.first.codes chains.proof.first.shape = true)
    (h₉ : listedFits chains.proof.first = .ok ())
    (h₁₀ : linksFit links chains.proof.first.codes chains.proof.first.shape
      chains.proof.first.layout chains.proof.first.lin.kCol = .ok ())
    (h₁₁ : numbersHeld links chains.proof.first = .ok ()) :
    buildLinksH links₀ X.NGr X.p4 X.layers.wsLay chains.proof.first = .ok { links := links } :=
  buildLinksH_of_parts a₂ a₃ a₄ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.buildLinksH_of_parts
#print axioms Johnson.AtFull.Made.built_of_parts
