-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RidersGPaid.lean: THE RIDERS AT THE FIRST SEGMENT's OPENING, CALLED BY NAME.
A statement with
its proof: calls alone.
  `ridersG_paid`: **`fillG_at`'s premise hR** (FillGAt.lean: a rider's premise for every item of Q
  that is none of its own), paid by name: `riderG_weights`, `riderG_oneRow` (RidersG.lean),
  `riderG_pileWithin` (RidersMore.lean), `riderG_fits` (BookFitsRides.lean). One binder hfB: proved
  in another file (`bookFitsB_iff`, Johnson/Desc/Sound/BookTestsLaw.lean) that this file does not
  import (a name declared twice beneath).
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.RidersMore
import Johnson.Desc.K13.Law.BookFitsRides
import Johnson.Desc.K13.Law.FillGAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker
open Desc.Plain
open Johnson.Pack (sigOf)
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame bookStepB)
open VerifiableInference.Desc.K12.Door (toTree)
open VerifiableInference.Desc.Book (BookFits)

/-- **The foreign riders at the first segment's opening, called by name.** -/
theorem ridersG_paid {Pp W Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub}
    {p : Option Place} (hm : Pub.noneSent ∈ Q)
    (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2)
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hB : ∀ x, Mg.pub bookFitsItem x = Sound.bookFitsB x.2.book)
    (hBP : ∀ x, Mg.pubP bookFitsItem x) (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hI : ∀ x, Mg.pub pileWithinItem x = pileWithinC x.2) (hIP : ∀ x, Mg.pubP pileWithinItem x)
    (hO : ∀ x, Mg.pub oneRowItem x = oneRowC x.2) (hOP : ∀ x, Mg.pubP oneRowItem x)
    (hQ : ∀ i ∈ Q, i = .noneSent ∨ i ∈ knownG ∨ i = weightsItem ∨ i = pileWithinItem ∨
      i = oneRowItem ∨ i = bookFitsItem) :
    ∀ i ∈ Q, i ≠ .noneSent → i ∉ knownG → RiderG Cl q gp nm X fvs kCol N Mg Q p i := by
  intro i hi h1 h2
  rcases hQ i hi with h | h | rfl | rfl | rfl | rfl
  · exact absurd h h1
  · exact absurd h h2
  · exact riderG_weights hm hNS hW hWP
  · exact riderG_pileWithin hm hi hNS hI hIP
  · exact riderG_oneRow hO hOP
  · exact riderG_fits Sound.bookFitsB hfB hi hB hBP

end VerifiableInference.Desc.K13.Law
