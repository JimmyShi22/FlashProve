-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedOthers4.lean: A STATEMENT THAT IS OWED, WRITTEN AS A DEFINITION OF A Prop:
no proof stands here.
IN PLAIN WORDS. WHAT STAYS AT W's COMMITMENT (`Others4`,
Johnson/Desc/K13/Law/FillFromSentences.lean: seven clauses on other files' letters and on the
reader), AT THE READER THROUGH THE RECORD's OWN BOOK (`rwBook`) AND AT SIX LETTERS OF THE FORM IN
WHICH THOSE FILES HAVE FILLED THEM (`SigLetters`, Johnson/Desc/K13/Law/Others3AtSig.lean). THE
PATTERN, clause by clause: `others3_at_sig` there.
THE ROAD THAT IS MEANT. `reader`: `reader4` (Reader4.lean); its four premises: "K13.pileMasks" is in
Q and says `pileMasksC`; `K1.indexThereB`; the second conjunct of `First.bookAt`; `place_in_book`
(Johnson/Desc/K12/Door/DoorGives.lean) from "K12.seatsCarried" and hbelow. `held`: `seed4`'s proof
(SigHeld.lean) WITHOUT ITS PREMISE ON THE BOOK's SIZE, WHICH IS NOT SPENT THERE AND WHICH
`Others4.held` DOES NOT HAND. `shown`, `noColl`, `pinIBack`: `pinsStay` (SigPins.lean), with "smp is
the same at the members at the index masks' seat" out of `SmpOld` (SmpEarlierMessages.lean): its premises: the
step's first part; `First.bookAt` and "held" are handed by the two clauses; `OlderStay`: the code
table (`plan_same_M4`), the older messages (`K1.sendAtS_kept`, `rowsB_same`), the book's older
places and trees (`atM4_seated`). `decodes`,
`pinWBack`: `decodes_M4`, `pinWBack_M4` (SigDecodes.lean).
Who spends it: `fillM4_of` (FillFromSentences.lean), for the tie at W's commitment.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.Others3AtSig
import Johnson.Desc.K13.Law.SmpEarlierMessages
import Johnson.Desc.K13.Law.MasksDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)
open VerifiableInference.Desc.K12.Door (seatsCarriedB placesBelowB)

/-- **OWED.** `Others4` at these letters and this reader. -/
def OwedOthers4 : Prop :=
  ∀ {Pp Cl Xi Cells Tok : Type} {nR : ℕ} (P : Where) (P' : K1.Par) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE) (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (Q : List Pub) (p : Option Place) (cs : Codes)
    (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (L : K12.Door.Laid), SigLetters N Mg cs G arr smp ms decT →
    pileMasksItem ∈ Q → seatsItem ∈ Q →
    (∀ x, Mg.pub pileMasksItem x = pileMasksC x.2) →
    (∀ x, Mg.pub seatsItem x = seatsCarriedB L x.2.book) →
    (∀ x, Mg.pub .indexThere x = true → K1.indexThereB x.2 = true) →
    (∀ (x : Pp × S) p, First.bookAt N p x.2 = true → seatsCarriedB L x.2.book = true →
      placesBelowB L x.2.book.place.size x.2.book.trees.size = true) →
    SmpOld N p ms smp → DecBlind decT → Others4 Cl P P' N Mg (rwBook arr mat) Q p

end VerifiableInference.Desc.K13.Law
